// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr import Lean.Meta.Tactic.Grind.Arith.Linear.Den import Lean.Meta.Tactic.Grind.Arith.Linear.Var import Lean.Meta.Tactic.Grind.Arith.Linear.StructId import Lean.Meta.Tactic.Grind.Arith.Linear.Reify import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr import Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr import Lean.Meta.Tactic.Grind.Arith.Linear.Proof import Lean.Meta.Tactic.Grind.Arith.Linear.OfNatModule
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3;
lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1;
lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0;
lean_object* lean_st_ref_take(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0;
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3;
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_mul(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0;
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3;
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0;
lean_object* l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0;
lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_coeff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__1;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0;
lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Expr_norm(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__4;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_toIntModuleExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0;
static lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__2;
lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2;
lean_object* lean_int_neg(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Grind_Linarith_instBEqPoly_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__1;
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__0;
x_18 = 0;
x_19 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__1;
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__2;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__0;
x_30 = 0;
x_31 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__1;
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__2;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__0;
x_53 = 0;
x_54 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__1;
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__2;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__0;
x_80 = 0;
x_81 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__1;
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__2;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_16, 3);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__1;
x_20 = l_Lean_Level_succ___override(x_18);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_mkConst(x_19, x_22);
x_24 = l_Lean_mkApp3(x_23, x_17, x_1, x_2);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_25, 3);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__1;
x_29 = l_Lean_Level_succ___override(x_27);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_mkConst(x_28, x_31);
x_33 = l_Lean_mkApp3(x_32, x_26, x_1, x_2);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_14, 0);
lean_inc(x_36);
lean_dec(x_14);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0;
x_15 = lean_int_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_29; uint8_t x_30; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_20 = x_18;
} else {
 lean_dec_ref(x_18);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_19, 30);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_17, 23);
lean_inc_ref(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_21, 2);
x_24 = l_Lean_mkIntLit(x_1);
x_29 = l_Lean_instInhabitedExpr;
x_30 = lean_nat_dec_lt(x_2, x_23);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec_ref(x_21);
x_31 = l_outOfBounds___redArg(x_29);
x_25 = x_31;
goto block_28;
}
else
{
lean_object* x_32; 
x_32 = l_Lean_PersistentArray_get_x21___redArg(x_29, x_21, x_2);
x_25 = x_32;
goto block_28;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_mkAppB(x_22, x_24, x_25);
if (lean_is_scalar(x_20)) {
 x_27 = lean_alloc_ctor(0, 1, 0);
} else {
 x_27 = x_20;
}
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_33; 
lean_dec(x_17);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_16, 0);
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
x_39 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_41, 30);
lean_inc_ref(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 2);
x_44 = l_Lean_instInhabitedExpr;
x_45 = lean_nat_dec_lt(x_2, x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec_ref(x_42);
x_46 = l_outOfBounds___redArg(x_44);
lean_ctor_set(x_39, 0, x_46);
return x_39;
}
else
{
lean_object* x_47; 
x_47 = l_Lean_PersistentArray_get_x21___redArg(x_44, x_42, x_2);
lean_ctor_set(x_39, 0, x_47);
return x_39;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_ctor_get(x_48, 30);
lean_inc_ref(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 2);
x_51 = l_Lean_instInhabitedExpr;
x_52 = lean_nat_dec_lt(x_2, x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_49);
x_53 = l_outOfBounds___redArg(x_51);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Lean_PersistentArray_get_x21___redArg(x_51, x_49, x_2);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_39);
if (x_57 == 0)
{
return x_39;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_39, 0);
lean_inc(x_58);
lean_dec(x_39);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_19, 22);
lean_inc_ref(x_22);
lean_dec(x_19);
x_23 = l_Lean_mkAppB(x_22, x_2, x_21);
x_1 = x_17;
x_2 = x_23;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec_ref(x_2);
return x_20;
}
}
else
{
uint8_t x_25; 
lean_dec_ref(x_2);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 17);
lean_inc_ref(x_16);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 17);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_ctor_get(x_1, 2);
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1(x_23, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__2(x_25, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_28;
}
else
{
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 18);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4(x_15, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_15);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8() {
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
lean_object* x_13; 
x_13 = l_Lean_Grind_Linarith_Poly_findVarToSubst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_40; 
lean_free_object(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_17 = x_15;
} else {
 lean_dec_ref(x_15);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_21 = x_16;
} else {
 lean_dec_ref(x_16);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_19, 0);
x_25 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_26 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_25, x_10);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = l_Lean_Grind_Linarith_Poly_coeff(x_24, x_22);
lean_inc(x_1);
x_30 = l_Lean_Grind_Linarith_Poly_mul(x_1, x_29);
x_31 = lean_int_neg(x_20);
lean_inc(x_24);
x_32 = l_Lean_Grind_Linarith_Poly_mul(x_24, x_31);
lean_dec(x_31);
x_33 = l_Lean_Grind_Linarith_Poly_combine(x_30, x_32);
x_40 = lean_unbox(x_27);
lean_dec(x_27);
if (x_40 == 0)
{
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_1);
x_34 = lean_box(0);
goto block_39;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_64; lean_object* x_65; lean_object* x_88; uint8_t x_89; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l_Lean_MessageData_ofExpr(x_42);
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_49);
lean_ctor_set(x_64, 1, x_50);
x_88 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_89 = lean_int_dec_lt(x_20, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_nat_abs(x_20);
lean_dec(x_20);
x_91 = l_Nat_reprFast(x_90);
x_65 = x_91;
goto block_87;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_nat_abs(x_20);
lean_dec(x_20);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_sub(x_92, x_93);
lean_dec(x_92);
x_95 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8;
x_96 = lean_nat_add(x_94, x_93);
lean_dec(x_94);
x_97 = l_Nat_reprFast(x_96);
x_98 = lean_string_append(x_95, x_97);
lean_dec_ref(x_97);
x_65 = x_98;
goto block_87;
}
block_63:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_MessageData_ofFormat(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
x_57 = l_Lean_MessageData_ofExpr(x_48);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_25, x_58, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_59) == 0)
{
lean_dec_ref(x_59);
x_34 = lean_box(0);
goto block_39;
}
else
{
uint8_t x_60; 
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
block_87:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = l_Lean_MessageData_ofFormat(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_50);
x_70 = l_Lean_MessageData_ofExpr(x_44);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_50);
x_73 = l_Lean_MessageData_ofExpr(x_46);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_50);
x_76 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_77 = lean_int_dec_lt(x_29, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_nat_abs(x_29);
lean_dec(x_29);
x_79 = l_Nat_reprFast(x_78);
x_51 = x_75;
x_52 = x_79;
goto block_63;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_80 = lean_nat_abs(x_29);
lean_dec(x_29);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_sub(x_80, x_81);
lean_dec(x_80);
x_83 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8;
x_84 = lean_nat_add(x_82, x_81);
lean_dec(x_82);
x_85 = l_Nat_reprFast(x_84);
x_86 = lean_string_append(x_83, x_85);
lean_dec_ref(x_85);
x_51 = x_75;
x_52 = x_86;
goto block_63;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_99 = !lean_is_exclusive(x_47);
if (x_99 == 0)
{
return x_47;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_47, 0);
lean_inc(x_100);
lean_dec(x_47);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_102 = !lean_is_exclusive(x_45);
if (x_102 == 0)
{
return x_45;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_45, 0);
lean_inc(x_103);
lean_dec(x_45);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_42);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_105 = !lean_is_exclusive(x_43);
if (x_105 == 0)
{
return x_43;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_43, 0);
lean_inc(x_106);
lean_dec(x_43);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_108 = !lean_is_exclusive(x_41);
if (x_108 == 0)
{
return x_41;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_41, 0);
lean_inc(x_109);
lean_dec(x_41);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
block_39:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
if (lean_is_scalar(x_23)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_23;
}
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_33);
if (lean_is_scalar(x_21)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_21;
}
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_35);
if (lean_is_scalar(x_17)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_17;
}
lean_ctor_set(x_37, 0, x_36);
if (lean_is_scalar(x_28)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_28;
}
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
lean_object* x_111; 
lean_dec(x_15);
lean_dec(x_1);
x_111 = lean_box(0);
lean_ctor_set(x_13, 0, x_111);
return x_13;
}
}
else
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_13, 0);
lean_inc(x_112);
lean_dec(x_13);
if (lean_obj_tag(x_112) == 1)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_137; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_118 = x_113;
} else {
 lean_dec_ref(x_113);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_115, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_120 = x_115;
} else {
 lean_dec_ref(x_115);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_116, 0);
x_122 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_123 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_122, x_10);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
x_126 = l_Lean_Grind_Linarith_Poly_coeff(x_121, x_119);
lean_inc(x_1);
x_127 = l_Lean_Grind_Linarith_Poly_mul(x_1, x_126);
x_128 = lean_int_neg(x_117);
lean_inc(x_121);
x_129 = l_Lean_Grind_Linarith_Poly_mul(x_121, x_128);
lean_dec(x_128);
x_130 = l_Lean_Grind_Linarith_Poly_combine(x_127, x_129);
x_137 = lean_unbox(x_124);
lean_dec(x_124);
if (x_137 == 0)
{
lean_dec(x_126);
lean_dec(x_117);
lean_dec(x_1);
x_131 = lean_box(0);
goto block_136;
}
else
{
lean_object* x_138; 
x_138 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec_ref(x_138);
x_140 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_119, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_116, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_130, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_161; lean_object* x_162; lean_object* x_185; uint8_t x_186; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = l_Lean_MessageData_ofExpr(x_139);
x_147 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_146);
lean_ctor_set(x_161, 1, x_147);
x_185 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_186 = lean_int_dec_lt(x_117, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_nat_abs(x_117);
lean_dec(x_117);
x_188 = l_Nat_reprFast(x_187);
x_162 = x_188;
goto block_184;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_189 = lean_nat_abs(x_117);
lean_dec(x_117);
x_190 = lean_unsigned_to_nat(1u);
x_191 = lean_nat_sub(x_189, x_190);
lean_dec(x_189);
x_192 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8;
x_193 = lean_nat_add(x_191, x_190);
lean_dec(x_191);
x_194 = l_Nat_reprFast(x_193);
x_195 = lean_string_append(x_192, x_194);
lean_dec_ref(x_194);
x_162 = x_195;
goto block_184;
}
block_160:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_150 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = l_Lean_MessageData_ofFormat(x_150);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_147);
x_154 = l_Lean_MessageData_ofExpr(x_145);
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_122, x_155, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_156) == 0)
{
lean_dec_ref(x_156);
x_131 = lean_box(0);
goto block_136;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_130);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_114);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_157);
return x_159;
}
}
block_184:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_163 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = l_Lean_MessageData_ofFormat(x_163);
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_161);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_147);
x_167 = l_Lean_MessageData_ofExpr(x_141);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_147);
x_170 = l_Lean_MessageData_ofExpr(x_143);
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_147);
x_173 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_174 = lean_int_dec_lt(x_126, x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_nat_abs(x_126);
lean_dec(x_126);
x_176 = l_Nat_reprFast(x_175);
x_148 = x_172;
x_149 = x_176;
goto block_160;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_177 = lean_nat_abs(x_126);
lean_dec(x_126);
x_178 = lean_unsigned_to_nat(1u);
x_179 = lean_nat_sub(x_177, x_178);
lean_dec(x_177);
x_180 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8;
x_181 = lean_nat_add(x_179, x_178);
lean_dec(x_179);
x_182 = l_Nat_reprFast(x_181);
x_183 = lean_string_append(x_180, x_182);
lean_dec_ref(x_182);
x_148 = x_172;
x_149 = x_183;
goto block_160;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_130);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_114);
x_196 = lean_ctor_get(x_144, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 x_197 = x_144;
} else {
 lean_dec_ref(x_144);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_130);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_114);
x_199 = lean_ctor_get(x_142, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_200 = x_142;
} else {
 lean_dec_ref(x_142);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 1, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_199);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_139);
lean_dec(x_130);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_114);
x_202 = lean_ctor_get(x_140, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_203 = x_140;
} else {
 lean_dec_ref(x_140);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_130);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_114);
x_205 = lean_ctor_get(x_138, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_206 = x_138;
} else {
 lean_dec_ref(x_138);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_205);
return x_207;
}
}
block_136:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
if (lean_is_scalar(x_120)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_120;
}
lean_ctor_set(x_132, 0, x_116);
lean_ctor_set(x_132, 1, x_130);
if (lean_is_scalar(x_118)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_118;
}
lean_ctor_set(x_133, 0, x_119);
lean_ctor_set(x_133, 1, x_132);
if (lean_is_scalar(x_114)) {
 x_134 = lean_alloc_ctor(1, 1, 0);
} else {
 x_134 = x_114;
}
lean_ctor_set(x_134, 0, x_133);
if (lean_is_scalar(x_125)) {
 x_135 = lean_alloc_ctor(0, 1, 0);
} else {
 x_135 = x_125;
}
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_112);
lean_dec(x_1);
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_209, 0, x_208);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_13);
if (x_210 == 0)
{
return x_13;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_13, 0);
lean_inc(x_211);
lean_dec(x_13);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 18);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4(x_15, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_mkNot(x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_mkNot(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
return x_19;
}
}
else
{
uint8_t x_26; 
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0() {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0;
x_70 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_69, x_14);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = x_12;
x_24 = x_13;
x_25 = x_14;
x_26 = x_15;
x_27 = lean_box(0);
goto block_68;
}
else
{
lean_object* x_73; 
x_73 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = l_Lean_MessageData_ofExpr(x_74);
x_80 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_MessageData_ofExpr(x_76);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
x_85 = l_Lean_MessageData_ofExpr(x_78);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_69, x_86, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_87) == 0)
{
lean_dec_ref(x_87);
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = x_12;
x_24 = x_13;
x_25 = x_14;
x_26 = x_15;
x_27 = lean_box(0);
goto block_68;
}
else
{
uint8_t x_88; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
return x_87;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_76);
lean_dec(x_74);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_91 = !lean_is_exclusive(x_77);
if (x_91 == 0)
{
return x_77;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_77, 0);
lean_inc(x_92);
lean_dec(x_77);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_74);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_94 = !lean_is_exclusive(x_75);
if (x_94 == 0)
{
return x_75;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_75, 0);
lean_inc(x_95);
lean_dec(x_75);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_97 = !lean_is_exclusive(x_73);
if (x_97 == 0)
{
return x_73;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_73, 0);
lean_inc(x_98);
lean_dec(x_73);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
block_68:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_int_emod(x_4, x_1);
x_31 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_32 = lean_int_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_37 = lean_box(0);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_28);
x_38 = l_Lean_Grind_Linarith_Poly_mul(x_28, x_4);
x_39 = lean_int_neg(x_1);
lean_inc(x_29);
x_40 = l_Lean_Grind_Linarith_Poly_mul(x_29, x_39);
x_41 = l_Lean_Grind_Linarith_Poly_combine(x_38, x_40);
x_42 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_4);
lean_ctor_set(x_42, 2, x_3);
lean_ctor_set(x_42, 3, x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_33, 0, x_44);
return x_33;
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
lean_dec(x_33);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_inc(x_28);
x_49 = l_Lean_Grind_Linarith_Poly_mul(x_28, x_4);
x_50 = lean_int_neg(x_1);
lean_inc(x_29);
x_51 = l_Lean_Grind_Linarith_Poly_mul(x_29, x_50);
x_52 = l_Lean_Grind_Linarith_Poly_combine(x_49, x_51);
x_53 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_4);
lean_ctor_set(x_53, 2, x_3);
lean_ctor_set(x_53, 3, x_5);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_57 = !lean_is_exclusive(x_33);
if (x_57 == 0)
{
return x_33;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_33, 0);
lean_inc(x_58);
lean_dec(x_33);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_int_neg(x_4);
lean_dec(x_4);
x_61 = lean_int_ediv(x_60, x_1);
lean_dec(x_60);
lean_inc(x_28);
x_62 = l_Lean_Grind_Linarith_Poly_mul(x_28, x_61);
lean_inc(x_29);
x_63 = l_Lean_Grind_Linarith_Poly_combine(x_62, x_29);
x_64 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_3);
lean_ctor_set(x_64, 2, x_5);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(x_1, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; lean_object* x_10; 
lean_free_object(x_6);
x_9 = lean_ctor_get(x_8, 0);
x_10 = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_nat_dec_eq(x_9, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_8);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
}
else
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec_ref(x_8);
x_16 = lean_box(0);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_nat_dec_eq(x_9, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_8);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_8);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_17);
lean_dec_ref(x_8);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
lean_dec_ref(x_8);
return x_10;
}
}
else
{
lean_object* x_25; 
lean_dec(x_8);
x_25 = lean_box(0);
lean_ctor_set(x_6, 0, x_25);
return x_6;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
lean_dec(x_6);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
x_28 = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(x_2, x_3, x_4);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_nat_dec_eq(x_27, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_26);
x_33 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; 
if (lean_is_scalar(x_30)) {
 x_35 = lean_alloc_ctor(0, 1, 0);
} else {
 x_35 = x_30;
}
lean_ctor_set(x_35, 0, x_26);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_29);
lean_dec_ref(x_26);
x_36 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_37 = lean_alloc_ctor(0, 1, 0);
} else {
 x_37 = x_30;
}
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
else
{
lean_dec_ref(x_26);
return x_28;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_26);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(x_1, x_2, x_3, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = 0;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_box(x_14);
lean_inc_ref(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_box(x_14);
lean_inc_ref(x_2);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 3);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_151; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_151 = lean_nat_dec_le(x_29, x_31);
if (x_151 == 0)
{
lean_dec(x_31);
x_32 = x_29;
goto block_150;
}
else
{
lean_dec(x_29);
x_32 = x_31;
goto block_150;
}
block_150:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_27);
lean_inc(x_21);
x_33 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_27);
x_34 = l_Lean_Grind_CommRing_Expr_toPoly(x_33);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_2);
lean_ctor_set(x_35, 2, x_21);
lean_ctor_set(x_35, 3, x_27);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_37 = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_32);
lean_inc_ref(x_39);
x_40 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_39, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_42 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_41, x_14, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
lean_inc(x_45);
x_46 = l_Lean_Grind_Linarith_Expr_norm(x_45);
x_47 = lean_box(0);
x_48 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_42);
lean_inc(x_38);
x_49 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_45);
lean_inc(x_46);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_14);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
lean_inc_ref(x_39);
x_55 = l_Lean_Grind_CommRing_Poly_mulConst(x_54, x_39);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_38);
lean_inc_ref(x_55);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_32);
x_57 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_55, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_59 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_58, x_14, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
if (lean_obj_tag(x_61) == 1)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_59);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l_Lean_Grind_Linarith_Poly_mul(x_46, x_54);
x_64 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_14);
x_66 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_66;
}
else
{
lean_object* x_67; 
lean_dec(x_61);
lean_dec_ref(x_56);
lean_dec(x_46);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_67 = lean_box(0);
lean_ctor_set(x_59, 0, x_67);
return x_59;
}
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
lean_dec(x_59);
if (lean_obj_tag(x_68) == 1)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = l_Lean_Grind_Linarith_Poly_mul(x_46, x_54);
x_71 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_71, 0, x_56);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_14);
x_73 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_68);
lean_dec_ref(x_56);
lean_dec(x_46);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec_ref(x_56);
lean_dec(x_46);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_76 = !lean_is_exclusive(x_59);
if (x_76 == 0)
{
return x_59;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_59, 0);
lean_inc(x_77);
lean_dec(x_59);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec_ref(x_56);
lean_dec(x_46);
lean_dec(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_57);
if (x_79 == 0)
{
return x_57;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_57, 0);
lean_inc(x_80);
lean_dec(x_57);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_51);
x_82 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
lean_inc_ref(x_39);
x_83 = l_Lean_Grind_CommRing_Poly_mulConst(x_82, x_39);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_38);
lean_inc_ref(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_32);
x_86 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_83, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_88 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_87, x_14, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_obj_tag(x_89) == 1)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_90);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec_ref(x_89);
x_92 = l_Lean_Grind_Linarith_Poly_mul(x_46, x_82);
x_93 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_14);
x_95 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_89);
lean_dec_ref(x_85);
lean_dec(x_46);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_96 = lean_box(0);
if (lean_is_scalar(x_90)) {
 x_97 = lean_alloc_ctor(0, 1, 0);
} else {
 x_97 = x_90;
}
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec_ref(x_85);
lean_dec(x_46);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = lean_ctor_get(x_88, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_99 = x_88;
} else {
 lean_dec_ref(x_88);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec_ref(x_85);
lean_dec(x_46);
lean_dec(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_101 = lean_ctor_get(x_86, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_102 = x_86;
} else {
 lean_dec_ref(x_86);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 1, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_101);
return x_103;
}
}
}
else
{
lean_dec(x_46);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_51;
}
}
else
{
lean_object* x_104; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = lean_box(0);
lean_ctor_set(x_42, 0, x_104);
return x_42;
}
}
else
{
lean_object* x_105; 
lean_dec(x_44);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = lean_box(0);
lean_ctor_set(x_42, 0, x_105);
return x_42;
}
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_42, 0);
lean_inc(x_106);
lean_dec(x_42);
if (lean_obj_tag(x_106) == 1)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
lean_inc(x_107);
x_108 = l_Lean_Grind_Linarith_Expr_norm(x_107);
x_109 = lean_box(0);
x_110 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_108, x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_inc(x_38);
x_111 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_111, 0, x_38);
lean_ctor_set(x_111, 1, x_107);
lean_inc(x_108);
x_112 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set_uint8(x_112, sizeof(void*)*2, x_14);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_113 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_112, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_114 = x_113;
} else {
 lean_dec_ref(x_113);
 x_114 = lean_box(0);
}
x_115 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
lean_inc_ref(x_39);
x_116 = l_Lean_Grind_CommRing_Poly_mulConst(x_115, x_39);
if (lean_is_scalar(x_114)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_114;
 lean_ctor_set_tag(x_117, 1);
}
lean_ctor_set(x_117, 0, x_38);
lean_inc_ref(x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_32);
x_119 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_116, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_121 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_120, x_14, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
if (lean_obj_tag(x_122) == 1)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_123);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec_ref(x_122);
x_125 = l_Lean_Grind_Linarith_Poly_mul(x_108, x_115);
x_126 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_126, 0, x_118);
lean_ctor_set(x_126, 1, x_124);
x_127 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set_uint8(x_127, sizeof(void*)*2, x_14);
x_128 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_127, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_122);
lean_dec_ref(x_118);
lean_dec(x_108);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_129 = lean_box(0);
if (lean_is_scalar(x_123)) {
 x_130 = lean_alloc_ctor(0, 1, 0);
} else {
 x_130 = x_123;
}
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec_ref(x_118);
lean_dec(x_108);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_131 = lean_ctor_get(x_121, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_132 = x_121;
} else {
 lean_dec_ref(x_121);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_131);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec_ref(x_118);
lean_dec(x_108);
lean_dec(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_134 = lean_ctor_get(x_119, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_135 = x_119;
} else {
 lean_dec_ref(x_119);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_134);
return x_136;
}
}
else
{
lean_dec(x_108);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_113;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_106);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_141 = !lean_is_exclusive(x_42);
if (x_141 == 0)
{
return x_42;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_42, 0);
lean_inc(x_142);
lean_dec(x_42);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_144 = !lean_is_exclusive(x_40);
if (x_144 == 0)
{
return x_40;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_40, 0);
lean_inc(x_145);
lean_dec(x_40);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_147 = !lean_is_exclusive(x_37);
if (x_147 == 0)
{
return x_37;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_37, 0);
lean_inc(x_148);
lean_dec(x_37);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
return x_149;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_152 = !lean_is_exclusive(x_30);
if (x_152 == 0)
{
return x_30;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_30, 0);
lean_inc(x_153);
lean_dec(x_30);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_155 = !lean_is_exclusive(x_28);
if (x_155 == 0)
{
return x_28;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_28, 0);
lean_inc(x_156);
lean_dec(x_28);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
}
}
else
{
lean_object* x_158; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_158 = lean_box(0);
lean_ctor_set(x_24, 0, x_158);
return x_24;
}
}
else
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_24, 0);
lean_inc(x_159);
lean_dec(x_24);
if (lean_obj_tag(x_159) == 1)
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec_ref(x_159);
x_161 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec_ref(x_161);
x_163 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_222; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_222 = lean_nat_dec_le(x_162, x_164);
if (x_222 == 0)
{
lean_dec(x_164);
x_165 = x_162;
goto block_221;
}
else
{
lean_dec(x_162);
x_165 = x_164;
goto block_221;
}
block_221:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_inc(x_160);
lean_inc(x_21);
x_166 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_166, 0, x_21);
lean_ctor_set(x_166, 1, x_160);
x_167 = l_Lean_Grind_CommRing_Expr_toPoly(x_166);
x_168 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_168, 0, x_1);
lean_ctor_set(x_168, 1, x_2);
lean_ctor_set(x_168, 2, x_21);
lean_ctor_set(x_168, 3, x_160);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_170 = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(x_169, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec_ref(x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_165);
lean_inc_ref(x_172);
x_173 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_172, x_165, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_165);
x_175 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_174, x_14, x_165, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_177 = x_175;
} else {
 lean_dec_ref(x_175);
 x_177 = lean_box(0);
}
if (lean_obj_tag(x_176) == 1)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
lean_dec_ref(x_176);
lean_inc(x_178);
x_179 = l_Lean_Grind_Linarith_Expr_norm(x_178);
x_180 = lean_box(0);
x_181 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_179, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_177);
lean_inc(x_171);
x_182 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_182, 0, x_171);
lean_ctor_set(x_182, 1, x_178);
lean_inc(x_179);
x_183 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_183, 0, x_179);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set_uint8(x_183, sizeof(void*)*2, x_14);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_184 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_183, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 x_185 = x_184;
} else {
 lean_dec_ref(x_184);
 x_185 = lean_box(0);
}
x_186 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
lean_inc_ref(x_172);
x_187 = l_Lean_Grind_CommRing_Poly_mulConst(x_186, x_172);
if (lean_is_scalar(x_185)) {
 x_188 = lean_alloc_ctor(1, 1, 0);
} else {
 x_188 = x_185;
 lean_ctor_set_tag(x_188, 1);
}
lean_ctor_set(x_188, 0, x_171);
lean_inc_ref(x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_165);
x_190 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_187, x_165, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec_ref(x_190);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_192 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_191, x_14, x_165, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
if (lean_obj_tag(x_193) == 1)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_194);
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
lean_dec_ref(x_193);
x_196 = l_Lean_Grind_Linarith_Poly_mul(x_179, x_186);
x_197 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_197, 0, x_189);
lean_ctor_set(x_197, 1, x_195);
x_198 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
lean_ctor_set_uint8(x_198, sizeof(void*)*2, x_14);
x_199 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_198, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_193);
lean_dec_ref(x_189);
lean_dec(x_179);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_200 = lean_box(0);
if (lean_is_scalar(x_194)) {
 x_201 = lean_alloc_ctor(0, 1, 0);
} else {
 x_201 = x_194;
}
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec_ref(x_189);
lean_dec(x_179);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_202 = lean_ctor_get(x_192, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_203 = x_192;
} else {
 lean_dec_ref(x_192);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec_ref(x_189);
lean_dec(x_179);
lean_dec(x_165);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_205 = lean_ctor_get(x_190, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_206 = x_190;
} else {
 lean_dec_ref(x_190);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_205);
return x_207;
}
}
else
{
lean_dec(x_179);
lean_dec(x_171);
lean_dec(x_165);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_184;
}
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_171);
lean_dec(x_165);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_208 = lean_box(0);
if (lean_is_scalar(x_177)) {
 x_209 = lean_alloc_ctor(0, 1, 0);
} else {
 x_209 = x_177;
}
lean_ctor_set(x_209, 0, x_208);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_176);
lean_dec(x_171);
lean_dec(x_165);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_210 = lean_box(0);
if (lean_is_scalar(x_177)) {
 x_211 = lean_alloc_ctor(0, 1, 0);
} else {
 x_211 = x_177;
}
lean_ctor_set(x_211, 0, x_210);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_171);
lean_dec(x_165);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_212 = lean_ctor_get(x_175, 0);
lean_inc(x_212);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_213 = x_175;
} else {
 lean_dec_ref(x_175);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 1, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_212);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_171);
lean_dec(x_165);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_215 = lean_ctor_get(x_173, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_216 = x_173;
} else {
 lean_dec_ref(x_173);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_215);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_165);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_218 = lean_ctor_get(x_170, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_219 = x_170;
} else {
 lean_dec_ref(x_170);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 1, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_218);
return x_220;
}
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_223 = lean_ctor_get(x_163, 0);
lean_inc(x_223);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_224 = x_163;
} else {
 lean_dec_ref(x_163);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 1, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_223);
return x_225;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_160);
lean_dec(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_226 = lean_ctor_get(x_161, 0);
lean_inc(x_226);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_227 = x_161;
} else {
 lean_dec_ref(x_161);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 1, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_226);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_159);
lean_dec(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_229 = lean_box(0);
x_230 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_230, 0, x_229);
return x_230;
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_231 = !lean_is_exclusive(x_24);
if (x_231 == 0)
{
return x_24;
}
else
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_24, 0);
lean_inc(x_232);
lean_dec(x_24);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_232);
return x_233;
}
}
}
else
{
lean_object* x_234; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_234 = lean_box(0);
lean_ctor_set(x_18, 0, x_234);
return x_18;
}
}
else
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_18, 0);
lean_inc(x_235);
lean_dec(x_18);
if (lean_obj_tag(x_235) == 1)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
lean_dec_ref(x_235);
x_237 = lean_box(x_14);
lean_inc_ref(x_2);
x_238 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 3);
lean_closure_set(x_238, 0, x_2);
lean_closure_set(x_238, 1, x_237);
lean_closure_set(x_238, 2, x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_239 = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(x_238, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_241 = x_239;
} else {
 lean_dec_ref(x_239);
 x_241 = lean_box(0);
}
if (lean_obj_tag(x_240) == 1)
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_241);
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
lean_dec_ref(x_240);
x_243 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec_ref(x_243);
x_245 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; uint8_t x_304; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
x_304 = lean_nat_dec_le(x_244, x_246);
if (x_304 == 0)
{
lean_dec(x_246);
x_247 = x_244;
goto block_303;
}
else
{
lean_dec(x_244);
x_247 = x_246;
goto block_303;
}
block_303:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_inc(x_242);
lean_inc(x_236);
x_248 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_248, 0, x_236);
lean_ctor_set(x_248, 1, x_242);
x_249 = l_Lean_Grind_CommRing_Expr_toPoly(x_248);
x_250 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_250, 0, x_1);
lean_ctor_set(x_250, 1, x_2);
lean_ctor_set(x_250, 2, x_236);
lean_ctor_set(x_250, 3, x_242);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_252 = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(x_251, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_247);
lean_inc_ref(x_254);
x_255 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_254, x_247, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec_ref(x_255);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_247);
x_257 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_256, x_14, x_247, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_259 = x_257;
} else {
 lean_dec_ref(x_257);
 x_259 = lean_box(0);
}
if (lean_obj_tag(x_258) == 1)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
lean_dec_ref(x_258);
lean_inc(x_260);
x_261 = l_Lean_Grind_Linarith_Expr_norm(x_260);
x_262 = lean_box(0);
x_263 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_261, x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_259);
lean_inc(x_253);
x_264 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_264, 0, x_253);
lean_ctor_set(x_264, 1, x_260);
lean_inc(x_261);
x_265 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_265, 0, x_261);
lean_ctor_set(x_265, 1, x_264);
lean_ctor_set_uint8(x_265, sizeof(void*)*2, x_14);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_266 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_265, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 x_267 = x_266;
} else {
 lean_dec_ref(x_266);
 x_267 = lean_box(0);
}
x_268 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
lean_inc_ref(x_254);
x_269 = l_Lean_Grind_CommRing_Poly_mulConst(x_268, x_254);
if (lean_is_scalar(x_267)) {
 x_270 = lean_alloc_ctor(1, 1, 0);
} else {
 x_270 = x_267;
 lean_ctor_set_tag(x_270, 1);
}
lean_ctor_set(x_270, 0, x_253);
lean_inc_ref(x_269);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_247);
x_272 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_269, x_247, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
lean_dec_ref(x_272);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_274 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_273, x_14, x_247, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
if (lean_obj_tag(x_275) == 1)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_276);
x_277 = lean_ctor_get(x_275, 0);
lean_inc(x_277);
lean_dec_ref(x_275);
x_278 = l_Lean_Grind_Linarith_Poly_mul(x_261, x_268);
x_279 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_279, 0, x_271);
lean_ctor_set(x_279, 1, x_277);
x_280 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set_uint8(x_280, sizeof(void*)*2, x_14);
x_281 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_280, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; 
lean_dec(x_275);
lean_dec_ref(x_271);
lean_dec(x_261);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_282 = lean_box(0);
if (lean_is_scalar(x_276)) {
 x_283 = lean_alloc_ctor(0, 1, 0);
} else {
 x_283 = x_276;
}
lean_ctor_set(x_283, 0, x_282);
return x_283;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec_ref(x_271);
lean_dec(x_261);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_284 = lean_ctor_get(x_274, 0);
lean_inc(x_284);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 x_285 = x_274;
} else {
 lean_dec_ref(x_274);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 1, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_284);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec_ref(x_271);
lean_dec(x_261);
lean_dec(x_247);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_287 = lean_ctor_get(x_272, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 x_288 = x_272;
} else {
 lean_dec_ref(x_272);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 1, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_287);
return x_289;
}
}
else
{
lean_dec(x_261);
lean_dec(x_253);
lean_dec(x_247);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_266;
}
}
else
{
lean_object* x_290; lean_object* x_291; 
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_253);
lean_dec(x_247);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_290 = lean_box(0);
if (lean_is_scalar(x_259)) {
 x_291 = lean_alloc_ctor(0, 1, 0);
} else {
 x_291 = x_259;
}
lean_ctor_set(x_291, 0, x_290);
return x_291;
}
}
else
{
lean_object* x_292; lean_object* x_293; 
lean_dec(x_258);
lean_dec(x_253);
lean_dec(x_247);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_292 = lean_box(0);
if (lean_is_scalar(x_259)) {
 x_293 = lean_alloc_ctor(0, 1, 0);
} else {
 x_293 = x_259;
}
lean_ctor_set(x_293, 0, x_292);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_253);
lean_dec(x_247);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_294 = lean_ctor_get(x_257, 0);
lean_inc(x_294);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_295 = x_257;
} else {
 lean_dec_ref(x_257);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 1, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_294);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_253);
lean_dec(x_247);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_297 = lean_ctor_get(x_255, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 x_298 = x_255;
} else {
 lean_dec_ref(x_255);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 1, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_297);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_247);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_300 = lean_ctor_get(x_252, 0);
lean_inc(x_300);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 x_301 = x_252;
} else {
 lean_dec_ref(x_252);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 1, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_300);
return x_302;
}
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_244);
lean_dec(x_242);
lean_dec(x_236);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_305 = lean_ctor_get(x_245, 0);
lean_inc(x_305);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 x_306 = x_245;
} else {
 lean_dec_ref(x_245);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 1, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_305);
return x_307;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_242);
lean_dec(x_236);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_308 = lean_ctor_get(x_243, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_309 = x_243;
} else {
 lean_dec_ref(x_243);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 1, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_308);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; 
lean_dec(x_240);
lean_dec(x_236);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_311 = lean_box(0);
if (lean_is_scalar(x_241)) {
 x_312 = lean_alloc_ctor(0, 1, 0);
} else {
 x_312 = x_241;
}
lean_ctor_set(x_312, 0, x_311);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_236);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_313 = lean_ctor_get(x_239, 0);
lean_inc(x_313);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_314 = x_239;
} else {
 lean_dec_ref(x_239);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 1, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_313);
return x_315;
}
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_235);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_316 = lean_box(0);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_316);
return x_317;
}
}
}
else
{
uint8_t x_318; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_318 = !lean_is_exclusive(x_18);
if (x_318 == 0)
{
return x_18;
}
else
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_18, 0);
lean_inc(x_319);
lean_dec(x_18);
x_320 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_320, 0, x_319);
return x_320;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_1, x_16, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_23 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_2, x_16, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc(x_26);
lean_inc(x_20);
x_27 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Grind_Linarith_Expr_norm(x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_23);
lean_inc(x_26);
lean_inc(x_20);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_31 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_31, 2, x_20);
lean_ctor_set(x_31, 3, x_26);
lean_inc(x_28);
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_16);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_33 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_33);
x_34 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_35 = l_Lean_Grind_Linarith_Poly_mul(x_28, x_34);
x_36 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_1);
lean_ctor_set(x_36, 2, x_26);
lean_ctor_set(x_36, 3, x_20);
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_16);
x_38 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_38;
}
else
{
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_33;
}
}
else
{
lean_object* x_39; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_39 = lean_box(0);
lean_ctor_set(x_23, 0, x_39);
return x_23;
}
}
else
{
lean_object* x_40; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_40 = lean_box(0);
lean_ctor_set(x_23, 0, x_40);
return x_23;
}
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
lean_dec(x_23);
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
lean_inc(x_42);
lean_inc(x_20);
x_43 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_43, 0, x_20);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Grind_Linarith_Expr_norm(x_43);
x_45 = lean_box(0);
x_46 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_inc(x_42);
lean_inc(x_20);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_47 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_2);
lean_ctor_set(x_47, 2, x_20);
lean_ctor_set(x_47, 3, x_42);
lean_inc(x_44);
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_16);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_49 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_49);
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_51 = l_Lean_Grind_Linarith_Poly_mul(x_44, x_50);
x_52 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_1);
lean_ctor_set(x_52, 2, x_42);
lean_ctor_set(x_52, 3, x_20);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_16);
x_54 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_54;
}
else
{
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_49;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_41);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_23);
if (x_59 == 0)
{
return x_23;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_23, 0);
lean_inc(x_60);
lean_dec(x_23);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_62 = !lean_is_exclusive(x_21);
if (x_62 == 0)
{
return x_21;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_21, 0);
lean_inc(x_63);
lean_dec(x_21);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = lean_box(0);
lean_ctor_set(x_17, 0, x_65);
return x_17;
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_17, 0);
lean_inc(x_66);
lean_dec(x_17);
if (lean_obj_tag(x_66) == 1)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_70 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_2, x_16, x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec_ref(x_71);
lean_inc(x_73);
lean_inc(x_67);
x_74 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Grind_Linarith_Expr_norm(x_74);
x_76 = lean_box(0);
x_77 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_72);
lean_inc(x_73);
lean_inc(x_67);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_78 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_2);
lean_ctor_set(x_78, 2, x_67);
lean_ctor_set(x_78, 3, x_73);
lean_inc(x_75);
x_79 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_16);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_80 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec_ref(x_80);
x_81 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_82 = l_Lean_Grind_Linarith_Poly_mul(x_75, x_81);
x_83 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_83, 0, x_2);
lean_ctor_set(x_83, 1, x_1);
lean_ctor_set(x_83, 2, x_73);
lean_ctor_set(x_83, 3, x_67);
x_84 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_16);
x_85 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_85;
}
else
{
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_67);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_80;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_67);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_86 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_87 = lean_alloc_ctor(0, 1, 0);
} else {
 x_87 = x_72;
}
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_71);
lean_dec(x_67);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_88 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_89 = lean_alloc_ctor(0, 1, 0);
} else {
 x_89 = x_72;
}
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_67);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_90 = lean_ctor_get(x_70, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_91 = x_70;
} else {
 lean_dec_ref(x_70);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_67);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_93 = lean_ctor_get(x_68, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_94 = x_68;
} else {
 lean_dec_ref(x_68);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_66);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_98 = !lean_is_exclusive(x_17);
if (x_98 == 0)
{
return x_17;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_17, 0);
lean_inc(x_99);
lean_dec(x_17);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_101 = !lean_is_exclusive(x_14);
if (x_101 == 0)
{
return x_14;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_14, 0);
lean_inc(x_102);
lean_dec(x_14);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0;
x_14 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = lean_panic_fn(x_14, x_1);
x_16 = lean_apply_11(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_16;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq", 47, 47);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq.0.Lean.Meta.Grind.Arith.Linear.EqCnstr.norm", 100, 100);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2;
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_unsigned_to_nat(92u);
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1;
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; 
x_22 = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_66; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_66 = lean_unbox(x_23);
lean_dec(x_23);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_1, 0);
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
x_35 = x_11;
goto block_65;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_1, 0);
x_69 = l_Lean_Grind_Linarith_Poly_gcdCoeffs(x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_dec_eq(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_inc(x_69);
x_72 = lean_nat_to_int(x_69);
lean_inc(x_68);
x_73 = l_Lean_Grind_Linarith_Poly_div(x_68, x_72);
lean_dec(x_72);
x_74 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_1);
lean_inc(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_24 = x_75;
x_25 = x_73;
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
x_35 = x_11;
goto block_65;
}
else
{
lean_dec(x_69);
lean_inc(x_68);
x_24 = x_1;
x_25 = x_68;
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
x_35 = x_11;
goto block_65;
}
}
block_65:
{
lean_object* x_36; 
lean_inc(x_25);
x_36 = l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(x_25);
if (lean_obj_tag(x_36) == 1)
{
uint8_t x_37; 
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_43 = lean_int_dec_lt(x_40, x_42);
if (x_43 == 0)
{
lean_free_object(x_38);
lean_free_object(x_36);
lean_dec(x_25);
x_13 = x_40;
x_14 = x_41;
x_15 = x_24;
x_16 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_45 = l_Lean_Grind_Linarith_Poly_mul(x_25, x_44);
lean_ctor_set_tag(x_36, 3);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 0, x_45);
x_13 = x_40;
x_14 = x_41;
x_15 = x_38;
x_16 = lean_box(0);
goto block_21;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_49 = lean_int_dec_lt(x_46, x_48);
if (x_49 == 0)
{
lean_free_object(x_36);
lean_dec(x_25);
x_13 = x_46;
x_14 = x_47;
x_15 = x_24;
x_16 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_51 = l_Lean_Grind_Linarith_Poly_mul(x_25, x_50);
lean_ctor_set_tag(x_36, 3);
lean_ctor_set(x_36, 0, x_24);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_36);
x_13 = x_46;
x_14 = x_47;
x_15 = x_52;
x_16 = lean_box(0);
goto block_21;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_36, 0);
lean_inc(x_53);
lean_dec(x_36);
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
x_57 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_58 = lean_int_dec_lt(x_54, x_57);
if (x_58 == 0)
{
lean_dec(x_56);
lean_dec(x_25);
x_13 = x_54;
x_14 = x_55;
x_15 = x_24;
x_16 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_60 = l_Lean_Grind_Linarith_Poly_mul(x_25, x_59);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_24);
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_56;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_13 = x_54;
x_14 = x_55;
x_15 = x_62;
x_16 = lean_box(0);
goto block_21;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_36);
lean_dec(x_25);
lean_dec_ref(x_24);
x_63 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3;
x_64 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(x_63, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35);
return x_64;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_76 = !lean_is_exclusive(x_22);
if (x_76 == 0)
{
return x_22;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_22, 0);
lean_inc(x_77);
lean_dec(x_22);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
block_21:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_nat_abs(x_13);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4;
x_2 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 2);
x_17 = lean_ctor_get(x_10, 3);
x_18 = lean_ctor_get(x_10, 4);
x_19 = lean_ctor_get(x_10, 5);
x_20 = lean_ctor_get(x_10, 6);
x_21 = lean_ctor_get(x_10, 7);
x_22 = lean_ctor_get(x_10, 8);
x_23 = lean_ctor_get(x_10, 9);
x_24 = lean_ctor_get(x_10, 10);
x_25 = lean_ctor_get(x_10, 11);
x_26 = lean_ctor_get(x_10, 12);
x_27 = lean_ctor_get(x_10, 13);
x_28 = lean_nat_dec_eq(x_17, x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_17, x_30);
lean_dec(x_17);
lean_ctor_set(x_10, 3, x_31);
lean_inc(x_29);
x_32 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; uint8_t x_36; 
lean_free_object(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_57; lean_object* x_58; 
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_41 = x_37;
} else {
 lean_dec_ref(x_37);
 x_41 = lean_box(0);
}
x_57 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_58 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_57, x_10);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_free_object(x_35);
x_42 = x_2;
x_43 = x_3;
x_44 = x_4;
x_45 = x_5;
x_46 = x_6;
x_47 = x_7;
x_48 = x_8;
x_49 = x_9;
x_50 = x_10;
x_51 = x_11;
x_52 = lean_box(0);
goto block_56;
}
else
{
lean_object* x_61; 
x_61 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = l_Lean_MessageData_ofExpr(x_62);
x_68 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
lean_ctor_set_tag(x_35, 7);
lean_ctor_set(x_35, 1, x_68);
lean_ctor_set(x_35, 0, x_67);
x_69 = l_Lean_MessageData_ofExpr(x_64);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_35);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
x_72 = l_Lean_MessageData_ofExpr(x_66);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_57, x_73, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_74) == 0)
{
lean_dec_ref(x_74);
x_42 = x_2;
x_43 = x_3;
x_44 = x_4;
x_45 = x_5;
x_46 = x_6;
x_47 = x_7;
x_48 = x_8;
x_49 = x_9;
x_50 = x_10;
x_51 = x_11;
x_52 = lean_box(0);
goto block_56;
}
else
{
uint8_t x_75; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
return x_74;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_35);
lean_dec(x_38);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_78 = !lean_is_exclusive(x_65);
if (x_78 == 0)
{
return x_65;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_65, 0);
lean_inc(x_79);
lean_dec(x_65);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_62);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_35);
lean_dec(x_38);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_81 = !lean_is_exclusive(x_63);
if (x_81 == 0)
{
return x_63;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_63, 0);
lean_inc(x_82);
lean_dec(x_63);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_35);
lean_dec(x_38);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_84 = !lean_is_exclusive(x_61);
if (x_84 == 0)
{
return x_61;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_61, 0);
lean_inc(x_85);
lean_dec(x_61);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_35);
lean_dec(x_38);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_87 = !lean_is_exclusive(x_58);
if (x_87 == 0)
{
return x_58;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_58, 0);
lean_inc(x_88);
lean_dec(x_58);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
block_56:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_53, 1, x_39);
lean_ctor_set(x_53, 2, x_1);
if (lean_is_scalar(x_41)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_41;
}
lean_ctor_set(x_54, 0, x_40);
lean_ctor_set(x_54, 1, x_53);
x_1 = x_54;
x_2 = x_42;
x_3 = x_43;
x_4 = x_44;
x_5 = x_45;
x_6 = x_46;
x_7 = x_47;
x_8 = x_48;
x_9 = x_49;
x_10 = x_50;
x_11 = x_51;
goto _start;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_110; lean_object* x_111; 
x_90 = lean_ctor_get(x_35, 1);
x_91 = lean_ctor_get(x_35, 0);
lean_inc(x_90);
lean_inc(x_91);
lean_dec(x_35);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_94 = x_90;
} else {
 lean_dec_ref(x_90);
 x_94 = lean_box(0);
}
x_110 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_111 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_110, x_10);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = lean_unbox(x_112);
lean_dec(x_112);
if (x_113 == 0)
{
x_95 = x_2;
x_96 = x_3;
x_97 = x_4;
x_98 = x_5;
x_99 = x_6;
x_100 = x_7;
x_101 = x_8;
x_102 = x_9;
x_103 = x_10;
x_104 = x_11;
x_105 = lean_box(0);
goto block_109;
}
else
{
lean_object* x_114; 
x_114 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_118 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_92, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_120 = l_Lean_MessageData_ofExpr(x_115);
x_121 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_MessageData_ofExpr(x_117);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_121);
x_126 = l_Lean_MessageData_ofExpr(x_119);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_110, x_127, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_128) == 0)
{
lean_dec_ref(x_128);
x_95 = x_2;
x_96 = x_3;
x_97 = x_4;
x_98 = x_5;
x_99 = x_6;
x_100 = x_7;
x_101 = x_8;
x_102 = x_9;
x_103 = x_10;
x_104 = x_11;
x_105 = lean_box(0);
goto block_109;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 1, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_129);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_132 = lean_ctor_get(x_118, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_133 = x_118;
} else {
 lean_dec_ref(x_118);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 1, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_115);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_135 = lean_ctor_get(x_116, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_136 = x_116;
} else {
 lean_dec_ref(x_116);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 1, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_138 = lean_ctor_get(x_114, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_139 = x_114;
} else {
 lean_dec_ref(x_114);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 1, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_138);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_141 = lean_ctor_get(x_111, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_142 = x_111;
} else {
 lean_dec_ref(x_111);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 1, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_141);
return x_143;
}
block_109:
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_106, 0, x_91);
lean_ctor_set(x_106, 1, x_92);
lean_ctor_set(x_106, 2, x_1);
if (lean_is_scalar(x_94)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_94;
}
lean_ctor_set(x_107, 0, x_93);
lean_ctor_set(x_107, 1, x_106);
x_1 = x_107;
x_2 = x_95;
x_3 = x_96;
x_4 = x_97;
x_5 = x_98;
x_6 = x_99;
x_7 = x_100;
x_8 = x_101;
x_9 = x_102;
x_10 = x_103;
x_11 = x_104;
goto _start;
}
}
}
else
{
lean_dec(x_34);
lean_dec_ref(x_10);
lean_ctor_set(x_32, 0, x_1);
return x_32;
}
}
else
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_32, 0);
lean_inc(x_144);
lean_dec(x_32);
if (lean_obj_tag(x_144) == 1)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_167; lean_object* x_168; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_146, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_146, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_151 = x_146;
} else {
 lean_dec_ref(x_146);
 x_151 = lean_box(0);
}
x_167 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_168 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_167, x_10);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec_ref(x_168);
x_170 = lean_unbox(x_169);
lean_dec(x_169);
if (x_170 == 0)
{
lean_dec(x_148);
x_152 = x_2;
x_153 = x_3;
x_154 = x_4;
x_155 = x_5;
x_156 = x_6;
x_157 = x_7;
x_158 = x_8;
x_159 = x_9;
x_160 = x_10;
x_161 = x_11;
x_162 = lean_box(0);
goto block_166;
}
else
{
lean_object* x_171; 
x_171 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_147, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec_ref(x_171);
x_173 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
x_175 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_149, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = l_Lean_MessageData_ofExpr(x_172);
x_178 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
if (lean_is_scalar(x_148)) {
 x_179 = lean_alloc_ctor(7, 2, 0);
} else {
 x_179 = x_148;
 lean_ctor_set_tag(x_179, 7);
}
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = l_Lean_MessageData_ofExpr(x_174);
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_178);
x_183 = l_Lean_MessageData_ofExpr(x_176);
x_184 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_185 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_167, x_184, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_185) == 0)
{
lean_dec_ref(x_185);
x_152 = x_2;
x_153 = x_3;
x_154 = x_4;
x_155 = x_5;
x_156 = x_6;
x_157 = x_7;
x_158 = x_8;
x_159 = x_9;
x_160 = x_10;
x_161 = x_11;
x_162 = lean_box(0);
goto block_166;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_187 = x_185;
} else {
 lean_dec_ref(x_185);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 1, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_174);
lean_dec(x_172);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_189 = lean_ctor_get(x_175, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_190 = x_175;
} else {
 lean_dec_ref(x_175);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 1, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_189);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_172);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_192 = lean_ctor_get(x_173, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_193 = x_173;
} else {
 lean_dec_ref(x_173);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_195 = lean_ctor_get(x_171, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_196 = x_171;
} else {
 lean_dec_ref(x_171);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 1, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_195);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_198 = lean_ctor_get(x_168, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_199 = x_168;
} else {
 lean_dec_ref(x_168);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_198);
return x_200;
}
block_166:
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_163, 0, x_147);
lean_ctor_set(x_163, 1, x_149);
lean_ctor_set(x_163, 2, x_1);
if (lean_is_scalar(x_151)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_151;
}
lean_ctor_set(x_164, 0, x_150);
lean_ctor_set(x_164, 1, x_163);
x_1 = x_164;
x_2 = x_152;
x_3 = x_153;
x_4 = x_154;
x_5 = x_155;
x_6 = x_156;
x_7 = x_157;
x_8 = x_158;
x_9 = x_159;
x_10 = x_160;
x_11 = x_161;
goto _start;
}
}
else
{
lean_object* x_201; 
lean_dec(x_144);
lean_dec_ref(x_10);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_1);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_202 = !lean_is_exclusive(x_32);
if (x_202 == 0)
{
return x_32;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_32, 0);
lean_inc(x_203);
lean_dec(x_32);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
return x_204;
}
}
}
else
{
lean_object* x_205; 
lean_free_object(x_10);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_1);
x_205 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_19);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; uint8_t x_222; 
x_206 = lean_ctor_get(x_10, 0);
x_207 = lean_ctor_get(x_10, 1);
x_208 = lean_ctor_get(x_10, 2);
x_209 = lean_ctor_get(x_10, 3);
x_210 = lean_ctor_get(x_10, 4);
x_211 = lean_ctor_get(x_10, 5);
x_212 = lean_ctor_get(x_10, 6);
x_213 = lean_ctor_get(x_10, 7);
x_214 = lean_ctor_get(x_10, 8);
x_215 = lean_ctor_get(x_10, 9);
x_216 = lean_ctor_get(x_10, 10);
x_217 = lean_ctor_get(x_10, 11);
x_218 = lean_ctor_get_uint8(x_10, sizeof(void*)*14);
x_219 = lean_ctor_get(x_10, 12);
x_220 = lean_ctor_get_uint8(x_10, sizeof(void*)*14 + 1);
x_221 = lean_ctor_get(x_10, 13);
lean_inc(x_221);
lean_inc(x_219);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_10);
x_222 = lean_nat_dec_eq(x_209, x_210);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_1, 0);
x_224 = lean_unsigned_to_nat(1u);
x_225 = lean_nat_add(x_209, x_224);
lean_dec(x_209);
x_226 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_226, 0, x_206);
lean_ctor_set(x_226, 1, x_207);
lean_ctor_set(x_226, 2, x_208);
lean_ctor_set(x_226, 3, x_225);
lean_ctor_set(x_226, 4, x_210);
lean_ctor_set(x_226, 5, x_211);
lean_ctor_set(x_226, 6, x_212);
lean_ctor_set(x_226, 7, x_213);
lean_ctor_set(x_226, 8, x_214);
lean_ctor_set(x_226, 9, x_215);
lean_ctor_set(x_226, 10, x_216);
lean_ctor_set(x_226, 11, x_217);
lean_ctor_set(x_226, 12, x_219);
lean_ctor_set(x_226, 13, x_221);
lean_ctor_set_uint8(x_226, sizeof(void*)*14, x_218);
lean_ctor_set_uint8(x_226, sizeof(void*)*14 + 1, x_220);
lean_inc(x_223);
x_227 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(x_223, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_226, x_11);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
if (lean_obj_tag(x_228) == 1)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_252; lean_object* x_253; 
lean_dec(x_229);
x_230 = lean_ctor_get(x_228, 0);
lean_inc(x_230);
lean_dec_ref(x_228);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_231, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_231, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_236 = x_231;
} else {
 lean_dec_ref(x_231);
 x_236 = lean_box(0);
}
x_252 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_253 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_252, x_226);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = lean_unbox(x_254);
lean_dec(x_254);
if (x_255 == 0)
{
lean_dec(x_233);
x_237 = x_2;
x_238 = x_3;
x_239 = x_4;
x_240 = x_5;
x_241 = x_6;
x_242 = x_7;
x_243 = x_8;
x_244 = x_9;
x_245 = x_226;
x_246 = x_11;
x_247 = lean_box(0);
goto block_251;
}
else
{
lean_object* x_256; 
x_256 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_232, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_226, x_11);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec_ref(x_256);
x_258 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_226, x_11);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec_ref(x_258);
x_260 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_234, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_226, x_11);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
lean_dec_ref(x_260);
x_262 = l_Lean_MessageData_ofExpr(x_257);
x_263 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
if (lean_is_scalar(x_233)) {
 x_264 = lean_alloc_ctor(7, 2, 0);
} else {
 x_264 = x_233;
 lean_ctor_set_tag(x_264, 7);
}
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = l_Lean_MessageData_ofExpr(x_259);
x_266 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_263);
x_268 = l_Lean_MessageData_ofExpr(x_261);
x_269 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_252, x_269, x_8, x_9, x_226, x_11);
if (lean_obj_tag(x_270) == 0)
{
lean_dec_ref(x_270);
x_237 = x_2;
x_238 = x_3;
x_239 = x_4;
x_240 = x_5;
x_241 = x_6;
x_242 = x_7;
x_243 = x_8;
x_244 = x_9;
x_245 = x_226;
x_246 = x_11;
x_247 = lean_box(0);
goto block_251;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_232);
lean_dec_ref(x_226);
lean_dec_ref(x_1);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 x_272 = x_270;
} else {
 lean_dec_ref(x_270);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 1, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_271);
return x_273;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_259);
lean_dec(x_257);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_226);
lean_dec_ref(x_1);
x_274 = lean_ctor_get(x_260, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 x_275 = x_260;
} else {
 lean_dec_ref(x_260);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 1, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_274);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_257);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_226);
lean_dec_ref(x_1);
x_277 = lean_ctor_get(x_258, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 x_278 = x_258;
} else {
 lean_dec_ref(x_258);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 1, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_277);
return x_279;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_226);
lean_dec_ref(x_1);
x_280 = lean_ctor_get(x_256, 0);
lean_inc(x_280);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 x_281 = x_256;
} else {
 lean_dec_ref(x_256);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 1, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_280);
return x_282;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_226);
lean_dec_ref(x_1);
x_283 = lean_ctor_get(x_253, 0);
lean_inc(x_283);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_284 = x_253;
} else {
 lean_dec_ref(x_253);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 1, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_283);
return x_285;
}
block_251:
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_248, 0, x_232);
lean_ctor_set(x_248, 1, x_234);
lean_ctor_set(x_248, 2, x_1);
if (lean_is_scalar(x_236)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_236;
}
lean_ctor_set(x_249, 0, x_235);
lean_ctor_set(x_249, 1, x_248);
x_1 = x_249;
x_2 = x_237;
x_3 = x_238;
x_4 = x_239;
x_5 = x_240;
x_6 = x_241;
x_7 = x_242;
x_8 = x_243;
x_9 = x_244;
x_10 = x_245;
x_11 = x_246;
goto _start;
}
}
else
{
lean_object* x_286; 
lean_dec(x_228);
lean_dec_ref(x_226);
if (lean_is_scalar(x_229)) {
 x_286 = lean_alloc_ctor(0, 1, 0);
} else {
 x_286 = x_229;
}
lean_ctor_set(x_286, 0, x_1);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec_ref(x_226);
lean_dec_ref(x_1);
x_287 = lean_ctor_get(x_227, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 x_288 = x_227;
} else {
 lean_dec_ref(x_227);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 1, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_287);
return x_289;
}
}
else
{
lean_object* x_290; 
lean_dec_ref(x_221);
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_210);
lean_dec(x_209);
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_1);
x_290 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_211);
return x_290;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind linarith` internal error, structure is not an ordered int module", 71, 71);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 20);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_free_object(x_12);
x_17 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1;
x_18 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(x_17, x_7, x_8, x_9, x_10);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_19, 20);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
x_23 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1;
x_24 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(x_23, x_7, x_8, x_9, x_10);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind linarith` internal error, structure is not an ordered module", 67, 67);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 21);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_free_object(x_12);
x_17 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1;
x_18 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(x_17, x_7, x_8, x_9, x_10);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_19, 21);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
x_23 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1;
x_24 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(x_23, x_7, x_8, x_9, x_10);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_2 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 18);
lean_inc_ref(x_21);
lean_dec(x_20);
x_22 = l_Lean_mkAppB(x_15, x_17, x_21);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_23, 18);
lean_inc_ref(x_24);
lean_dec(x_23);
x_25 = l_Lean_mkAppB(x_15, x_17, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_15);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_dec(x_15);
return x_16;
}
}
else
{
return x_14;
}
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_36, 18);
lean_inc_ref(x_37);
lean_dec(x_36);
x_38 = l_Lean_mkAppB(x_31, x_33, x_37);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_ctor_get(x_39, 18);
lean_inc_ref(x_40);
lean_dec(x_39);
x_41 = l_Lean_mkAppB(x_31, x_33, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_33);
lean_dec(x_31);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_34, 0);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
lean_dec(x_31);
return x_32;
}
}
else
{
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_34; 
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0;
x_18 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_17, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_20 = x_18;
} else {
 lean_dec_ref(x_18);
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
x_34 = lean_unbox(x_19);
lean_dec(x_19);
if (x_34 == 0)
{
x_29 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_MessageData_ofExpr(x_36);
x_42 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_MessageData_ofExpr(x_38);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
x_47 = l_Lean_MessageData_ofExpr(x_40);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_17, x_48, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_49) == 0)
{
lean_dec_ref(x_49);
x_29 = lean_box(0);
goto block_33;
}
else
{
uint8_t x_50; 
lean_dec(x_28);
lean_dec(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_39);
if (x_53 == 0)
{
return x_39;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_39, 0);
lean_inc(x_54);
lean_dec(x_39);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_37);
if (x_56 == 0)
{
return x_37;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_37, 0);
lean_inc(x_57);
lean_dec(x_37);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_28);
lean_dec(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_35);
if (x_59 == 0)
{
return x_35;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_35, 0);
lean_inc(x_60);
lean_dec(x_35);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
block_33:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_5);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_23);
if (lean_is_scalar(x_20)) {
 x_32 = lean_alloc_ctor(0, 1, 0);
} else {
 x_32 = x_20;
}
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_8, x_7);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_dec_ref(x_9);
x_23 = lean_array_uget(x_6, x_8);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(x_1, x_2, x_3, x_25, x_26, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_29 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec_ref(x_29);
x_30 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
size_t x_34; size_t x_35; 
lean_free_object(x_30);
lean_free_object(x_23);
x_34 = 1;
x_35 = lean_usize_add(x_8, x_34);
lean_inc_ref(x_4);
{
size_t _tmp_7 = x_35;
lean_object* _tmp_8 = x_4;
x_8 = _tmp_7;
x_9 = _tmp_8;
}
goto _start;
}
else
{
lean_object* x_37; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0;
lean_ctor_set(x_23, 1, x_5);
lean_ctor_set(x_23, 0, x_37);
lean_ctor_set(x_30, 0, x_23);
return x_30;
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
size_t x_40; size_t x_41; 
lean_free_object(x_23);
x_40 = 1;
x_41 = lean_usize_add(x_8, x_40);
lean_inc_ref(x_4);
{
size_t _tmp_7 = x_41;
lean_object* _tmp_8 = x_4;
x_8 = _tmp_7;
x_9 = _tmp_8;
}
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0;
lean_ctor_set(x_23, 1, x_5);
lean_ctor_set(x_23, 0, x_43);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_23);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_free_object(x_23);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_30);
if (x_45 == 0)
{
return x_30;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_30, 0);
lean_inc(x_46);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_23);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
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
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_29, 0);
lean_inc(x_49);
lean_dec(x_29);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_free_object(x_23);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_27);
if (x_51 == 0)
{
return x_27;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_27, 0);
lean_inc(x_52);
lean_dec(x_27);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_23, 0);
x_55 = lean_ctor_get(x_23, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_23);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_56 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(x_1, x_2, x_3, x_54, x_55, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_58 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_57, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_dec_ref(x_58);
x_59 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_unbox(x_60);
lean_dec(x_60);
if (x_62 == 0)
{
size_t x_63; size_t x_64; 
lean_dec(x_61);
x_63 = 1;
x_64 = lean_usize_add(x_8, x_63);
lean_inc_ref(x_4);
{
size_t _tmp_7 = x_64;
lean_object* _tmp_8 = x_4;
x_8 = _tmp_7;
x_9 = _tmp_8;
}
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0;
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_5);
if (lean_is_scalar(x_61)) {
 x_68 = lean_alloc_ctor(0, 1, 0);
} else {
 x_68 = x_61;
}
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_70 = x_59;
} else {
 lean_dec_ref(x_59);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_ctor_get(x_58, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_73 = x_58;
} else {
 lean_dec_ref(x_58);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = lean_ctor_get(x_56, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_76 = x_56;
} else {
 lean_dec_ref(x_56);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args) {
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
lean_object* x_20 = _args[19];
_start:
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_22 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec_ref(x_6);
return x_23;
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
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_box(0);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0;
x_18 = lean_array_size(x_4);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(x_1, x_2, x_3, x_17, x_16, x_4, x_18, x_19, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_ctor_set(x_20, 0, x_16);
return x_20;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_16);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
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
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(x_3, x_1, x_2, x_4, x_5, x_11, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
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
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(x_3, x_1, x_2, x_4, x_5, x_11, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(x_1, x_2, x_3, x_8, x_7, x_10, x_11, x_9);
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
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(x_1, x_2, x_3, x_17, x_16, x_19, x_20, x_18);
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
x_32 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_28, x_27, x_30, x_31, x_29);
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
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_37, x_36, x_39, x_40, x_38);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
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
x_14 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_13, x_11);
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
x_22 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_21, x_20);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_7 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(x_1, x_2, x_4, x_5, x_4);
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
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(x_1, x_2, x_10, x_6, x_12, x_13, x_11);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0;
x_4 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3;
x_2 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__4;
x_5 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(x_1, x_3, x_2, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(x_1, x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_1, x_13);
if (x_14 == 0)
{
lean_dec_ref(x_3);
return x_4;
}
else
{
uint8_t x_15; 
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_4, 7);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 6);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 5);
lean_dec(x_18);
x_19 = lean_ctor_get(x_4, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_fget(x_5, x_1);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 32);
x_27 = lean_box(0);
x_28 = lean_array_fset(x_5, x_1, x_27);
x_29 = l_Lean_PersistentArray_set___redArg(x_26, x_2, x_3);
lean_ctor_set(x_24, 32, x_29);
x_30 = lean_array_fset(x_28, x_1, x_24);
lean_ctor_set(x_4, 0, x_30);
return x_4;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
x_33 = lean_ctor_get(x_24, 2);
x_34 = lean_ctor_get(x_24, 3);
x_35 = lean_ctor_get(x_24, 4);
x_36 = lean_ctor_get(x_24, 5);
x_37 = lean_ctor_get(x_24, 6);
x_38 = lean_ctor_get(x_24, 7);
x_39 = lean_ctor_get(x_24, 8);
x_40 = lean_ctor_get(x_24, 9);
x_41 = lean_ctor_get(x_24, 10);
x_42 = lean_ctor_get(x_24, 11);
x_43 = lean_ctor_get(x_24, 12);
x_44 = lean_ctor_get(x_24, 13);
x_45 = lean_ctor_get(x_24, 14);
x_46 = lean_ctor_get(x_24, 15);
x_47 = lean_ctor_get(x_24, 16);
x_48 = lean_ctor_get(x_24, 17);
x_49 = lean_ctor_get(x_24, 18);
x_50 = lean_ctor_get(x_24, 19);
x_51 = lean_ctor_get(x_24, 20);
x_52 = lean_ctor_get(x_24, 21);
x_53 = lean_ctor_get(x_24, 22);
x_54 = lean_ctor_get(x_24, 23);
x_55 = lean_ctor_get(x_24, 24);
x_56 = lean_ctor_get(x_24, 25);
x_57 = lean_ctor_get(x_24, 26);
x_58 = lean_ctor_get(x_24, 27);
x_59 = lean_ctor_get(x_24, 28);
x_60 = lean_ctor_get(x_24, 29);
x_61 = lean_ctor_get(x_24, 30);
x_62 = lean_ctor_get(x_24, 31);
x_63 = lean_ctor_get(x_24, 32);
x_64 = lean_ctor_get(x_24, 33);
x_65 = lean_ctor_get(x_24, 34);
x_66 = lean_ctor_get(x_24, 35);
x_67 = lean_ctor_get_uint8(x_24, sizeof(void*)*42);
x_68 = lean_ctor_get(x_24, 36);
x_69 = lean_ctor_get(x_24, 37);
x_70 = lean_ctor_get(x_24, 38);
x_71 = lean_ctor_get(x_24, 39);
x_72 = lean_ctor_get(x_24, 40);
x_73 = lean_ctor_get(x_24, 41);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_74 = lean_box(0);
x_75 = lean_array_fset(x_5, x_1, x_74);
x_76 = l_Lean_PersistentArray_set___redArg(x_63, x_2, x_3);
x_77 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_77, 0, x_31);
lean_ctor_set(x_77, 1, x_32);
lean_ctor_set(x_77, 2, x_33);
lean_ctor_set(x_77, 3, x_34);
lean_ctor_set(x_77, 4, x_35);
lean_ctor_set(x_77, 5, x_36);
lean_ctor_set(x_77, 6, x_37);
lean_ctor_set(x_77, 7, x_38);
lean_ctor_set(x_77, 8, x_39);
lean_ctor_set(x_77, 9, x_40);
lean_ctor_set(x_77, 10, x_41);
lean_ctor_set(x_77, 11, x_42);
lean_ctor_set(x_77, 12, x_43);
lean_ctor_set(x_77, 13, x_44);
lean_ctor_set(x_77, 14, x_45);
lean_ctor_set(x_77, 15, x_46);
lean_ctor_set(x_77, 16, x_47);
lean_ctor_set(x_77, 17, x_48);
lean_ctor_set(x_77, 18, x_49);
lean_ctor_set(x_77, 19, x_50);
lean_ctor_set(x_77, 20, x_51);
lean_ctor_set(x_77, 21, x_52);
lean_ctor_set(x_77, 22, x_53);
lean_ctor_set(x_77, 23, x_54);
lean_ctor_set(x_77, 24, x_55);
lean_ctor_set(x_77, 25, x_56);
lean_ctor_set(x_77, 26, x_57);
lean_ctor_set(x_77, 27, x_58);
lean_ctor_set(x_77, 28, x_59);
lean_ctor_set(x_77, 29, x_60);
lean_ctor_set(x_77, 30, x_61);
lean_ctor_set(x_77, 31, x_62);
lean_ctor_set(x_77, 32, x_76);
lean_ctor_set(x_77, 33, x_64);
lean_ctor_set(x_77, 34, x_65);
lean_ctor_set(x_77, 35, x_66);
lean_ctor_set(x_77, 36, x_68);
lean_ctor_set(x_77, 37, x_69);
lean_ctor_set(x_77, 38, x_70);
lean_ctor_set(x_77, 39, x_71);
lean_ctor_set(x_77, 40, x_72);
lean_ctor_set(x_77, 41, x_73);
lean_ctor_set_uint8(x_77, sizeof(void*)*42, x_67);
x_78 = lean_array_fset(x_75, x_1, x_77);
lean_ctor_set(x_4, 0, x_78);
return x_4;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_4);
x_79 = lean_array_fget(x_5, x_1);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 2);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_79, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_79, 4);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_79, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 6);
lean_inc(x_86);
x_87 = lean_ctor_get(x_79, 7);
lean_inc(x_87);
x_88 = lean_ctor_get(x_79, 8);
lean_inc(x_88);
x_89 = lean_ctor_get(x_79, 9);
lean_inc(x_89);
x_90 = lean_ctor_get(x_79, 10);
lean_inc(x_90);
x_91 = lean_ctor_get(x_79, 11);
lean_inc(x_91);
x_92 = lean_ctor_get(x_79, 12);
lean_inc(x_92);
x_93 = lean_ctor_get(x_79, 13);
lean_inc(x_93);
x_94 = lean_ctor_get(x_79, 14);
lean_inc(x_94);
x_95 = lean_ctor_get(x_79, 15);
lean_inc(x_95);
x_96 = lean_ctor_get(x_79, 16);
lean_inc(x_96);
x_97 = lean_ctor_get(x_79, 17);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_79, 18);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_79, 19);
lean_inc(x_99);
x_100 = lean_ctor_get(x_79, 20);
lean_inc(x_100);
x_101 = lean_ctor_get(x_79, 21);
lean_inc(x_101);
x_102 = lean_ctor_get(x_79, 22);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_79, 23);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_79, 24);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_79, 25);
lean_inc(x_105);
x_106 = lean_ctor_get(x_79, 26);
lean_inc(x_106);
x_107 = lean_ctor_get(x_79, 27);
lean_inc(x_107);
x_108 = lean_ctor_get(x_79, 28);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_79, 29);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_79, 30);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_79, 31);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_79, 32);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_79, 33);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_79, 34);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_79, 35);
lean_inc_ref(x_115);
x_116 = lean_ctor_get_uint8(x_79, sizeof(void*)*42);
x_117 = lean_ctor_get(x_79, 36);
lean_inc(x_117);
x_118 = lean_ctor_get(x_79, 37);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_79, 38);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_79, 39);
lean_inc(x_120);
x_121 = lean_ctor_get(x_79, 40);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_79, 41);
lean_inc_ref(x_122);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 lean_ctor_release(x_79, 3);
 lean_ctor_release(x_79, 4);
 lean_ctor_release(x_79, 5);
 lean_ctor_release(x_79, 6);
 lean_ctor_release(x_79, 7);
 lean_ctor_release(x_79, 8);
 lean_ctor_release(x_79, 9);
 lean_ctor_release(x_79, 10);
 lean_ctor_release(x_79, 11);
 lean_ctor_release(x_79, 12);
 lean_ctor_release(x_79, 13);
 lean_ctor_release(x_79, 14);
 lean_ctor_release(x_79, 15);
 lean_ctor_release(x_79, 16);
 lean_ctor_release(x_79, 17);
 lean_ctor_release(x_79, 18);
 lean_ctor_release(x_79, 19);
 lean_ctor_release(x_79, 20);
 lean_ctor_release(x_79, 21);
 lean_ctor_release(x_79, 22);
 lean_ctor_release(x_79, 23);
 lean_ctor_release(x_79, 24);
 lean_ctor_release(x_79, 25);
 lean_ctor_release(x_79, 26);
 lean_ctor_release(x_79, 27);
 lean_ctor_release(x_79, 28);
 lean_ctor_release(x_79, 29);
 lean_ctor_release(x_79, 30);
 lean_ctor_release(x_79, 31);
 lean_ctor_release(x_79, 32);
 lean_ctor_release(x_79, 33);
 lean_ctor_release(x_79, 34);
 lean_ctor_release(x_79, 35);
 lean_ctor_release(x_79, 36);
 lean_ctor_release(x_79, 37);
 lean_ctor_release(x_79, 38);
 lean_ctor_release(x_79, 39);
 lean_ctor_release(x_79, 40);
 lean_ctor_release(x_79, 41);
 x_123 = x_79;
} else {
 lean_dec_ref(x_79);
 x_123 = lean_box(0);
}
x_124 = lean_box(0);
x_125 = lean_array_fset(x_5, x_1, x_124);
x_126 = l_Lean_PersistentArray_set___redArg(x_112, x_2, x_3);
if (lean_is_scalar(x_123)) {
 x_127 = lean_alloc_ctor(0, 42, 1);
} else {
 x_127 = x_123;
}
lean_ctor_set(x_127, 0, x_80);
lean_ctor_set(x_127, 1, x_81);
lean_ctor_set(x_127, 2, x_82);
lean_ctor_set(x_127, 3, x_83);
lean_ctor_set(x_127, 4, x_84);
lean_ctor_set(x_127, 5, x_85);
lean_ctor_set(x_127, 6, x_86);
lean_ctor_set(x_127, 7, x_87);
lean_ctor_set(x_127, 8, x_88);
lean_ctor_set(x_127, 9, x_89);
lean_ctor_set(x_127, 10, x_90);
lean_ctor_set(x_127, 11, x_91);
lean_ctor_set(x_127, 12, x_92);
lean_ctor_set(x_127, 13, x_93);
lean_ctor_set(x_127, 14, x_94);
lean_ctor_set(x_127, 15, x_95);
lean_ctor_set(x_127, 16, x_96);
lean_ctor_set(x_127, 17, x_97);
lean_ctor_set(x_127, 18, x_98);
lean_ctor_set(x_127, 19, x_99);
lean_ctor_set(x_127, 20, x_100);
lean_ctor_set(x_127, 21, x_101);
lean_ctor_set(x_127, 22, x_102);
lean_ctor_set(x_127, 23, x_103);
lean_ctor_set(x_127, 24, x_104);
lean_ctor_set(x_127, 25, x_105);
lean_ctor_set(x_127, 26, x_106);
lean_ctor_set(x_127, 27, x_107);
lean_ctor_set(x_127, 28, x_108);
lean_ctor_set(x_127, 29, x_109);
lean_ctor_set(x_127, 30, x_110);
lean_ctor_set(x_127, 31, x_111);
lean_ctor_set(x_127, 32, x_126);
lean_ctor_set(x_127, 33, x_113);
lean_ctor_set(x_127, 34, x_114);
lean_ctor_set(x_127, 35, x_115);
lean_ctor_set(x_127, 36, x_117);
lean_ctor_set(x_127, 37, x_118);
lean_ctor_set(x_127, 38, x_119);
lean_ctor_set(x_127, 39, x_120);
lean_ctor_set(x_127, 40, x_121);
lean_ctor_set(x_127, 41, x_122);
lean_ctor_set_uint8(x_127, sizeof(void*)*42, x_116);
x_128 = lean_array_fset(x_125, x_1, x_127);
x_129 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_6);
lean_ctor_set(x_129, 2, x_7);
lean_ctor_set(x_129, 3, x_8);
lean_ctor_set(x_129, 4, x_9);
lean_ctor_set(x_129, 5, x_10);
lean_ctor_set(x_129, 6, x_11);
lean_ctor_set(x_129, 7, x_12);
return x_129;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_16);
x_20 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_31 = lean_ctor_get(x_21, 32);
lean_inc_ref(x_31);
lean_dec(x_21);
x_32 = lean_ctor_get(x_31, 2);
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0;
x_34 = lean_nat_dec_lt(x_4, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec_ref(x_31);
x_35 = l_outOfBounds___redArg(x_33);
x_22 = x_35;
goto block_30;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_PersistentArray_get_x21___redArg(x_33, x_31, x_4);
x_22 = x_36;
goto block_30;
}
block_30:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(x_2, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_inc(x_5);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(x_26, 0, x_5);
lean_closure_set(x_26, 1, x_4);
lean_closure_set(x_26, 2, x_24);
x_27 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_28 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_27, x_26, x_6);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_dec_ref(x_28);
x_29 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_1, x_2, x_3, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_25);
return x_29;
}
else
{
lean_dec(x_25);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_28;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_20, 0);
lean_inc(x_38);
lean_dec(x_20);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_box(0);
lean_ctor_set(x_16, 0, x_40);
return x_16;
}
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_16, 0);
lean_inc(x_41);
lean_dec(x_16);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_54 = lean_ctor_get(x_44, 32);
lean_inc_ref(x_54);
lean_dec(x_44);
x_55 = lean_ctor_get(x_54, 2);
x_56 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0;
x_57 = lean_nat_dec_lt(x_4, x_55);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec_ref(x_54);
x_58 = l_outOfBounds___redArg(x_56);
x_45 = x_58;
goto block_53;
}
else
{
lean_object* x_59; 
x_59 = l_Lean_PersistentArray_get_x21___redArg(x_56, x_54, x_4);
x_45 = x_59;
goto block_53;
}
block_53:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(x_2, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
lean_inc(x_5);
x_49 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(x_49, 0, x_5);
lean_closure_set(x_49, 1, x_4);
lean_closure_set(x_49, 2, x_47);
x_50 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_51 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_50, x_49, x_6);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
lean_dec_ref(x_51);
x_52 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_1, x_2, x_3, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_48);
return x_52;
}
else
{
lean_dec(x_48);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_51;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_ctor_get(x_43, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_61 = x_43;
} else {
 lean_dec_ref(x_43);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_16);
if (x_65 == 0)
{
return x_16;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_16, 0);
lean_inc(x_66);
lean_dec(x_16);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_1, x_13);
if (x_14 == 0)
{
lean_dec_ref(x_3);
return x_4;
}
else
{
uint8_t x_15; 
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_4, 7);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 6);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 5);
lean_dec(x_18);
x_19 = lean_ctor_get(x_4, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_fget(x_5, x_1);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 33);
x_27 = lean_box(0);
x_28 = lean_array_fset(x_5, x_1, x_27);
x_29 = l_Lean_PersistentArray_set___redArg(x_26, x_2, x_3);
lean_ctor_set(x_24, 33, x_29);
x_30 = lean_array_fset(x_28, x_1, x_24);
lean_ctor_set(x_4, 0, x_30);
return x_4;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
x_33 = lean_ctor_get(x_24, 2);
x_34 = lean_ctor_get(x_24, 3);
x_35 = lean_ctor_get(x_24, 4);
x_36 = lean_ctor_get(x_24, 5);
x_37 = lean_ctor_get(x_24, 6);
x_38 = lean_ctor_get(x_24, 7);
x_39 = lean_ctor_get(x_24, 8);
x_40 = lean_ctor_get(x_24, 9);
x_41 = lean_ctor_get(x_24, 10);
x_42 = lean_ctor_get(x_24, 11);
x_43 = lean_ctor_get(x_24, 12);
x_44 = lean_ctor_get(x_24, 13);
x_45 = lean_ctor_get(x_24, 14);
x_46 = lean_ctor_get(x_24, 15);
x_47 = lean_ctor_get(x_24, 16);
x_48 = lean_ctor_get(x_24, 17);
x_49 = lean_ctor_get(x_24, 18);
x_50 = lean_ctor_get(x_24, 19);
x_51 = lean_ctor_get(x_24, 20);
x_52 = lean_ctor_get(x_24, 21);
x_53 = lean_ctor_get(x_24, 22);
x_54 = lean_ctor_get(x_24, 23);
x_55 = lean_ctor_get(x_24, 24);
x_56 = lean_ctor_get(x_24, 25);
x_57 = lean_ctor_get(x_24, 26);
x_58 = lean_ctor_get(x_24, 27);
x_59 = lean_ctor_get(x_24, 28);
x_60 = lean_ctor_get(x_24, 29);
x_61 = lean_ctor_get(x_24, 30);
x_62 = lean_ctor_get(x_24, 31);
x_63 = lean_ctor_get(x_24, 32);
x_64 = lean_ctor_get(x_24, 33);
x_65 = lean_ctor_get(x_24, 34);
x_66 = lean_ctor_get(x_24, 35);
x_67 = lean_ctor_get_uint8(x_24, sizeof(void*)*42);
x_68 = lean_ctor_get(x_24, 36);
x_69 = lean_ctor_get(x_24, 37);
x_70 = lean_ctor_get(x_24, 38);
x_71 = lean_ctor_get(x_24, 39);
x_72 = lean_ctor_get(x_24, 40);
x_73 = lean_ctor_get(x_24, 41);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_74 = lean_box(0);
x_75 = lean_array_fset(x_5, x_1, x_74);
x_76 = l_Lean_PersistentArray_set___redArg(x_64, x_2, x_3);
x_77 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_77, 0, x_31);
lean_ctor_set(x_77, 1, x_32);
lean_ctor_set(x_77, 2, x_33);
lean_ctor_set(x_77, 3, x_34);
lean_ctor_set(x_77, 4, x_35);
lean_ctor_set(x_77, 5, x_36);
lean_ctor_set(x_77, 6, x_37);
lean_ctor_set(x_77, 7, x_38);
lean_ctor_set(x_77, 8, x_39);
lean_ctor_set(x_77, 9, x_40);
lean_ctor_set(x_77, 10, x_41);
lean_ctor_set(x_77, 11, x_42);
lean_ctor_set(x_77, 12, x_43);
lean_ctor_set(x_77, 13, x_44);
lean_ctor_set(x_77, 14, x_45);
lean_ctor_set(x_77, 15, x_46);
lean_ctor_set(x_77, 16, x_47);
lean_ctor_set(x_77, 17, x_48);
lean_ctor_set(x_77, 18, x_49);
lean_ctor_set(x_77, 19, x_50);
lean_ctor_set(x_77, 20, x_51);
lean_ctor_set(x_77, 21, x_52);
lean_ctor_set(x_77, 22, x_53);
lean_ctor_set(x_77, 23, x_54);
lean_ctor_set(x_77, 24, x_55);
lean_ctor_set(x_77, 25, x_56);
lean_ctor_set(x_77, 26, x_57);
lean_ctor_set(x_77, 27, x_58);
lean_ctor_set(x_77, 28, x_59);
lean_ctor_set(x_77, 29, x_60);
lean_ctor_set(x_77, 30, x_61);
lean_ctor_set(x_77, 31, x_62);
lean_ctor_set(x_77, 32, x_63);
lean_ctor_set(x_77, 33, x_76);
lean_ctor_set(x_77, 34, x_65);
lean_ctor_set(x_77, 35, x_66);
lean_ctor_set(x_77, 36, x_68);
lean_ctor_set(x_77, 37, x_69);
lean_ctor_set(x_77, 38, x_70);
lean_ctor_set(x_77, 39, x_71);
lean_ctor_set(x_77, 40, x_72);
lean_ctor_set(x_77, 41, x_73);
lean_ctor_set_uint8(x_77, sizeof(void*)*42, x_67);
x_78 = lean_array_fset(x_75, x_1, x_77);
lean_ctor_set(x_4, 0, x_78);
return x_4;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_4);
x_79 = lean_array_fget(x_5, x_1);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 2);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_79, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_79, 4);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_79, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 6);
lean_inc(x_86);
x_87 = lean_ctor_get(x_79, 7);
lean_inc(x_87);
x_88 = lean_ctor_get(x_79, 8);
lean_inc(x_88);
x_89 = lean_ctor_get(x_79, 9);
lean_inc(x_89);
x_90 = lean_ctor_get(x_79, 10);
lean_inc(x_90);
x_91 = lean_ctor_get(x_79, 11);
lean_inc(x_91);
x_92 = lean_ctor_get(x_79, 12);
lean_inc(x_92);
x_93 = lean_ctor_get(x_79, 13);
lean_inc(x_93);
x_94 = lean_ctor_get(x_79, 14);
lean_inc(x_94);
x_95 = lean_ctor_get(x_79, 15);
lean_inc(x_95);
x_96 = lean_ctor_get(x_79, 16);
lean_inc(x_96);
x_97 = lean_ctor_get(x_79, 17);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_79, 18);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_79, 19);
lean_inc(x_99);
x_100 = lean_ctor_get(x_79, 20);
lean_inc(x_100);
x_101 = lean_ctor_get(x_79, 21);
lean_inc(x_101);
x_102 = lean_ctor_get(x_79, 22);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_79, 23);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_79, 24);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_79, 25);
lean_inc(x_105);
x_106 = lean_ctor_get(x_79, 26);
lean_inc(x_106);
x_107 = lean_ctor_get(x_79, 27);
lean_inc(x_107);
x_108 = lean_ctor_get(x_79, 28);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_79, 29);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_79, 30);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_79, 31);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_79, 32);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_79, 33);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_79, 34);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_79, 35);
lean_inc_ref(x_115);
x_116 = lean_ctor_get_uint8(x_79, sizeof(void*)*42);
x_117 = lean_ctor_get(x_79, 36);
lean_inc(x_117);
x_118 = lean_ctor_get(x_79, 37);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_79, 38);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_79, 39);
lean_inc(x_120);
x_121 = lean_ctor_get(x_79, 40);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_79, 41);
lean_inc_ref(x_122);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 lean_ctor_release(x_79, 3);
 lean_ctor_release(x_79, 4);
 lean_ctor_release(x_79, 5);
 lean_ctor_release(x_79, 6);
 lean_ctor_release(x_79, 7);
 lean_ctor_release(x_79, 8);
 lean_ctor_release(x_79, 9);
 lean_ctor_release(x_79, 10);
 lean_ctor_release(x_79, 11);
 lean_ctor_release(x_79, 12);
 lean_ctor_release(x_79, 13);
 lean_ctor_release(x_79, 14);
 lean_ctor_release(x_79, 15);
 lean_ctor_release(x_79, 16);
 lean_ctor_release(x_79, 17);
 lean_ctor_release(x_79, 18);
 lean_ctor_release(x_79, 19);
 lean_ctor_release(x_79, 20);
 lean_ctor_release(x_79, 21);
 lean_ctor_release(x_79, 22);
 lean_ctor_release(x_79, 23);
 lean_ctor_release(x_79, 24);
 lean_ctor_release(x_79, 25);
 lean_ctor_release(x_79, 26);
 lean_ctor_release(x_79, 27);
 lean_ctor_release(x_79, 28);
 lean_ctor_release(x_79, 29);
 lean_ctor_release(x_79, 30);
 lean_ctor_release(x_79, 31);
 lean_ctor_release(x_79, 32);
 lean_ctor_release(x_79, 33);
 lean_ctor_release(x_79, 34);
 lean_ctor_release(x_79, 35);
 lean_ctor_release(x_79, 36);
 lean_ctor_release(x_79, 37);
 lean_ctor_release(x_79, 38);
 lean_ctor_release(x_79, 39);
 lean_ctor_release(x_79, 40);
 lean_ctor_release(x_79, 41);
 x_123 = x_79;
} else {
 lean_dec_ref(x_79);
 x_123 = lean_box(0);
}
x_124 = lean_box(0);
x_125 = lean_array_fset(x_5, x_1, x_124);
x_126 = l_Lean_PersistentArray_set___redArg(x_113, x_2, x_3);
if (lean_is_scalar(x_123)) {
 x_127 = lean_alloc_ctor(0, 42, 1);
} else {
 x_127 = x_123;
}
lean_ctor_set(x_127, 0, x_80);
lean_ctor_set(x_127, 1, x_81);
lean_ctor_set(x_127, 2, x_82);
lean_ctor_set(x_127, 3, x_83);
lean_ctor_set(x_127, 4, x_84);
lean_ctor_set(x_127, 5, x_85);
lean_ctor_set(x_127, 6, x_86);
lean_ctor_set(x_127, 7, x_87);
lean_ctor_set(x_127, 8, x_88);
lean_ctor_set(x_127, 9, x_89);
lean_ctor_set(x_127, 10, x_90);
lean_ctor_set(x_127, 11, x_91);
lean_ctor_set(x_127, 12, x_92);
lean_ctor_set(x_127, 13, x_93);
lean_ctor_set(x_127, 14, x_94);
lean_ctor_set(x_127, 15, x_95);
lean_ctor_set(x_127, 16, x_96);
lean_ctor_set(x_127, 17, x_97);
lean_ctor_set(x_127, 18, x_98);
lean_ctor_set(x_127, 19, x_99);
lean_ctor_set(x_127, 20, x_100);
lean_ctor_set(x_127, 21, x_101);
lean_ctor_set(x_127, 22, x_102);
lean_ctor_set(x_127, 23, x_103);
lean_ctor_set(x_127, 24, x_104);
lean_ctor_set(x_127, 25, x_105);
lean_ctor_set(x_127, 26, x_106);
lean_ctor_set(x_127, 27, x_107);
lean_ctor_set(x_127, 28, x_108);
lean_ctor_set(x_127, 29, x_109);
lean_ctor_set(x_127, 30, x_110);
lean_ctor_set(x_127, 31, x_111);
lean_ctor_set(x_127, 32, x_112);
lean_ctor_set(x_127, 33, x_126);
lean_ctor_set(x_127, 34, x_114);
lean_ctor_set(x_127, 35, x_115);
lean_ctor_set(x_127, 36, x_117);
lean_ctor_set(x_127, 37, x_118);
lean_ctor_set(x_127, 38, x_119);
lean_ctor_set(x_127, 39, x_120);
lean_ctor_set(x_127, 40, x_121);
lean_ctor_set(x_127, 41, x_122);
lean_ctor_set_uint8(x_127, sizeof(void*)*42, x_116);
x_128 = lean_array_fset(x_125, x_1, x_127);
x_129 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_6);
lean_ctor_set(x_129, 2, x_7);
lean_ctor_set(x_129, 3, x_8);
lean_ctor_set(x_129, 4, x_9);
lean_ctor_set(x_129, 5, x_10);
lean_ctor_set(x_129, 6, x_11);
lean_ctor_set(x_129, 7, x_12);
return x_129;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_16);
x_20 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_31 = lean_ctor_get(x_21, 33);
lean_inc_ref(x_31);
lean_dec(x_21);
x_32 = lean_ctor_get(x_31, 2);
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0;
x_34 = lean_nat_dec_lt(x_4, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec_ref(x_31);
x_35 = l_outOfBounds___redArg(x_33);
x_22 = x_35;
goto block_30;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_PersistentArray_get_x21___redArg(x_33, x_31, x_4);
x_22 = x_36;
goto block_30;
}
block_30:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(x_2, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_inc(x_5);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(x_26, 0, x_5);
lean_closure_set(x_26, 1, x_4);
lean_closure_set(x_26, 2, x_24);
x_27 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_28 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_27, x_26, x_6);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_dec_ref(x_28);
x_29 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_1, x_2, x_3, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_25);
return x_29;
}
else
{
lean_dec(x_25);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_28;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_20, 0);
lean_inc(x_38);
lean_dec(x_20);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_box(0);
lean_ctor_set(x_16, 0, x_40);
return x_16;
}
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_16, 0);
lean_inc(x_41);
lean_dec(x_16);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_54 = lean_ctor_get(x_44, 33);
lean_inc_ref(x_54);
lean_dec(x_44);
x_55 = lean_ctor_get(x_54, 2);
x_56 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0;
x_57 = lean_nat_dec_lt(x_4, x_55);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec_ref(x_54);
x_58 = l_outOfBounds___redArg(x_56);
x_45 = x_58;
goto block_53;
}
else
{
lean_object* x_59; 
x_59 = l_Lean_PersistentArray_get_x21___redArg(x_56, x_54, x_4);
x_45 = x_59;
goto block_53;
}
block_53:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(x_2, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
lean_inc(x_5);
x_49 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(x_49, 0, x_5);
lean_closure_set(x_49, 1, x_4);
lean_closure_set(x_49, 2, x_47);
x_50 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_51 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_50, x_49, x_6);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
lean_dec_ref(x_51);
x_52 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_1, x_2, x_3, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_48);
return x_52;
}
else
{
lean_dec(x_48);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_51;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_ctor_get(x_43, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_61 = x_43;
} else {
 lean_dec_ref(x_43);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_16);
if (x_65 == 0)
{
return x_16;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_16, 0);
lean_inc(x_66);
lean_dec(x_16);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_1, x_12);
if (x_13 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
uint8_t x_14; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_3, 7);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 6);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 5);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 4);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 3);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = lean_array_fget(x_4, x_1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 41);
x_26 = lean_box(0);
x_27 = lean_array_fset(x_4, x_1, x_26);
x_28 = l_Lean_PersistentArray_push___redArg(x_25, x_2);
lean_ctor_set(x_23, 41, x_28);
x_29 = lean_array_fset(x_27, x_1, x_23);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
x_32 = lean_ctor_get(x_23, 2);
x_33 = lean_ctor_get(x_23, 3);
x_34 = lean_ctor_get(x_23, 4);
x_35 = lean_ctor_get(x_23, 5);
x_36 = lean_ctor_get(x_23, 6);
x_37 = lean_ctor_get(x_23, 7);
x_38 = lean_ctor_get(x_23, 8);
x_39 = lean_ctor_get(x_23, 9);
x_40 = lean_ctor_get(x_23, 10);
x_41 = lean_ctor_get(x_23, 11);
x_42 = lean_ctor_get(x_23, 12);
x_43 = lean_ctor_get(x_23, 13);
x_44 = lean_ctor_get(x_23, 14);
x_45 = lean_ctor_get(x_23, 15);
x_46 = lean_ctor_get(x_23, 16);
x_47 = lean_ctor_get(x_23, 17);
x_48 = lean_ctor_get(x_23, 18);
x_49 = lean_ctor_get(x_23, 19);
x_50 = lean_ctor_get(x_23, 20);
x_51 = lean_ctor_get(x_23, 21);
x_52 = lean_ctor_get(x_23, 22);
x_53 = lean_ctor_get(x_23, 23);
x_54 = lean_ctor_get(x_23, 24);
x_55 = lean_ctor_get(x_23, 25);
x_56 = lean_ctor_get(x_23, 26);
x_57 = lean_ctor_get(x_23, 27);
x_58 = lean_ctor_get(x_23, 28);
x_59 = lean_ctor_get(x_23, 29);
x_60 = lean_ctor_get(x_23, 30);
x_61 = lean_ctor_get(x_23, 31);
x_62 = lean_ctor_get(x_23, 32);
x_63 = lean_ctor_get(x_23, 33);
x_64 = lean_ctor_get(x_23, 34);
x_65 = lean_ctor_get(x_23, 35);
x_66 = lean_ctor_get_uint8(x_23, sizeof(void*)*42);
x_67 = lean_ctor_get(x_23, 36);
x_68 = lean_ctor_get(x_23, 37);
x_69 = lean_ctor_get(x_23, 38);
x_70 = lean_ctor_get(x_23, 39);
x_71 = lean_ctor_get(x_23, 40);
x_72 = lean_ctor_get(x_23, 41);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_73 = lean_box(0);
x_74 = lean_array_fset(x_4, x_1, x_73);
x_75 = l_Lean_PersistentArray_push___redArg(x_72, x_2);
x_76 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_76, 0, x_30);
lean_ctor_set(x_76, 1, x_31);
lean_ctor_set(x_76, 2, x_32);
lean_ctor_set(x_76, 3, x_33);
lean_ctor_set(x_76, 4, x_34);
lean_ctor_set(x_76, 5, x_35);
lean_ctor_set(x_76, 6, x_36);
lean_ctor_set(x_76, 7, x_37);
lean_ctor_set(x_76, 8, x_38);
lean_ctor_set(x_76, 9, x_39);
lean_ctor_set(x_76, 10, x_40);
lean_ctor_set(x_76, 11, x_41);
lean_ctor_set(x_76, 12, x_42);
lean_ctor_set(x_76, 13, x_43);
lean_ctor_set(x_76, 14, x_44);
lean_ctor_set(x_76, 15, x_45);
lean_ctor_set(x_76, 16, x_46);
lean_ctor_set(x_76, 17, x_47);
lean_ctor_set(x_76, 18, x_48);
lean_ctor_set(x_76, 19, x_49);
lean_ctor_set(x_76, 20, x_50);
lean_ctor_set(x_76, 21, x_51);
lean_ctor_set(x_76, 22, x_52);
lean_ctor_set(x_76, 23, x_53);
lean_ctor_set(x_76, 24, x_54);
lean_ctor_set(x_76, 25, x_55);
lean_ctor_set(x_76, 26, x_56);
lean_ctor_set(x_76, 27, x_57);
lean_ctor_set(x_76, 28, x_58);
lean_ctor_set(x_76, 29, x_59);
lean_ctor_set(x_76, 30, x_60);
lean_ctor_set(x_76, 31, x_61);
lean_ctor_set(x_76, 32, x_62);
lean_ctor_set(x_76, 33, x_63);
lean_ctor_set(x_76, 34, x_64);
lean_ctor_set(x_76, 35, x_65);
lean_ctor_set(x_76, 36, x_67);
lean_ctor_set(x_76, 37, x_68);
lean_ctor_set(x_76, 38, x_69);
lean_ctor_set(x_76, 39, x_70);
lean_ctor_set(x_76, 40, x_71);
lean_ctor_set(x_76, 41, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*42, x_66);
x_77 = lean_array_fset(x_74, x_1, x_76);
lean_ctor_set(x_3, 0, x_77);
return x_3;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_3);
x_78 = lean_array_fget(x_4, x_1);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 2);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_78, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 4);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_78, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 6);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 7);
lean_inc(x_86);
x_87 = lean_ctor_get(x_78, 8);
lean_inc(x_87);
x_88 = lean_ctor_get(x_78, 9);
lean_inc(x_88);
x_89 = lean_ctor_get(x_78, 10);
lean_inc(x_89);
x_90 = lean_ctor_get(x_78, 11);
lean_inc(x_90);
x_91 = lean_ctor_get(x_78, 12);
lean_inc(x_91);
x_92 = lean_ctor_get(x_78, 13);
lean_inc(x_92);
x_93 = lean_ctor_get(x_78, 14);
lean_inc(x_93);
x_94 = lean_ctor_get(x_78, 15);
lean_inc(x_94);
x_95 = lean_ctor_get(x_78, 16);
lean_inc(x_95);
x_96 = lean_ctor_get(x_78, 17);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_78, 18);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_78, 19);
lean_inc(x_98);
x_99 = lean_ctor_get(x_78, 20);
lean_inc(x_99);
x_100 = lean_ctor_get(x_78, 21);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 22);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_78, 23);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_78, 24);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_78, 25);
lean_inc(x_104);
x_105 = lean_ctor_get(x_78, 26);
lean_inc(x_105);
x_106 = lean_ctor_get(x_78, 27);
lean_inc(x_106);
x_107 = lean_ctor_get(x_78, 28);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_78, 29);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_78, 30);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_78, 31);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_78, 32);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_78, 33);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_78, 34);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_78, 35);
lean_inc_ref(x_114);
x_115 = lean_ctor_get_uint8(x_78, sizeof(void*)*42);
x_116 = lean_ctor_get(x_78, 36);
lean_inc(x_116);
x_117 = lean_ctor_get(x_78, 37);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_78, 38);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_78, 39);
lean_inc(x_119);
x_120 = lean_ctor_get(x_78, 40);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_78, 41);
lean_inc_ref(x_121);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 lean_ctor_release(x_78, 5);
 lean_ctor_release(x_78, 6);
 lean_ctor_release(x_78, 7);
 lean_ctor_release(x_78, 8);
 lean_ctor_release(x_78, 9);
 lean_ctor_release(x_78, 10);
 lean_ctor_release(x_78, 11);
 lean_ctor_release(x_78, 12);
 lean_ctor_release(x_78, 13);
 lean_ctor_release(x_78, 14);
 lean_ctor_release(x_78, 15);
 lean_ctor_release(x_78, 16);
 lean_ctor_release(x_78, 17);
 lean_ctor_release(x_78, 18);
 lean_ctor_release(x_78, 19);
 lean_ctor_release(x_78, 20);
 lean_ctor_release(x_78, 21);
 lean_ctor_release(x_78, 22);
 lean_ctor_release(x_78, 23);
 lean_ctor_release(x_78, 24);
 lean_ctor_release(x_78, 25);
 lean_ctor_release(x_78, 26);
 lean_ctor_release(x_78, 27);
 lean_ctor_release(x_78, 28);
 lean_ctor_release(x_78, 29);
 lean_ctor_release(x_78, 30);
 lean_ctor_release(x_78, 31);
 lean_ctor_release(x_78, 32);
 lean_ctor_release(x_78, 33);
 lean_ctor_release(x_78, 34);
 lean_ctor_release(x_78, 35);
 lean_ctor_release(x_78, 36);
 lean_ctor_release(x_78, 37);
 lean_ctor_release(x_78, 38);
 lean_ctor_release(x_78, 39);
 lean_ctor_release(x_78, 40);
 lean_ctor_release(x_78, 41);
 x_122 = x_78;
} else {
 lean_dec_ref(x_78);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
x_124 = lean_array_fset(x_4, x_1, x_123);
x_125 = l_Lean_PersistentArray_push___redArg(x_121, x_2);
if (lean_is_scalar(x_122)) {
 x_126 = lean_alloc_ctor(0, 42, 1);
} else {
 x_126 = x_122;
}
lean_ctor_set(x_126, 0, x_79);
lean_ctor_set(x_126, 1, x_80);
lean_ctor_set(x_126, 2, x_81);
lean_ctor_set(x_126, 3, x_82);
lean_ctor_set(x_126, 4, x_83);
lean_ctor_set(x_126, 5, x_84);
lean_ctor_set(x_126, 6, x_85);
lean_ctor_set(x_126, 7, x_86);
lean_ctor_set(x_126, 8, x_87);
lean_ctor_set(x_126, 9, x_88);
lean_ctor_set(x_126, 10, x_89);
lean_ctor_set(x_126, 11, x_90);
lean_ctor_set(x_126, 12, x_91);
lean_ctor_set(x_126, 13, x_92);
lean_ctor_set(x_126, 14, x_93);
lean_ctor_set(x_126, 15, x_94);
lean_ctor_set(x_126, 16, x_95);
lean_ctor_set(x_126, 17, x_96);
lean_ctor_set(x_126, 18, x_97);
lean_ctor_set(x_126, 19, x_98);
lean_ctor_set(x_126, 20, x_99);
lean_ctor_set(x_126, 21, x_100);
lean_ctor_set(x_126, 22, x_101);
lean_ctor_set(x_126, 23, x_102);
lean_ctor_set(x_126, 24, x_103);
lean_ctor_set(x_126, 25, x_104);
lean_ctor_set(x_126, 26, x_105);
lean_ctor_set(x_126, 27, x_106);
lean_ctor_set(x_126, 28, x_107);
lean_ctor_set(x_126, 29, x_108);
lean_ctor_set(x_126, 30, x_109);
lean_ctor_set(x_126, 31, x_110);
lean_ctor_set(x_126, 32, x_111);
lean_ctor_set(x_126, 33, x_112);
lean_ctor_set(x_126, 34, x_113);
lean_ctor_set(x_126, 35, x_114);
lean_ctor_set(x_126, 36, x_116);
lean_ctor_set(x_126, 37, x_117);
lean_ctor_set(x_126, 38, x_118);
lean_ctor_set(x_126, 39, x_119);
lean_ctor_set(x_126, 40, x_120);
lean_ctor_set(x_126, 41, x_125);
lean_ctor_set_uint8(x_126, sizeof(void*)*42, x_115);
x_127 = lean_array_fset(x_124, x_1, x_126);
x_128 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_5);
lean_ctor_set(x_128, 2, x_6);
lean_ctor_set(x_128, 3, x_7);
lean_ctor_set(x_128, 4, x_8);
lean_ctor_set(x_128, 5, x_9);
lean_ctor_set(x_128, 6, x_10);
lean_ctor_set(x_128, 7, x_11);
return x_128;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ignored", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2;
x_34 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_33, x_10);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Lean_MessageData_ofExpr(x_38);
x_40 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_33, x_39, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_dec_ref(x_40);
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = lean_box(0);
goto block_32;
}
else
{
lean_dec(x_2);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
block_32:
{
lean_object* x_24; 
x_24 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_1, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(x_26, 0, x_13);
lean_closure_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_28 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_27, x_26, x_14);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_13);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 2);
x_17 = lean_ctor_get(x_10, 3);
x_18 = lean_ctor_get(x_10, 4);
x_19 = lean_ctor_get(x_10, 5);
x_20 = lean_ctor_get(x_10, 6);
x_21 = lean_ctor_get(x_10, 7);
x_22 = lean_ctor_get(x_10, 8);
x_23 = lean_ctor_get(x_10, 9);
x_24 = lean_ctor_get(x_10, 10);
x_25 = lean_ctor_get(x_10, 11);
x_26 = lean_ctor_get(x_10, 12);
x_27 = lean_ctor_get(x_10, 13);
x_28 = lean_nat_dec_eq(x_17, x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_17, x_30);
lean_dec(x_17);
lean_ctor_set(x_10, 3, x_31);
x_32 = l_Lean_Grind_Linarith_Poly_findVarToSubst(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_ctor_get(x_37, 0);
x_41 = l_Lean_Grind_Linarith_Poly_coeff(x_40, x_39);
lean_inc_ref(x_1);
x_42 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_41, x_39, x_37, x_38, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_39);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; 
lean_dec_ref(x_1);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_1 = x_44;
goto _start;
}
else
{
lean_object* x_46; 
lean_dec(x_43);
x_46 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_46);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_46);
if (x_52 == 0)
{
return x_46;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
else
{
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_42;
}
}
else
{
lean_object* x_55; 
lean_dec(x_34);
lean_dec_ref(x_10);
lean_dec(x_2);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_32, 0, x_55);
return x_32;
}
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_32, 0);
lean_inc(x_56);
lean_dec(x_32);
if (lean_obj_tag(x_56) == 1)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_ctor_get(x_59, 0);
x_63 = l_Lean_Grind_Linarith_Poly_coeff(x_62, x_61);
lean_inc_ref(x_1);
x_64 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_63, x_61, x_59, x_60, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_61);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
if (lean_obj_tag(x_65) == 1)
{
lean_object* x_66; 
lean_dec_ref(x_1);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_1 = x_66;
goto _start;
}
else
{
lean_object* x_68; 
lean_dec(x_65);
x_68 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_69 = x_68;
} else {
 lean_dec_ref(x_68);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_73 = x_68;
} else {
 lean_dec_ref(x_68);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
return x_74;
}
}
}
else
{
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_64;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_56);
lean_dec_ref(x_10);
lean_dec(x_2);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_1);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
x_77 = !lean_is_exclusive(x_32);
if (x_77 == 0)
{
return x_32;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_32, 0);
lean_inc(x_78);
lean_dec(x_32);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; 
lean_free_object(x_10);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_2);
lean_dec_ref(x_1);
x_80 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_19);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; uint8_t x_97; 
x_81 = lean_ctor_get(x_10, 0);
x_82 = lean_ctor_get(x_10, 1);
x_83 = lean_ctor_get(x_10, 2);
x_84 = lean_ctor_get(x_10, 3);
x_85 = lean_ctor_get(x_10, 4);
x_86 = lean_ctor_get(x_10, 5);
x_87 = lean_ctor_get(x_10, 6);
x_88 = lean_ctor_get(x_10, 7);
x_89 = lean_ctor_get(x_10, 8);
x_90 = lean_ctor_get(x_10, 9);
x_91 = lean_ctor_get(x_10, 10);
x_92 = lean_ctor_get(x_10, 11);
x_93 = lean_ctor_get_uint8(x_10, sizeof(void*)*14);
x_94 = lean_ctor_get(x_10, 12);
x_95 = lean_ctor_get_uint8(x_10, sizeof(void*)*14 + 1);
x_96 = lean_ctor_get(x_10, 13);
lean_inc(x_96);
lean_inc(x_94);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_10);
x_97 = lean_nat_dec_eq(x_84, x_85);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_1, 0);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_add(x_84, x_99);
lean_dec(x_84);
x_101 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_101, 0, x_81);
lean_ctor_set(x_101, 1, x_82);
lean_ctor_set(x_101, 2, x_83);
lean_ctor_set(x_101, 3, x_100);
lean_ctor_set(x_101, 4, x_85);
lean_ctor_set(x_101, 5, x_86);
lean_ctor_set(x_101, 6, x_87);
lean_ctor_set(x_101, 7, x_88);
lean_ctor_set(x_101, 8, x_89);
lean_ctor_set(x_101, 9, x_90);
lean_ctor_set(x_101, 10, x_91);
lean_ctor_set(x_101, 11, x_92);
lean_ctor_set(x_101, 12, x_94);
lean_ctor_set(x_101, 13, x_96);
lean_ctor_set_uint8(x_101, sizeof(void*)*14, x_93);
lean_ctor_set_uint8(x_101, sizeof(void*)*14 + 1, x_95);
x_102 = l_Lean_Grind_Linarith_Poly_findVarToSubst(x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_101, x_11);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
if (lean_obj_tag(x_103) == 1)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_104);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec_ref(x_103);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
lean_dec(x_105);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_ctor_get(x_107, 0);
x_111 = l_Lean_Grind_Linarith_Poly_coeff(x_110, x_109);
lean_inc_ref(x_1);
x_112 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_111, x_109, x_107, x_108, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_101, x_11);
lean_dec(x_109);
lean_dec(x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
if (lean_obj_tag(x_113) == 1)
{
lean_object* x_114; 
lean_dec_ref(x_1);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_1 = x_114;
x_10 = x_101;
goto _start;
}
else
{
lean_object* x_116; 
lean_dec(x_113);
x_116 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_101, x_11);
lean_dec_ref(x_101);
lean_dec_ref(x_1);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_117 = x_116;
} else {
 lean_dec_ref(x_116);
 x_117 = lean_box(0);
}
x_118 = lean_box(0);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 1, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_116, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_121 = x_116;
} else {
 lean_dec_ref(x_116);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
}
else
{
lean_dec_ref(x_101);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_112;
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_103);
lean_dec_ref(x_101);
lean_dec(x_2);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_1);
if (lean_is_scalar(x_104)) {
 x_124 = lean_alloc_ctor(0, 1, 0);
} else {
 x_124 = x_104;
}
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec_ref(x_101);
lean_dec(x_2);
lean_dec_ref(x_1);
x_125 = lean_ctor_get(x_102, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_126 = x_102;
} else {
 lean_dec_ref(x_102);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
return x_127;
}
}
else
{
lean_object* x_128; 
lean_dec_ref(x_96);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec_ref(x_81);
lean_dec(x_2);
lean_dec_ref(x_1);
x_128 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(x_86);
return x_128;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
x_21 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(x_1, x_18, x_15, x_17);
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
x_32 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(x_1, x_29, x_26, x_28);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(x_1, x_6, x_11, x_8);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_nat_sub(x_4, x_9);
x_14 = lean_array_get_size(x_7);
x_15 = lean_nat_dec_lt(x_13, x_14);
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
x_28 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(x_1, x_21, x_27, x_24);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 3);
x_10 = lean_ctor_get(x_5, 4);
x_11 = lean_ctor_get(x_5, 5);
x_12 = lean_ctor_get(x_5, 6);
x_13 = lean_ctor_get(x_5, 7);
x_14 = lean_array_get_size(x_6);
x_15 = lean_nat_dec_lt(x_1, x_14);
if (x_15 == 0)
{
lean_dec_ref(x_2);
return x_5;
}
else
{
uint8_t x_16; 
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_5, 7);
lean_dec(x_17);
x_18 = lean_ctor_get(x_5, 6);
lean_dec(x_18);
x_19 = lean_ctor_get(x_5, 5);
lean_dec(x_19);
x_20 = lean_ctor_get(x_5, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_5, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_5, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_5, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = lean_array_fget(x_6, x_1);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 34);
x_28 = lean_box(0);
x_29 = lean_array_fset(x_6, x_1, x_28);
x_30 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(x_2, x_3, x_27, x_4);
lean_ctor_set(x_25, 34, x_30);
x_31 = lean_array_fset(x_29, x_1, x_25);
lean_ctor_set(x_5, 0, x_31);
return x_5;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
x_34 = lean_ctor_get(x_25, 2);
x_35 = lean_ctor_get(x_25, 3);
x_36 = lean_ctor_get(x_25, 4);
x_37 = lean_ctor_get(x_25, 5);
x_38 = lean_ctor_get(x_25, 6);
x_39 = lean_ctor_get(x_25, 7);
x_40 = lean_ctor_get(x_25, 8);
x_41 = lean_ctor_get(x_25, 9);
x_42 = lean_ctor_get(x_25, 10);
x_43 = lean_ctor_get(x_25, 11);
x_44 = lean_ctor_get(x_25, 12);
x_45 = lean_ctor_get(x_25, 13);
x_46 = lean_ctor_get(x_25, 14);
x_47 = lean_ctor_get(x_25, 15);
x_48 = lean_ctor_get(x_25, 16);
x_49 = lean_ctor_get(x_25, 17);
x_50 = lean_ctor_get(x_25, 18);
x_51 = lean_ctor_get(x_25, 19);
x_52 = lean_ctor_get(x_25, 20);
x_53 = lean_ctor_get(x_25, 21);
x_54 = lean_ctor_get(x_25, 22);
x_55 = lean_ctor_get(x_25, 23);
x_56 = lean_ctor_get(x_25, 24);
x_57 = lean_ctor_get(x_25, 25);
x_58 = lean_ctor_get(x_25, 26);
x_59 = lean_ctor_get(x_25, 27);
x_60 = lean_ctor_get(x_25, 28);
x_61 = lean_ctor_get(x_25, 29);
x_62 = lean_ctor_get(x_25, 30);
x_63 = lean_ctor_get(x_25, 31);
x_64 = lean_ctor_get(x_25, 32);
x_65 = lean_ctor_get(x_25, 33);
x_66 = lean_ctor_get(x_25, 34);
x_67 = lean_ctor_get(x_25, 35);
x_68 = lean_ctor_get_uint8(x_25, sizeof(void*)*42);
x_69 = lean_ctor_get(x_25, 36);
x_70 = lean_ctor_get(x_25, 37);
x_71 = lean_ctor_get(x_25, 38);
x_72 = lean_ctor_get(x_25, 39);
x_73 = lean_ctor_get(x_25, 40);
x_74 = lean_ctor_get(x_25, 41);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_75 = lean_box(0);
x_76 = lean_array_fset(x_6, x_1, x_75);
x_77 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(x_2, x_3, x_66, x_4);
x_78 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_78, 0, x_32);
lean_ctor_set(x_78, 1, x_33);
lean_ctor_set(x_78, 2, x_34);
lean_ctor_set(x_78, 3, x_35);
lean_ctor_set(x_78, 4, x_36);
lean_ctor_set(x_78, 5, x_37);
lean_ctor_set(x_78, 6, x_38);
lean_ctor_set(x_78, 7, x_39);
lean_ctor_set(x_78, 8, x_40);
lean_ctor_set(x_78, 9, x_41);
lean_ctor_set(x_78, 10, x_42);
lean_ctor_set(x_78, 11, x_43);
lean_ctor_set(x_78, 12, x_44);
lean_ctor_set(x_78, 13, x_45);
lean_ctor_set(x_78, 14, x_46);
lean_ctor_set(x_78, 15, x_47);
lean_ctor_set(x_78, 16, x_48);
lean_ctor_set(x_78, 17, x_49);
lean_ctor_set(x_78, 18, x_50);
lean_ctor_set(x_78, 19, x_51);
lean_ctor_set(x_78, 20, x_52);
lean_ctor_set(x_78, 21, x_53);
lean_ctor_set(x_78, 22, x_54);
lean_ctor_set(x_78, 23, x_55);
lean_ctor_set(x_78, 24, x_56);
lean_ctor_set(x_78, 25, x_57);
lean_ctor_set(x_78, 26, x_58);
lean_ctor_set(x_78, 27, x_59);
lean_ctor_set(x_78, 28, x_60);
lean_ctor_set(x_78, 29, x_61);
lean_ctor_set(x_78, 30, x_62);
lean_ctor_set(x_78, 31, x_63);
lean_ctor_set(x_78, 32, x_64);
lean_ctor_set(x_78, 33, x_65);
lean_ctor_set(x_78, 34, x_77);
lean_ctor_set(x_78, 35, x_67);
lean_ctor_set(x_78, 36, x_69);
lean_ctor_set(x_78, 37, x_70);
lean_ctor_set(x_78, 38, x_71);
lean_ctor_set(x_78, 39, x_72);
lean_ctor_set(x_78, 40, x_73);
lean_ctor_set(x_78, 41, x_74);
lean_ctor_set_uint8(x_78, sizeof(void*)*42, x_68);
x_79 = lean_array_fset(x_76, x_1, x_78);
lean_ctor_set(x_5, 0, x_79);
return x_5;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_5);
x_80 = lean_array_fget(x_6, x_1);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 2);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_80, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 4);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_80, 5);
lean_inc(x_86);
x_87 = lean_ctor_get(x_80, 6);
lean_inc(x_87);
x_88 = lean_ctor_get(x_80, 7);
lean_inc(x_88);
x_89 = lean_ctor_get(x_80, 8);
lean_inc(x_89);
x_90 = lean_ctor_get(x_80, 9);
lean_inc(x_90);
x_91 = lean_ctor_get(x_80, 10);
lean_inc(x_91);
x_92 = lean_ctor_get(x_80, 11);
lean_inc(x_92);
x_93 = lean_ctor_get(x_80, 12);
lean_inc(x_93);
x_94 = lean_ctor_get(x_80, 13);
lean_inc(x_94);
x_95 = lean_ctor_get(x_80, 14);
lean_inc(x_95);
x_96 = lean_ctor_get(x_80, 15);
lean_inc(x_96);
x_97 = lean_ctor_get(x_80, 16);
lean_inc(x_97);
x_98 = lean_ctor_get(x_80, 17);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_80, 18);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_80, 19);
lean_inc(x_100);
x_101 = lean_ctor_get(x_80, 20);
lean_inc(x_101);
x_102 = lean_ctor_get(x_80, 21);
lean_inc(x_102);
x_103 = lean_ctor_get(x_80, 22);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_80, 23);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_80, 24);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_80, 25);
lean_inc(x_106);
x_107 = lean_ctor_get(x_80, 26);
lean_inc(x_107);
x_108 = lean_ctor_get(x_80, 27);
lean_inc(x_108);
x_109 = lean_ctor_get(x_80, 28);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_80, 29);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_80, 30);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_80, 31);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_80, 32);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_80, 33);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_80, 34);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_80, 35);
lean_inc_ref(x_116);
x_117 = lean_ctor_get_uint8(x_80, sizeof(void*)*42);
x_118 = lean_ctor_get(x_80, 36);
lean_inc(x_118);
x_119 = lean_ctor_get(x_80, 37);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_80, 38);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_80, 39);
lean_inc(x_121);
x_122 = lean_ctor_get(x_80, 40);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_80, 41);
lean_inc_ref(x_123);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 lean_ctor_release(x_80, 5);
 lean_ctor_release(x_80, 6);
 lean_ctor_release(x_80, 7);
 lean_ctor_release(x_80, 8);
 lean_ctor_release(x_80, 9);
 lean_ctor_release(x_80, 10);
 lean_ctor_release(x_80, 11);
 lean_ctor_release(x_80, 12);
 lean_ctor_release(x_80, 13);
 lean_ctor_release(x_80, 14);
 lean_ctor_release(x_80, 15);
 lean_ctor_release(x_80, 16);
 lean_ctor_release(x_80, 17);
 lean_ctor_release(x_80, 18);
 lean_ctor_release(x_80, 19);
 lean_ctor_release(x_80, 20);
 lean_ctor_release(x_80, 21);
 lean_ctor_release(x_80, 22);
 lean_ctor_release(x_80, 23);
 lean_ctor_release(x_80, 24);
 lean_ctor_release(x_80, 25);
 lean_ctor_release(x_80, 26);
 lean_ctor_release(x_80, 27);
 lean_ctor_release(x_80, 28);
 lean_ctor_release(x_80, 29);
 lean_ctor_release(x_80, 30);
 lean_ctor_release(x_80, 31);
 lean_ctor_release(x_80, 32);
 lean_ctor_release(x_80, 33);
 lean_ctor_release(x_80, 34);
 lean_ctor_release(x_80, 35);
 lean_ctor_release(x_80, 36);
 lean_ctor_release(x_80, 37);
 lean_ctor_release(x_80, 38);
 lean_ctor_release(x_80, 39);
 lean_ctor_release(x_80, 40);
 lean_ctor_release(x_80, 41);
 x_124 = x_80;
} else {
 lean_dec_ref(x_80);
 x_124 = lean_box(0);
}
x_125 = lean_box(0);
x_126 = lean_array_fset(x_6, x_1, x_125);
x_127 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(x_2, x_3, x_115, x_4);
if (lean_is_scalar(x_124)) {
 x_128 = lean_alloc_ctor(0, 42, 1);
} else {
 x_128 = x_124;
}
lean_ctor_set(x_128, 0, x_81);
lean_ctor_set(x_128, 1, x_82);
lean_ctor_set(x_128, 2, x_83);
lean_ctor_set(x_128, 3, x_84);
lean_ctor_set(x_128, 4, x_85);
lean_ctor_set(x_128, 5, x_86);
lean_ctor_set(x_128, 6, x_87);
lean_ctor_set(x_128, 7, x_88);
lean_ctor_set(x_128, 8, x_89);
lean_ctor_set(x_128, 9, x_90);
lean_ctor_set(x_128, 10, x_91);
lean_ctor_set(x_128, 11, x_92);
lean_ctor_set(x_128, 12, x_93);
lean_ctor_set(x_128, 13, x_94);
lean_ctor_set(x_128, 14, x_95);
lean_ctor_set(x_128, 15, x_96);
lean_ctor_set(x_128, 16, x_97);
lean_ctor_set(x_128, 17, x_98);
lean_ctor_set(x_128, 18, x_99);
lean_ctor_set(x_128, 19, x_100);
lean_ctor_set(x_128, 20, x_101);
lean_ctor_set(x_128, 21, x_102);
lean_ctor_set(x_128, 22, x_103);
lean_ctor_set(x_128, 23, x_104);
lean_ctor_set(x_128, 24, x_105);
lean_ctor_set(x_128, 25, x_106);
lean_ctor_set(x_128, 26, x_107);
lean_ctor_set(x_128, 27, x_108);
lean_ctor_set(x_128, 28, x_109);
lean_ctor_set(x_128, 29, x_110);
lean_ctor_set(x_128, 30, x_111);
lean_ctor_set(x_128, 31, x_112);
lean_ctor_set(x_128, 32, x_113);
lean_ctor_set(x_128, 33, x_114);
lean_ctor_set(x_128, 34, x_127);
lean_ctor_set(x_128, 35, x_116);
lean_ctor_set(x_128, 36, x_118);
lean_ctor_set(x_128, 37, x_119);
lean_ctor_set(x_128, 38, x_120);
lean_ctor_set(x_128, 39, x_121);
lean_ctor_set(x_128, 40, x_122);
lean_ctor_set(x_128, 41, x_123);
lean_ctor_set_uint8(x_128, sizeof(void*)*42, x_117);
x_129 = lean_array_fset(x_126, x_1, x_128);
x_130 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_7);
lean_ctor_set(x_130, 2, x_8);
lean_ctor_set(x_130, 3, x_9);
lean_ctor_set(x_130, 4, x_10);
lean_ctor_set(x_130, 5, x_11);
lean_ctor_set(x_130, 6, x_12);
lean_ctor_set(x_130, 7, x_13);
return x_130;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_143; 
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0;
x_29 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_28, x_10);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0;
x_143 = lean_unbox(x_30);
lean_dec(x_30);
if (x_143 == 0)
{
x_71 = x_2;
x_72 = x_3;
x_73 = x_4;
x_74 = x_5;
x_75 = x_6;
x_76 = x_7;
x_77 = x_8;
x_78 = x_9;
x_79 = x_10;
x_80 = x_11;
x_81 = lean_box(0);
goto block_142;
}
else
{
lean_object* x_144; 
x_144 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = l_Lean_MessageData_ofExpr(x_145);
x_147 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_28, x_146, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_147) == 0)
{
lean_dec_ref(x_147);
x_71 = x_2;
x_72 = x_3;
x_73 = x_4;
x_74 = x_5;
x_75 = x_6;
x_76 = x_7;
x_77 = x_8;
x_78 = x_9;
x_79 = x_10;
x_80 = x_11;
x_81 = lean_box(0);
goto block_142;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_147;
}
}
else
{
uint8_t x_148; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_148 = !lean_is_exclusive(x_144);
if (x_148 == 0)
{
return x_144;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_144, 0);
lean_inc(x_149);
lean_dec(x_144);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_13);
x_26 = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(x_25, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
return x_26;
}
block_70:
{
lean_object* x_48; 
lean_inc(x_37);
x_48 = l_Lean_Grind_Linarith_Poly_updateOccs(x_35, x_37, x_38, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_48);
lean_inc(x_37);
x_49 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 5, 4);
lean_closure_set(x_49, 0, x_37);
lean_closure_set(x_49, 1, x_32);
lean_closure_set(x_49, 2, x_31);
lean_closure_set(x_49, 3, x_33);
x_50 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_51 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_50, x_49, x_38);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
lean_dec_ref(x_51);
x_52 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(x_34, x_37, x_38, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_46);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = 0;
x_56 = lean_unbox(x_54);
lean_dec(x_54);
x_57 = l_Lean_instBEqLBool_beq(x_56, x_55);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
x_58 = lean_box(0);
lean_ctor_set(x_52, 0, x_58);
return x_52;
}
else
{
lean_object* x_59; 
lean_free_object(x_52);
x_59 = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(x_36, x_37, x_38);
lean_dec(x_38);
return x_59;
}
}
else
{
lean_object* x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_52, 0);
lean_inc(x_60);
lean_dec(x_52);
x_61 = 0;
x_62 = lean_unbox(x_60);
lean_dec(x_60);
x_63 = l_Lean_instBEqLBool_beq(x_62, x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(x_36, x_37, x_38);
lean_dec(x_38);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
return x_52;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_52, 0);
lean_inc(x_68);
lean_dec(x_52);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
return x_51;
}
}
else
{
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
return x_48;
}
}
block_142:
{
lean_object* x_82; 
lean_inc_ref(x_79);
lean_inc(x_71);
x_82 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(x_1, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78, x_79, x_80);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_82, 0);
if (lean_obj_tag(x_84) == 1)
{
lean_object* x_85; lean_object* x_86; 
lean_free_object(x_82);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_ctor_get(x_85, 0);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2;
x_88 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_87, x_79);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
x_13 = x_85;
x_14 = x_71;
x_15 = x_72;
x_16 = x_73;
x_17 = x_74;
x_18 = x_75;
x_19 = x_76;
x_20 = x_77;
x_21 = x_78;
x_22 = x_79;
x_23 = x_80;
x_24 = lean_box(0);
goto block_27;
}
else
{
lean_object* x_91; 
x_91 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_85, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78, x_79, x_80);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = l_Lean_MessageData_ofExpr(x_92);
x_94 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_87, x_93, x_77, x_78, x_79, x_80);
if (lean_obj_tag(x_94) == 0)
{
lean_dec_ref(x_94);
x_13 = x_85;
x_14 = x_71;
x_15 = x_72;
x_16 = x_73;
x_17 = x_74;
x_18 = x_75;
x_19 = x_76;
x_20 = x_77;
x_21 = x_78;
x_22 = x_79;
x_23 = x_80;
x_24 = lean_box(0);
goto block_27;
}
else
{
lean_dec(x_85);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec(x_85);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
x_95 = !lean_is_exclusive(x_91);
if (x_95 == 0)
{
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_inc_ref(x_86);
x_98 = lean_ctor_get(x_86, 1);
lean_inc(x_98);
x_99 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4;
x_100 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_99, x_79);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_inc(x_98);
lean_inc(x_85);
x_32 = x_85;
x_33 = x_98;
x_34 = x_85;
x_35 = x_86;
x_36 = x_98;
x_37 = x_71;
x_38 = x_72;
x_39 = x_73;
x_40 = x_74;
x_41 = x_75;
x_42 = x_76;
x_43 = x_77;
x_44 = x_78;
x_45 = x_79;
x_46 = x_80;
x_47 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_103; 
x_103 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_85, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78, x_79, x_80);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = l_Lean_MessageData_ofExpr(x_104);
x_106 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_99, x_105, x_77, x_78, x_79, x_80);
if (lean_obj_tag(x_106) == 0)
{
lean_dec_ref(x_106);
lean_inc(x_98);
lean_inc(x_85);
x_32 = x_85;
x_33 = x_98;
x_34 = x_85;
x_35 = x_86;
x_36 = x_98;
x_37 = x_71;
x_38 = x_72;
x_39 = x_73;
x_40 = x_74;
x_41 = x_75;
x_42 = x_76;
x_43 = x_77;
x_44 = x_78;
x_45 = x_79;
x_46 = x_80;
x_47 = lean_box(0);
goto block_70;
}
else
{
lean_dec(x_98);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_106;
}
}
else
{
uint8_t x_107; 
lean_dec(x_98);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
x_107 = !lean_is_exclusive(x_103);
if (x_107 == 0)
{
return x_103;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_103, 0);
lean_inc(x_108);
lean_dec(x_103);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
}
}
else
{
lean_object* x_110; 
lean_dec(x_84);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
x_110 = lean_box(0);
lean_ctor_set(x_82, 0, x_110);
return x_82;
}
}
else
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_82, 0);
lean_inc(x_111);
lean_dec(x_82);
if (lean_obj_tag(x_111) == 1)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = lean_ctor_get(x_112, 0);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2;
x_115 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_114, x_79);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
x_13 = x_112;
x_14 = x_71;
x_15 = x_72;
x_16 = x_73;
x_17 = x_74;
x_18 = x_75;
x_19 = x_76;
x_20 = x_77;
x_21 = x_78;
x_22 = x_79;
x_23 = x_80;
x_24 = lean_box(0);
goto block_27;
}
else
{
lean_object* x_118; 
x_118 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_112, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78, x_79, x_80);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_120 = l_Lean_MessageData_ofExpr(x_119);
x_121 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_114, x_120, x_77, x_78, x_79, x_80);
if (lean_obj_tag(x_121) == 0)
{
lean_dec_ref(x_121);
x_13 = x_112;
x_14 = x_71;
x_15 = x_72;
x_16 = x_73;
x_17 = x_74;
x_18 = x_75;
x_19 = x_76;
x_20 = x_77;
x_21 = x_78;
x_22 = x_79;
x_23 = x_80;
x_24 = lean_box(0);
goto block_27;
}
else
{
lean_dec(x_112);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_112);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
x_122 = lean_ctor_get(x_118, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_123 = x_118;
} else {
 lean_dec_ref(x_118);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 1, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_122);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_inc_ref(x_113);
x_125 = lean_ctor_get(x_113, 1);
lean_inc(x_125);
x_126 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4;
x_127 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_126, x_79);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec_ref(x_127);
x_129 = lean_unbox(x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_inc(x_125);
lean_inc(x_112);
x_32 = x_112;
x_33 = x_125;
x_34 = x_112;
x_35 = x_113;
x_36 = x_125;
x_37 = x_71;
x_38 = x_72;
x_39 = x_73;
x_40 = x_74;
x_41 = x_75;
x_42 = x_76;
x_43 = x_77;
x_44 = x_78;
x_45 = x_79;
x_46 = x_80;
x_47 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_130; 
x_130 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(x_112, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78, x_79, x_80);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = l_Lean_MessageData_ofExpr(x_131);
x_133 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_126, x_132, x_77, x_78, x_79, x_80);
if (lean_obj_tag(x_133) == 0)
{
lean_dec_ref(x_133);
lean_inc(x_125);
lean_inc(x_112);
x_32 = x_112;
x_33 = x_125;
x_34 = x_112;
x_35 = x_113;
x_36 = x_125;
x_37 = x_71;
x_38 = x_72;
x_39 = x_73;
x_40 = x_74;
x_41 = x_75;
x_42 = x_76;
x_43 = x_77;
x_44 = x_78;
x_45 = x_79;
x_46 = x_80;
x_47 = lean_box(0);
goto block_70;
}
else
{
lean_dec(x_125);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_125);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
x_134 = lean_ctor_get(x_130, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_135 = x_130;
} else {
 lean_dec_ref(x_130);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_134);
return x_136;
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_111);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
x_139 = !lean_is_exclusive(x_82);
if (x_139 == 0)
{
return x_82;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_82, 0);
lean_inc(x_140);
lean_dec(x_82);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
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
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(x_3, x_1, x_2, x_4, x_5, x_11, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
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
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(x_3, x_1, x_2, x_4, x_5, x_11, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(x_1, x_2, x_3, x_8, x_7, x_10, x_11, x_9);
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
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(x_1, x_2, x_3, x_17, x_16, x_19, x_20, x_18);
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
x_32 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_28, x_27, x_30, x_31, x_29);
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
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_37, x_36, x_39, x_40, x_38);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
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
x_14 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_13, x_11);
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
x_22 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_21, x_20);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_7 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(x_1, x_2, x_4, x_5, x_4);
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
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(x_1, x_2, x_10, x_6, x_12, x_13, x_11);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0;
x_4 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3;
x_2 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__4;
x_5 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(x_1, x_3, x_2, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(x_1, x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_1, x_13);
if (x_14 == 0)
{
lean_dec_ref(x_3);
return x_4;
}
else
{
uint8_t x_15; 
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_4, 7);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 6);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 5);
lean_dec(x_18);
x_19 = lean_ctor_get(x_4, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_fget(x_5, x_1);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 34);
x_27 = lean_box(0);
x_28 = lean_array_fset(x_5, x_1, x_27);
x_29 = l_Lean_PersistentArray_set___redArg(x_26, x_2, x_3);
lean_ctor_set(x_24, 34, x_29);
x_30 = lean_array_fset(x_28, x_1, x_24);
lean_ctor_set(x_4, 0, x_30);
return x_4;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
x_33 = lean_ctor_get(x_24, 2);
x_34 = lean_ctor_get(x_24, 3);
x_35 = lean_ctor_get(x_24, 4);
x_36 = lean_ctor_get(x_24, 5);
x_37 = lean_ctor_get(x_24, 6);
x_38 = lean_ctor_get(x_24, 7);
x_39 = lean_ctor_get(x_24, 8);
x_40 = lean_ctor_get(x_24, 9);
x_41 = lean_ctor_get(x_24, 10);
x_42 = lean_ctor_get(x_24, 11);
x_43 = lean_ctor_get(x_24, 12);
x_44 = lean_ctor_get(x_24, 13);
x_45 = lean_ctor_get(x_24, 14);
x_46 = lean_ctor_get(x_24, 15);
x_47 = lean_ctor_get(x_24, 16);
x_48 = lean_ctor_get(x_24, 17);
x_49 = lean_ctor_get(x_24, 18);
x_50 = lean_ctor_get(x_24, 19);
x_51 = lean_ctor_get(x_24, 20);
x_52 = lean_ctor_get(x_24, 21);
x_53 = lean_ctor_get(x_24, 22);
x_54 = lean_ctor_get(x_24, 23);
x_55 = lean_ctor_get(x_24, 24);
x_56 = lean_ctor_get(x_24, 25);
x_57 = lean_ctor_get(x_24, 26);
x_58 = lean_ctor_get(x_24, 27);
x_59 = lean_ctor_get(x_24, 28);
x_60 = lean_ctor_get(x_24, 29);
x_61 = lean_ctor_get(x_24, 30);
x_62 = lean_ctor_get(x_24, 31);
x_63 = lean_ctor_get(x_24, 32);
x_64 = lean_ctor_get(x_24, 33);
x_65 = lean_ctor_get(x_24, 34);
x_66 = lean_ctor_get(x_24, 35);
x_67 = lean_ctor_get_uint8(x_24, sizeof(void*)*42);
x_68 = lean_ctor_get(x_24, 36);
x_69 = lean_ctor_get(x_24, 37);
x_70 = lean_ctor_get(x_24, 38);
x_71 = lean_ctor_get(x_24, 39);
x_72 = lean_ctor_get(x_24, 40);
x_73 = lean_ctor_get(x_24, 41);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_74 = lean_box(0);
x_75 = lean_array_fset(x_5, x_1, x_74);
x_76 = l_Lean_PersistentArray_set___redArg(x_65, x_2, x_3);
x_77 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_77, 0, x_31);
lean_ctor_set(x_77, 1, x_32);
lean_ctor_set(x_77, 2, x_33);
lean_ctor_set(x_77, 3, x_34);
lean_ctor_set(x_77, 4, x_35);
lean_ctor_set(x_77, 5, x_36);
lean_ctor_set(x_77, 6, x_37);
lean_ctor_set(x_77, 7, x_38);
lean_ctor_set(x_77, 8, x_39);
lean_ctor_set(x_77, 9, x_40);
lean_ctor_set(x_77, 10, x_41);
lean_ctor_set(x_77, 11, x_42);
lean_ctor_set(x_77, 12, x_43);
lean_ctor_set(x_77, 13, x_44);
lean_ctor_set(x_77, 14, x_45);
lean_ctor_set(x_77, 15, x_46);
lean_ctor_set(x_77, 16, x_47);
lean_ctor_set(x_77, 17, x_48);
lean_ctor_set(x_77, 18, x_49);
lean_ctor_set(x_77, 19, x_50);
lean_ctor_set(x_77, 20, x_51);
lean_ctor_set(x_77, 21, x_52);
lean_ctor_set(x_77, 22, x_53);
lean_ctor_set(x_77, 23, x_54);
lean_ctor_set(x_77, 24, x_55);
lean_ctor_set(x_77, 25, x_56);
lean_ctor_set(x_77, 26, x_57);
lean_ctor_set(x_77, 27, x_58);
lean_ctor_set(x_77, 28, x_59);
lean_ctor_set(x_77, 29, x_60);
lean_ctor_set(x_77, 30, x_61);
lean_ctor_set(x_77, 31, x_62);
lean_ctor_set(x_77, 32, x_63);
lean_ctor_set(x_77, 33, x_64);
lean_ctor_set(x_77, 34, x_76);
lean_ctor_set(x_77, 35, x_66);
lean_ctor_set(x_77, 36, x_68);
lean_ctor_set(x_77, 37, x_69);
lean_ctor_set(x_77, 38, x_70);
lean_ctor_set(x_77, 39, x_71);
lean_ctor_set(x_77, 40, x_72);
lean_ctor_set(x_77, 41, x_73);
lean_ctor_set_uint8(x_77, sizeof(void*)*42, x_67);
x_78 = lean_array_fset(x_75, x_1, x_77);
lean_ctor_set(x_4, 0, x_78);
return x_4;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_4);
x_79 = lean_array_fget(x_5, x_1);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 2);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_79, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_79, 4);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_79, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 6);
lean_inc(x_86);
x_87 = lean_ctor_get(x_79, 7);
lean_inc(x_87);
x_88 = lean_ctor_get(x_79, 8);
lean_inc(x_88);
x_89 = lean_ctor_get(x_79, 9);
lean_inc(x_89);
x_90 = lean_ctor_get(x_79, 10);
lean_inc(x_90);
x_91 = lean_ctor_get(x_79, 11);
lean_inc(x_91);
x_92 = lean_ctor_get(x_79, 12);
lean_inc(x_92);
x_93 = lean_ctor_get(x_79, 13);
lean_inc(x_93);
x_94 = lean_ctor_get(x_79, 14);
lean_inc(x_94);
x_95 = lean_ctor_get(x_79, 15);
lean_inc(x_95);
x_96 = lean_ctor_get(x_79, 16);
lean_inc(x_96);
x_97 = lean_ctor_get(x_79, 17);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_79, 18);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_79, 19);
lean_inc(x_99);
x_100 = lean_ctor_get(x_79, 20);
lean_inc(x_100);
x_101 = lean_ctor_get(x_79, 21);
lean_inc(x_101);
x_102 = lean_ctor_get(x_79, 22);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_79, 23);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_79, 24);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_79, 25);
lean_inc(x_105);
x_106 = lean_ctor_get(x_79, 26);
lean_inc(x_106);
x_107 = lean_ctor_get(x_79, 27);
lean_inc(x_107);
x_108 = lean_ctor_get(x_79, 28);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_79, 29);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_79, 30);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_79, 31);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_79, 32);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_79, 33);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_79, 34);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_79, 35);
lean_inc_ref(x_115);
x_116 = lean_ctor_get_uint8(x_79, sizeof(void*)*42);
x_117 = lean_ctor_get(x_79, 36);
lean_inc(x_117);
x_118 = lean_ctor_get(x_79, 37);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_79, 38);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_79, 39);
lean_inc(x_120);
x_121 = lean_ctor_get(x_79, 40);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_79, 41);
lean_inc_ref(x_122);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 lean_ctor_release(x_79, 3);
 lean_ctor_release(x_79, 4);
 lean_ctor_release(x_79, 5);
 lean_ctor_release(x_79, 6);
 lean_ctor_release(x_79, 7);
 lean_ctor_release(x_79, 8);
 lean_ctor_release(x_79, 9);
 lean_ctor_release(x_79, 10);
 lean_ctor_release(x_79, 11);
 lean_ctor_release(x_79, 12);
 lean_ctor_release(x_79, 13);
 lean_ctor_release(x_79, 14);
 lean_ctor_release(x_79, 15);
 lean_ctor_release(x_79, 16);
 lean_ctor_release(x_79, 17);
 lean_ctor_release(x_79, 18);
 lean_ctor_release(x_79, 19);
 lean_ctor_release(x_79, 20);
 lean_ctor_release(x_79, 21);
 lean_ctor_release(x_79, 22);
 lean_ctor_release(x_79, 23);
 lean_ctor_release(x_79, 24);
 lean_ctor_release(x_79, 25);
 lean_ctor_release(x_79, 26);
 lean_ctor_release(x_79, 27);
 lean_ctor_release(x_79, 28);
 lean_ctor_release(x_79, 29);
 lean_ctor_release(x_79, 30);
 lean_ctor_release(x_79, 31);
 lean_ctor_release(x_79, 32);
 lean_ctor_release(x_79, 33);
 lean_ctor_release(x_79, 34);
 lean_ctor_release(x_79, 35);
 lean_ctor_release(x_79, 36);
 lean_ctor_release(x_79, 37);
 lean_ctor_release(x_79, 38);
 lean_ctor_release(x_79, 39);
 lean_ctor_release(x_79, 40);
 lean_ctor_release(x_79, 41);
 x_123 = x_79;
} else {
 lean_dec_ref(x_79);
 x_123 = lean_box(0);
}
x_124 = lean_box(0);
x_125 = lean_array_fset(x_5, x_1, x_124);
x_126 = l_Lean_PersistentArray_set___redArg(x_114, x_2, x_3);
if (lean_is_scalar(x_123)) {
 x_127 = lean_alloc_ctor(0, 42, 1);
} else {
 x_127 = x_123;
}
lean_ctor_set(x_127, 0, x_80);
lean_ctor_set(x_127, 1, x_81);
lean_ctor_set(x_127, 2, x_82);
lean_ctor_set(x_127, 3, x_83);
lean_ctor_set(x_127, 4, x_84);
lean_ctor_set(x_127, 5, x_85);
lean_ctor_set(x_127, 6, x_86);
lean_ctor_set(x_127, 7, x_87);
lean_ctor_set(x_127, 8, x_88);
lean_ctor_set(x_127, 9, x_89);
lean_ctor_set(x_127, 10, x_90);
lean_ctor_set(x_127, 11, x_91);
lean_ctor_set(x_127, 12, x_92);
lean_ctor_set(x_127, 13, x_93);
lean_ctor_set(x_127, 14, x_94);
lean_ctor_set(x_127, 15, x_95);
lean_ctor_set(x_127, 16, x_96);
lean_ctor_set(x_127, 17, x_97);
lean_ctor_set(x_127, 18, x_98);
lean_ctor_set(x_127, 19, x_99);
lean_ctor_set(x_127, 20, x_100);
lean_ctor_set(x_127, 21, x_101);
lean_ctor_set(x_127, 22, x_102);
lean_ctor_set(x_127, 23, x_103);
lean_ctor_set(x_127, 24, x_104);
lean_ctor_set(x_127, 25, x_105);
lean_ctor_set(x_127, 26, x_106);
lean_ctor_set(x_127, 27, x_107);
lean_ctor_set(x_127, 28, x_108);
lean_ctor_set(x_127, 29, x_109);
lean_ctor_set(x_127, 30, x_110);
lean_ctor_set(x_127, 31, x_111);
lean_ctor_set(x_127, 32, x_112);
lean_ctor_set(x_127, 33, x_113);
lean_ctor_set(x_127, 34, x_126);
lean_ctor_set(x_127, 35, x_115);
lean_ctor_set(x_127, 36, x_117);
lean_ctor_set(x_127, 37, x_118);
lean_ctor_set(x_127, 38, x_119);
lean_ctor_set(x_127, 39, x_120);
lean_ctor_set(x_127, 40, x_121);
lean_ctor_set(x_127, 41, x_122);
lean_ctor_set_uint8(x_127, sizeof(void*)*42, x_116);
x_128 = lean_array_fset(x_125, x_1, x_127);
x_129 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_6);
lean_ctor_set(x_129, 2, x_7);
lean_ctor_set(x_129, 3, x_8);
lean_ctor_set(x_129, 4, x_9);
lean_ctor_set(x_129, 5, x_10);
lean_ctor_set(x_129, 6, x_11);
lean_ctor_set(x_129, 7, x_12);
return x_129;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_21; lean_object* x_22; uint8_t x_27; 
x_27 = lean_usize_dec_lt(x_8, x_7);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_9);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
lean_dec_ref(x_9);
x_29 = lean_array_uget(x_6, x_8);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc_ref(x_3);
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_1, x_2, x_3, x_31, x_32, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_36 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_35, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec_ref(x_36);
x_37 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_free_object(x_37);
lean_free_object(x_29);
lean_inc_ref(x_4);
x_21 = x_4;
x_22 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_41; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0;
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_29, 0, x_41);
lean_ctor_set(x_37, 0, x_29);
return x_37;
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_free_object(x_29);
lean_inc_ref(x_4);
x_21 = x_4;
x_22 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_44 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0;
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_29, 0, x_44);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_29);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_free_object(x_29);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_46 = !lean_is_exclusive(x_37);
if (x_46 == 0)
{
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_free_object(x_29);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_49 = !lean_is_exclusive(x_36);
if (x_49 == 0)
{
return x_36;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_36, 0);
lean_inc(x_50);
lean_dec(x_36);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_34);
lean_free_object(x_29);
lean_inc(x_10);
x_52 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_32, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_32);
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_52);
lean_inc_ref(x_4);
x_21 = x_4;
x_22 = lean_box(0);
goto block_26;
}
else
{
uint8_t x_53; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_29);
lean_dec(x_32);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_56 = !lean_is_exclusive(x_33);
if (x_56 == 0)
{
return x_33;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_33, 0);
lean_inc(x_57);
lean_dec(x_33);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_29, 0);
x_60 = lean_ctor_get(x_29, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_29);
lean_inc(x_60);
lean_inc_ref(x_3);
x_61 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_1, x_2, x_3, x_59, x_60, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_64 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_63, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_dec_ref(x_64);
x_65 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_unbox(x_66);
lean_dec(x_66);
if (x_68 == 0)
{
lean_dec(x_67);
lean_inc_ref(x_4);
x_21 = x_4;
x_22 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_69 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0;
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_5);
if (lean_is_scalar(x_67)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_67;
}
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_72 = lean_ctor_get(x_65, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_75 = lean_ctor_get(x_64, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_76 = x_64;
} else {
 lean_dec_ref(x_64);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_62);
lean_inc(x_10);
x_78 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_60, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_60);
if (lean_obj_tag(x_78) == 0)
{
lean_dec_ref(x_78);
lean_inc_ref(x_4);
x_21 = x_4;
x_22 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_60);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_82 = lean_ctor_get(x_61, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_83 = x_61;
} else {
 lean_dec_ref(x_61);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_82);
return x_84;
}
}
}
block_26:
{
size_t x_23; size_t x_24; 
x_23 = 1;
x_24 = lean_usize_add(x_8, x_23);
x_8 = x_24;
x_9 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args) {
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
lean_object* x_20 = _args[19];
_start:
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_22 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_16);
x_20 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_47 = lean_ctor_get(x_21, 34);
lean_inc_ref(x_47);
lean_dec(x_21);
x_48 = lean_ctor_get(x_47, 2);
x_49 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0;
x_50 = lean_nat_dec_lt(x_4, x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec_ref(x_47);
x_51 = l_outOfBounds___redArg(x_49);
x_22 = x_51;
goto block_46;
}
else
{
lean_object* x_52; 
x_52 = l_Lean_PersistentArray_get_x21___redArg(x_49, x_47, x_4);
x_22 = x_52;
goto block_46;
}
block_46:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(x_2, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_inc(x_5);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(x_26, 0, x_5);
lean_closure_set(x_26, 1, x_4);
lean_closure_set(x_26, 2, x_24);
x_27 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_28 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_27, x_26, x_6);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
lean_dec_ref(x_28);
x_29 = lean_box(0);
x_30 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0;
x_31 = lean_array_size(x_25);
x_32 = 0;
x_33 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(x_1, x_2, x_3, x_30, x_29, x_25, x_31, x_32, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_25);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_ctor_set(x_33, 0, x_29);
return x_33;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_29);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
return x_33;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
lean_dec(x_25);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_28;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_53 = !lean_is_exclusive(x_20);
if (x_53 == 0)
{
return x_20;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_20, 0);
lean_inc(x_54);
lean_dec(x_20);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_56 = lean_box(0);
lean_ctor_set(x_16, 0, x_56);
return x_16;
}
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_16, 0);
lean_inc(x_57);
lean_dec(x_16);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_83 = lean_ctor_get(x_60, 34);
lean_inc_ref(x_83);
lean_dec(x_60);
x_84 = lean_ctor_get(x_83, 2);
x_85 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0;
x_86 = lean_nat_dec_lt(x_4, x_84);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec_ref(x_83);
x_87 = l_outOfBounds___redArg(x_85);
x_61 = x_87;
goto block_82;
}
else
{
lean_object* x_88; 
x_88 = l_Lean_PersistentArray_get_x21___redArg(x_85, x_83, x_4);
x_61 = x_88;
goto block_82;
}
block_82:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(x_2, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec_ref(x_62);
lean_inc(x_5);
x_65 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(x_65, 0, x_5);
lean_closure_set(x_65, 1, x_4);
lean_closure_set(x_65, 2, x_63);
x_66 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_67 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_66, x_65, x_6);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; 
lean_dec_ref(x_67);
x_68 = lean_box(0);
x_69 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0;
x_70 = lean_array_size(x_64);
x_71 = 0;
x_72 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(x_1, x_2, x_3, x_69, x_68, x_64, x_70, x_71, x_69, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_64);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_68);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec_ref(x_75);
if (lean_is_scalar(x_74)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_74;
}
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_72, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
return x_81;
}
}
else
{
lean_dec(x_64);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_67;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_89 = lean_ctor_get(x_59, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_90 = x_59;
} else {
 lean_dec_ref(x_59);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_94 = !lean_is_exclusive(x_16);
if (x_94 == 0)
{
return x_16;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_16, 0);
lean_inc(x_95);
lean_dec(x_16);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_17);
x_18 = lean_nat_to_int(x_1);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
lean_dec(x_18);
return x_19;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_1, x_12);
if (x_13 == 0)
{
return x_3;
}
else
{
uint8_t x_14; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_3, 7);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 6);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 5);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 4);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 3);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = lean_array_fget(x_4, x_1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_23, 40);
x_26 = lean_box(0);
x_27 = lean_array_fset(x_4, x_1, x_26);
x_28 = lean_box(1);
x_29 = l_Lean_PersistentArray_set___redArg(x_25, x_2, x_28);
lean_ctor_set(x_23, 40, x_29);
x_30 = lean_array_fset(x_27, x_1, x_23);
lean_ctor_set(x_3, 0, x_30);
return x_3;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
x_33 = lean_ctor_get(x_23, 2);
x_34 = lean_ctor_get(x_23, 3);
x_35 = lean_ctor_get(x_23, 4);
x_36 = lean_ctor_get(x_23, 5);
x_37 = lean_ctor_get(x_23, 6);
x_38 = lean_ctor_get(x_23, 7);
x_39 = lean_ctor_get(x_23, 8);
x_40 = lean_ctor_get(x_23, 9);
x_41 = lean_ctor_get(x_23, 10);
x_42 = lean_ctor_get(x_23, 11);
x_43 = lean_ctor_get(x_23, 12);
x_44 = lean_ctor_get(x_23, 13);
x_45 = lean_ctor_get(x_23, 14);
x_46 = lean_ctor_get(x_23, 15);
x_47 = lean_ctor_get(x_23, 16);
x_48 = lean_ctor_get(x_23, 17);
x_49 = lean_ctor_get(x_23, 18);
x_50 = lean_ctor_get(x_23, 19);
x_51 = lean_ctor_get(x_23, 20);
x_52 = lean_ctor_get(x_23, 21);
x_53 = lean_ctor_get(x_23, 22);
x_54 = lean_ctor_get(x_23, 23);
x_55 = lean_ctor_get(x_23, 24);
x_56 = lean_ctor_get(x_23, 25);
x_57 = lean_ctor_get(x_23, 26);
x_58 = lean_ctor_get(x_23, 27);
x_59 = lean_ctor_get(x_23, 28);
x_60 = lean_ctor_get(x_23, 29);
x_61 = lean_ctor_get(x_23, 30);
x_62 = lean_ctor_get(x_23, 31);
x_63 = lean_ctor_get(x_23, 32);
x_64 = lean_ctor_get(x_23, 33);
x_65 = lean_ctor_get(x_23, 34);
x_66 = lean_ctor_get(x_23, 35);
x_67 = lean_ctor_get_uint8(x_23, sizeof(void*)*42);
x_68 = lean_ctor_get(x_23, 36);
x_69 = lean_ctor_get(x_23, 37);
x_70 = lean_ctor_get(x_23, 38);
x_71 = lean_ctor_get(x_23, 39);
x_72 = lean_ctor_get(x_23, 40);
x_73 = lean_ctor_get(x_23, 41);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_74 = lean_box(0);
x_75 = lean_array_fset(x_4, x_1, x_74);
x_76 = lean_box(1);
x_77 = l_Lean_PersistentArray_set___redArg(x_72, x_2, x_76);
x_78 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_78, 0, x_31);
lean_ctor_set(x_78, 1, x_32);
lean_ctor_set(x_78, 2, x_33);
lean_ctor_set(x_78, 3, x_34);
lean_ctor_set(x_78, 4, x_35);
lean_ctor_set(x_78, 5, x_36);
lean_ctor_set(x_78, 6, x_37);
lean_ctor_set(x_78, 7, x_38);
lean_ctor_set(x_78, 8, x_39);
lean_ctor_set(x_78, 9, x_40);
lean_ctor_set(x_78, 10, x_41);
lean_ctor_set(x_78, 11, x_42);
lean_ctor_set(x_78, 12, x_43);
lean_ctor_set(x_78, 13, x_44);
lean_ctor_set(x_78, 14, x_45);
lean_ctor_set(x_78, 15, x_46);
lean_ctor_set(x_78, 16, x_47);
lean_ctor_set(x_78, 17, x_48);
lean_ctor_set(x_78, 18, x_49);
lean_ctor_set(x_78, 19, x_50);
lean_ctor_set(x_78, 20, x_51);
lean_ctor_set(x_78, 21, x_52);
lean_ctor_set(x_78, 22, x_53);
lean_ctor_set(x_78, 23, x_54);
lean_ctor_set(x_78, 24, x_55);
lean_ctor_set(x_78, 25, x_56);
lean_ctor_set(x_78, 26, x_57);
lean_ctor_set(x_78, 27, x_58);
lean_ctor_set(x_78, 28, x_59);
lean_ctor_set(x_78, 29, x_60);
lean_ctor_set(x_78, 30, x_61);
lean_ctor_set(x_78, 31, x_62);
lean_ctor_set(x_78, 32, x_63);
lean_ctor_set(x_78, 33, x_64);
lean_ctor_set(x_78, 34, x_65);
lean_ctor_set(x_78, 35, x_66);
lean_ctor_set(x_78, 36, x_68);
lean_ctor_set(x_78, 37, x_69);
lean_ctor_set(x_78, 38, x_70);
lean_ctor_set(x_78, 39, x_71);
lean_ctor_set(x_78, 40, x_77);
lean_ctor_set(x_78, 41, x_73);
lean_ctor_set_uint8(x_78, sizeof(void*)*42, x_67);
x_79 = lean_array_fset(x_75, x_1, x_78);
lean_ctor_set(x_3, 0, x_79);
return x_3;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_3);
x_80 = lean_array_fget(x_4, x_1);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 2);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_80, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 4);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_80, 5);
lean_inc(x_86);
x_87 = lean_ctor_get(x_80, 6);
lean_inc(x_87);
x_88 = lean_ctor_get(x_80, 7);
lean_inc(x_88);
x_89 = lean_ctor_get(x_80, 8);
lean_inc(x_89);
x_90 = lean_ctor_get(x_80, 9);
lean_inc(x_90);
x_91 = lean_ctor_get(x_80, 10);
lean_inc(x_91);
x_92 = lean_ctor_get(x_80, 11);
lean_inc(x_92);
x_93 = lean_ctor_get(x_80, 12);
lean_inc(x_93);
x_94 = lean_ctor_get(x_80, 13);
lean_inc(x_94);
x_95 = lean_ctor_get(x_80, 14);
lean_inc(x_95);
x_96 = lean_ctor_get(x_80, 15);
lean_inc(x_96);
x_97 = lean_ctor_get(x_80, 16);
lean_inc(x_97);
x_98 = lean_ctor_get(x_80, 17);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_80, 18);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_80, 19);
lean_inc(x_100);
x_101 = lean_ctor_get(x_80, 20);
lean_inc(x_101);
x_102 = lean_ctor_get(x_80, 21);
lean_inc(x_102);
x_103 = lean_ctor_get(x_80, 22);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_80, 23);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_80, 24);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_80, 25);
lean_inc(x_106);
x_107 = lean_ctor_get(x_80, 26);
lean_inc(x_107);
x_108 = lean_ctor_get(x_80, 27);
lean_inc(x_108);
x_109 = lean_ctor_get(x_80, 28);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_80, 29);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_80, 30);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_80, 31);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_80, 32);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_80, 33);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_80, 34);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_80, 35);
lean_inc_ref(x_116);
x_117 = lean_ctor_get_uint8(x_80, sizeof(void*)*42);
x_118 = lean_ctor_get(x_80, 36);
lean_inc(x_118);
x_119 = lean_ctor_get(x_80, 37);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_80, 38);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_80, 39);
lean_inc(x_121);
x_122 = lean_ctor_get(x_80, 40);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_80, 41);
lean_inc_ref(x_123);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 lean_ctor_release(x_80, 5);
 lean_ctor_release(x_80, 6);
 lean_ctor_release(x_80, 7);
 lean_ctor_release(x_80, 8);
 lean_ctor_release(x_80, 9);
 lean_ctor_release(x_80, 10);
 lean_ctor_release(x_80, 11);
 lean_ctor_release(x_80, 12);
 lean_ctor_release(x_80, 13);
 lean_ctor_release(x_80, 14);
 lean_ctor_release(x_80, 15);
 lean_ctor_release(x_80, 16);
 lean_ctor_release(x_80, 17);
 lean_ctor_release(x_80, 18);
 lean_ctor_release(x_80, 19);
 lean_ctor_release(x_80, 20);
 lean_ctor_release(x_80, 21);
 lean_ctor_release(x_80, 22);
 lean_ctor_release(x_80, 23);
 lean_ctor_release(x_80, 24);
 lean_ctor_release(x_80, 25);
 lean_ctor_release(x_80, 26);
 lean_ctor_release(x_80, 27);
 lean_ctor_release(x_80, 28);
 lean_ctor_release(x_80, 29);
 lean_ctor_release(x_80, 30);
 lean_ctor_release(x_80, 31);
 lean_ctor_release(x_80, 32);
 lean_ctor_release(x_80, 33);
 lean_ctor_release(x_80, 34);
 lean_ctor_release(x_80, 35);
 lean_ctor_release(x_80, 36);
 lean_ctor_release(x_80, 37);
 lean_ctor_release(x_80, 38);
 lean_ctor_release(x_80, 39);
 lean_ctor_release(x_80, 40);
 lean_ctor_release(x_80, 41);
 x_124 = x_80;
} else {
 lean_dec_ref(x_80);
 x_124 = lean_box(0);
}
x_125 = lean_box(0);
x_126 = lean_array_fset(x_4, x_1, x_125);
x_127 = lean_box(1);
x_128 = l_Lean_PersistentArray_set___redArg(x_122, x_2, x_127);
if (lean_is_scalar(x_124)) {
 x_129 = lean_alloc_ctor(0, 42, 1);
} else {
 x_129 = x_124;
}
lean_ctor_set(x_129, 0, x_81);
lean_ctor_set(x_129, 1, x_82);
lean_ctor_set(x_129, 2, x_83);
lean_ctor_set(x_129, 3, x_84);
lean_ctor_set(x_129, 4, x_85);
lean_ctor_set(x_129, 5, x_86);
lean_ctor_set(x_129, 6, x_87);
lean_ctor_set(x_129, 7, x_88);
lean_ctor_set(x_129, 8, x_89);
lean_ctor_set(x_129, 9, x_90);
lean_ctor_set(x_129, 10, x_91);
lean_ctor_set(x_129, 11, x_92);
lean_ctor_set(x_129, 12, x_93);
lean_ctor_set(x_129, 13, x_94);
lean_ctor_set(x_129, 14, x_95);
lean_ctor_set(x_129, 15, x_96);
lean_ctor_set(x_129, 16, x_97);
lean_ctor_set(x_129, 17, x_98);
lean_ctor_set(x_129, 18, x_99);
lean_ctor_set(x_129, 19, x_100);
lean_ctor_set(x_129, 20, x_101);
lean_ctor_set(x_129, 21, x_102);
lean_ctor_set(x_129, 22, x_103);
lean_ctor_set(x_129, 23, x_104);
lean_ctor_set(x_129, 24, x_105);
lean_ctor_set(x_129, 25, x_106);
lean_ctor_set(x_129, 26, x_107);
lean_ctor_set(x_129, 27, x_108);
lean_ctor_set(x_129, 28, x_109);
lean_ctor_set(x_129, 29, x_110);
lean_ctor_set(x_129, 30, x_111);
lean_ctor_set(x_129, 31, x_112);
lean_ctor_set(x_129, 32, x_113);
lean_ctor_set(x_129, 33, x_114);
lean_ctor_set(x_129, 34, x_115);
lean_ctor_set(x_129, 35, x_116);
lean_ctor_set(x_129, 36, x_118);
lean_ctor_set(x_129, 37, x_119);
lean_ctor_set(x_129, 38, x_120);
lean_ctor_set(x_129, 39, x_121);
lean_ctor_set(x_129, 40, x_128);
lean_ctor_set(x_129, 41, x_123);
lean_ctor_set_uint8(x_129, sizeof(void*)*42, x_117);
x_130 = lean_array_fset(x_126, x_1, x_129);
x_131 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_5);
lean_ctor_set(x_131, 2, x_6);
lean_ctor_set(x_131, 3, x_7);
lean_ctor_set(x_131, 4, x_8);
lean_ctor_set(x_131, 5, x_9);
lean_ctor_set(x_131, 6, x_10);
lean_ctor_set(x_131, 7, x_11);
return x_131;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 4);
lean_inc(x_20);
lean_dec_ref(x_6);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(x_1, x_2, x_3, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec_ref(x_21);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(x_1, x_2, x_3, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_dec_ref(x_22);
{
lean_object* _tmp_4 = x_4;
lean_object* _tmp_5 = x_20;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_5);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_33; uint8_t x_34; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 40);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_2);
lean_inc(x_4);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(x_19, 0, x_4);
lean_closure_set(x_19, 1, x_2);
x_33 = lean_box(1);
x_34 = lean_nat_dec_lt(x_2, x_18);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec_ref(x_17);
x_35 = l_outOfBounds___redArg(x_33);
x_20 = x_35;
goto block_32;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_PersistentArray_get_x21___redArg(x_33, x_17, x_2);
x_20 = x_36;
goto block_32;
}
block_32:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_22 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_21, x_19, x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec_ref(x_22);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(x_1, x_2, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_23);
x_24 = lean_box(0);
x_25 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(x_1, x_2, x_3, x_24, x_24, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_28; 
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_24);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
}
else
{
lean_dec(x_20);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
return x_15;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_15, 0);
lean_inc(x_38);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_18; 
x_18 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_19 = lean_ctor_get(x_18, 0);
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 2);
x_61 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0;
x_62 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_63 = lean_int_dec_eq(x_19, x_62);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = lean_int_dec_eq(x_19, x_61);
if (x_64 == 0)
{
x_13 = lean_box(0);
goto block_17;
}
else
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_21, 0);
x_66 = lean_ctor_get(x_21, 1);
x_67 = lean_ctor_get(x_21, 2);
x_68 = lean_int_dec_eq(x_65, x_62);
if (x_68 == 0)
{
x_13 = lean_box(0);
goto block_17;
}
else
{
if (lean_obj_tag(x_67) == 0)
{
x_22 = x_66;
x_23 = x_2;
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = lean_box(0);
goto block_60;
}
else
{
x_13 = lean_box(0);
goto block_17;
}
}
}
else
{
x_13 = lean_box(0);
goto block_17;
}
}
}
else
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_21, 0);
x_70 = lean_ctor_get(x_21, 1);
x_71 = lean_ctor_get(x_21, 2);
x_72 = lean_int_dec_eq(x_69, x_61);
if (x_72 == 0)
{
x_13 = lean_box(0);
goto block_17;
}
else
{
if (lean_obj_tag(x_71) == 0)
{
x_22 = x_70;
x_23 = x_2;
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = lean_box(0);
goto block_60;
}
else
{
x_13 = lean_box(0);
goto block_17;
}
}
}
else
{
x_13 = lean_box(0);
goto block_17;
}
}
block_60:
{
lean_object* x_34; 
x_34 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_20, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = l_Lean_Meta_Grind_isEqv___redArg(x_35, x_37, x_24);
lean_dec(x_37);
lean_dec(x_35);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; lean_object* x_43; 
x_42 = 1;
x_43 = lean_box(x_42);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
uint8_t x_44; lean_object* x_45; 
x_44 = 0;
x_45 = lean_box(x_44);
lean_ctor_set(x_38, 0, x_45);
return x_38;
}
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_48 = 1;
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
else
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_51 = 0;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
return x_38;
}
}
else
{
uint8_t x_54; 
lean_dec(x_35);
x_54 = !lean_is_exclusive(x_36);
if (x_54 == 0)
{
return x_36;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_36, 0);
lean_inc(x_55);
lean_dec(x_36);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_34);
if (x_57 == 0)
{
return x_34;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_34, 0);
lean_inc(x_58);
lean_dec(x_34);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
else
{
x_13 = lean_box(0);
goto block_17;
}
block_17:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_6 = lean_int_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
lean_inc_ref(x_3);
x_9 = l_Lean_Grind_Linarith_Poly_mul(x_3, x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_1, x_13);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
else
{
uint8_t x_15; 
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_4, 7);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 6);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 5);
lean_dec(x_18);
x_19 = lean_ctor_get(x_4, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_fget(x_5, x_1);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_24, 38);
x_27 = lean_ctor_get(x_24, 39);
x_28 = lean_box(0);
x_29 = lean_array_fset(x_5, x_1, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_2);
x_31 = l_Lean_PersistentArray_set___redArg(x_26, x_3, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_24, 39, x_32);
lean_ctor_set(x_24, 38, x_31);
x_33 = lean_array_fset(x_29, x_1, x_24);
lean_ctor_set(x_4, 0, x_33);
return x_4;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
x_36 = lean_ctor_get(x_24, 2);
x_37 = lean_ctor_get(x_24, 3);
x_38 = lean_ctor_get(x_24, 4);
x_39 = lean_ctor_get(x_24, 5);
x_40 = lean_ctor_get(x_24, 6);
x_41 = lean_ctor_get(x_24, 7);
x_42 = lean_ctor_get(x_24, 8);
x_43 = lean_ctor_get(x_24, 9);
x_44 = lean_ctor_get(x_24, 10);
x_45 = lean_ctor_get(x_24, 11);
x_46 = lean_ctor_get(x_24, 12);
x_47 = lean_ctor_get(x_24, 13);
x_48 = lean_ctor_get(x_24, 14);
x_49 = lean_ctor_get(x_24, 15);
x_50 = lean_ctor_get(x_24, 16);
x_51 = lean_ctor_get(x_24, 17);
x_52 = lean_ctor_get(x_24, 18);
x_53 = lean_ctor_get(x_24, 19);
x_54 = lean_ctor_get(x_24, 20);
x_55 = lean_ctor_get(x_24, 21);
x_56 = lean_ctor_get(x_24, 22);
x_57 = lean_ctor_get(x_24, 23);
x_58 = lean_ctor_get(x_24, 24);
x_59 = lean_ctor_get(x_24, 25);
x_60 = lean_ctor_get(x_24, 26);
x_61 = lean_ctor_get(x_24, 27);
x_62 = lean_ctor_get(x_24, 28);
x_63 = lean_ctor_get(x_24, 29);
x_64 = lean_ctor_get(x_24, 30);
x_65 = lean_ctor_get(x_24, 31);
x_66 = lean_ctor_get(x_24, 32);
x_67 = lean_ctor_get(x_24, 33);
x_68 = lean_ctor_get(x_24, 34);
x_69 = lean_ctor_get(x_24, 35);
x_70 = lean_ctor_get_uint8(x_24, sizeof(void*)*42);
x_71 = lean_ctor_get(x_24, 36);
x_72 = lean_ctor_get(x_24, 37);
x_73 = lean_ctor_get(x_24, 38);
x_74 = lean_ctor_get(x_24, 39);
x_75 = lean_ctor_get(x_24, 40);
x_76 = lean_ctor_get(x_24, 41);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_77 = lean_box(0);
x_78 = lean_array_fset(x_5, x_1, x_77);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_2);
x_80 = l_Lean_PersistentArray_set___redArg(x_73, x_3, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_3);
lean_ctor_set(x_81, 1, x_74);
x_82 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_82, 0, x_34);
lean_ctor_set(x_82, 1, x_35);
lean_ctor_set(x_82, 2, x_36);
lean_ctor_set(x_82, 3, x_37);
lean_ctor_set(x_82, 4, x_38);
lean_ctor_set(x_82, 5, x_39);
lean_ctor_set(x_82, 6, x_40);
lean_ctor_set(x_82, 7, x_41);
lean_ctor_set(x_82, 8, x_42);
lean_ctor_set(x_82, 9, x_43);
lean_ctor_set(x_82, 10, x_44);
lean_ctor_set(x_82, 11, x_45);
lean_ctor_set(x_82, 12, x_46);
lean_ctor_set(x_82, 13, x_47);
lean_ctor_set(x_82, 14, x_48);
lean_ctor_set(x_82, 15, x_49);
lean_ctor_set(x_82, 16, x_50);
lean_ctor_set(x_82, 17, x_51);
lean_ctor_set(x_82, 18, x_52);
lean_ctor_set(x_82, 19, x_53);
lean_ctor_set(x_82, 20, x_54);
lean_ctor_set(x_82, 21, x_55);
lean_ctor_set(x_82, 22, x_56);
lean_ctor_set(x_82, 23, x_57);
lean_ctor_set(x_82, 24, x_58);
lean_ctor_set(x_82, 25, x_59);
lean_ctor_set(x_82, 26, x_60);
lean_ctor_set(x_82, 27, x_61);
lean_ctor_set(x_82, 28, x_62);
lean_ctor_set(x_82, 29, x_63);
lean_ctor_set(x_82, 30, x_64);
lean_ctor_set(x_82, 31, x_65);
lean_ctor_set(x_82, 32, x_66);
lean_ctor_set(x_82, 33, x_67);
lean_ctor_set(x_82, 34, x_68);
lean_ctor_set(x_82, 35, x_69);
lean_ctor_set(x_82, 36, x_71);
lean_ctor_set(x_82, 37, x_72);
lean_ctor_set(x_82, 38, x_80);
lean_ctor_set(x_82, 39, x_81);
lean_ctor_set(x_82, 40, x_75);
lean_ctor_set(x_82, 41, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*42, x_70);
x_83 = lean_array_fset(x_78, x_1, x_82);
lean_ctor_set(x_4, 0, x_83);
return x_4;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_4);
x_84 = lean_array_fget(x_5, x_1);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 2);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_84, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_84, 4);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_84, 5);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 6);
lean_inc(x_91);
x_92 = lean_ctor_get(x_84, 7);
lean_inc(x_92);
x_93 = lean_ctor_get(x_84, 8);
lean_inc(x_93);
x_94 = lean_ctor_get(x_84, 9);
lean_inc(x_94);
x_95 = lean_ctor_get(x_84, 10);
lean_inc(x_95);
x_96 = lean_ctor_get(x_84, 11);
lean_inc(x_96);
x_97 = lean_ctor_get(x_84, 12);
lean_inc(x_97);
x_98 = lean_ctor_get(x_84, 13);
lean_inc(x_98);
x_99 = lean_ctor_get(x_84, 14);
lean_inc(x_99);
x_100 = lean_ctor_get(x_84, 15);
lean_inc(x_100);
x_101 = lean_ctor_get(x_84, 16);
lean_inc(x_101);
x_102 = lean_ctor_get(x_84, 17);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_84, 18);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_84, 19);
lean_inc(x_104);
x_105 = lean_ctor_get(x_84, 20);
lean_inc(x_105);
x_106 = lean_ctor_get(x_84, 21);
lean_inc(x_106);
x_107 = lean_ctor_get(x_84, 22);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_84, 23);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_84, 24);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_84, 25);
lean_inc(x_110);
x_111 = lean_ctor_get(x_84, 26);
lean_inc(x_111);
x_112 = lean_ctor_get(x_84, 27);
lean_inc(x_112);
x_113 = lean_ctor_get(x_84, 28);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_84, 29);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_84, 30);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_84, 31);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_84, 32);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_84, 33);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_84, 34);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_84, 35);
lean_inc_ref(x_120);
x_121 = lean_ctor_get_uint8(x_84, sizeof(void*)*42);
x_122 = lean_ctor_get(x_84, 36);
lean_inc(x_122);
x_123 = lean_ctor_get(x_84, 37);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_84, 38);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_84, 39);
lean_inc(x_125);
x_126 = lean_ctor_get(x_84, 40);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_84, 41);
lean_inc_ref(x_127);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 lean_ctor_release(x_84, 3);
 lean_ctor_release(x_84, 4);
 lean_ctor_release(x_84, 5);
 lean_ctor_release(x_84, 6);
 lean_ctor_release(x_84, 7);
 lean_ctor_release(x_84, 8);
 lean_ctor_release(x_84, 9);
 lean_ctor_release(x_84, 10);
 lean_ctor_release(x_84, 11);
 lean_ctor_release(x_84, 12);
 lean_ctor_release(x_84, 13);
 lean_ctor_release(x_84, 14);
 lean_ctor_release(x_84, 15);
 lean_ctor_release(x_84, 16);
 lean_ctor_release(x_84, 17);
 lean_ctor_release(x_84, 18);
 lean_ctor_release(x_84, 19);
 lean_ctor_release(x_84, 20);
 lean_ctor_release(x_84, 21);
 lean_ctor_release(x_84, 22);
 lean_ctor_release(x_84, 23);
 lean_ctor_release(x_84, 24);
 lean_ctor_release(x_84, 25);
 lean_ctor_release(x_84, 26);
 lean_ctor_release(x_84, 27);
 lean_ctor_release(x_84, 28);
 lean_ctor_release(x_84, 29);
 lean_ctor_release(x_84, 30);
 lean_ctor_release(x_84, 31);
 lean_ctor_release(x_84, 32);
 lean_ctor_release(x_84, 33);
 lean_ctor_release(x_84, 34);
 lean_ctor_release(x_84, 35);
 lean_ctor_release(x_84, 36);
 lean_ctor_release(x_84, 37);
 lean_ctor_release(x_84, 38);
 lean_ctor_release(x_84, 39);
 lean_ctor_release(x_84, 40);
 lean_ctor_release(x_84, 41);
 x_128 = x_84;
} else {
 lean_dec_ref(x_84);
 x_128 = lean_box(0);
}
x_129 = lean_box(0);
x_130 = lean_array_fset(x_5, x_1, x_129);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_2);
x_132 = l_Lean_PersistentArray_set___redArg(x_124, x_3, x_131);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_3);
lean_ctor_set(x_133, 1, x_125);
if (lean_is_scalar(x_128)) {
 x_134 = lean_alloc_ctor(0, 42, 1);
} else {
 x_134 = x_128;
}
lean_ctor_set(x_134, 0, x_85);
lean_ctor_set(x_134, 1, x_86);
lean_ctor_set(x_134, 2, x_87);
lean_ctor_set(x_134, 3, x_88);
lean_ctor_set(x_134, 4, x_89);
lean_ctor_set(x_134, 5, x_90);
lean_ctor_set(x_134, 6, x_91);
lean_ctor_set(x_134, 7, x_92);
lean_ctor_set(x_134, 8, x_93);
lean_ctor_set(x_134, 9, x_94);
lean_ctor_set(x_134, 10, x_95);
lean_ctor_set(x_134, 11, x_96);
lean_ctor_set(x_134, 12, x_97);
lean_ctor_set(x_134, 13, x_98);
lean_ctor_set(x_134, 14, x_99);
lean_ctor_set(x_134, 15, x_100);
lean_ctor_set(x_134, 16, x_101);
lean_ctor_set(x_134, 17, x_102);
lean_ctor_set(x_134, 18, x_103);
lean_ctor_set(x_134, 19, x_104);
lean_ctor_set(x_134, 20, x_105);
lean_ctor_set(x_134, 21, x_106);
lean_ctor_set(x_134, 22, x_107);
lean_ctor_set(x_134, 23, x_108);
lean_ctor_set(x_134, 24, x_109);
lean_ctor_set(x_134, 25, x_110);
lean_ctor_set(x_134, 26, x_111);
lean_ctor_set(x_134, 27, x_112);
lean_ctor_set(x_134, 28, x_113);
lean_ctor_set(x_134, 29, x_114);
lean_ctor_set(x_134, 30, x_115);
lean_ctor_set(x_134, 31, x_116);
lean_ctor_set(x_134, 32, x_117);
lean_ctor_set(x_134, 33, x_118);
lean_ctor_set(x_134, 34, x_119);
lean_ctor_set(x_134, 35, x_120);
lean_ctor_set(x_134, 36, x_122);
lean_ctor_set(x_134, 37, x_123);
lean_ctor_set(x_134, 38, x_132);
lean_ctor_set(x_134, 39, x_133);
lean_ctor_set(x_134, 40, x_126);
lean_ctor_set(x_134, 41, x_127);
lean_ctor_set_uint8(x_134, sizeof(void*)*42, x_121);
x_135 = lean_array_fset(x_130, x_1, x_134);
x_136 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_6);
lean_ctor_set(x_136, 2, x_7);
lean_ctor_set(x_136, 3, x_8);
lean_ctor_set(x_136, 4, x_9);
lean_ctor_set(x_136, 5, x_10);
lean_ctor_set(x_136, 6, x_11);
lean_ctor_set(x_136, 7, x_12);
return x_136;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(">> ", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_211 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0;
x_212 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_211, x_10);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec_ref(x_212);
x_214 = lean_unbox(x_213);
lean_dec(x_213);
if (x_214 == 0)
{
x_98 = x_2;
x_99 = x_3;
x_100 = x_4;
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_10;
x_107 = x_11;
x_108 = lean_box(0);
goto block_210;
}
else
{
lean_object* x_215; 
x_215 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec_ref(x_215);
x_217 = l_Lean_MessageData_ofExpr(x_216);
x_218 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_211, x_217, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_218) == 0)
{
lean_dec_ref(x_218);
x_98 = x_2;
x_99 = x_3;
x_100 = x_4;
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_10;
x_107 = x_11;
x_108 = lean_box(0);
goto block_210;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_218;
}
}
else
{
uint8_t x_219; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_219 = !lean_is_exclusive(x_215);
if (x_219 == 0)
{
return x_215;
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_215, 0);
lean_inc(x_220);
lean_dec(x_215);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
return x_221;
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_37:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_22);
x_33 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(x_33, 0, x_22);
lean_closure_set(x_33, 1, x_18);
lean_closure_set(x_33, 2, x_17);
x_34 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_35 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_34, x_33, x_23);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec_ref(x_35);
x_36 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
return x_36;
}
else
{
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec(x_19);
return x_35;
}
}
block_69:
{
lean_object* x_54; 
x_54 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_ctor_get_uint8(x_55, sizeof(void*)*42);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
x_17 = x_38;
x_18 = x_39;
x_19 = x_40;
x_20 = x_41;
x_21 = x_42;
x_22 = x_43;
x_23 = x_44;
x_24 = x_45;
x_25 = x_46;
x_26 = x_47;
x_27 = x_48;
x_28 = x_49;
x_29 = x_50;
x_30 = x_51;
x_31 = x_52;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_inc_ref(x_42);
x_60 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(x_42);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
lean_inc(x_52);
lean_inc_ref(x_51);
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
x_62 = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(x_61, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_17 = x_38;
x_18 = x_39;
x_19 = x_40;
x_20 = x_41;
x_21 = x_42;
x_22 = x_43;
x_23 = x_44;
x_24 = x_45;
x_25 = x_46;
x_26 = x_47;
x_27 = x_48;
x_28 = x_49;
x_29 = x_50;
x_30 = x_51;
x_31 = x_52;
x_32 = lean_box(0);
goto block_37;
}
else
{
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
x_63 = !lean_is_exclusive(x_57);
if (x_63 == 0)
{
return x_57;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_57, 0);
lean_inc(x_64);
lean_dec(x_57);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
x_17 = x_38;
x_18 = x_39;
x_19 = x_40;
x_20 = x_41;
x_21 = x_42;
x_22 = x_43;
x_23 = x_44;
x_24 = x_45;
x_25 = x_46;
x_26 = x_47;
x_27 = x_48;
x_28 = x_49;
x_29 = x_50;
x_30 = x_51;
x_31 = x_52;
x_32 = lean_box(0);
goto block_37;
}
}
else
{
uint8_t x_66; 
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
x_66 = !lean_is_exclusive(x_54);
if (x_66 == 0)
{
return x_54;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_54, 0);
lean_inc(x_67);
lean_dec(x_54);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
block_97:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4;
x_87 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_86, x_83);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
x_38 = x_70;
x_39 = x_71;
x_40 = x_72;
x_41 = x_73;
x_42 = x_74;
x_43 = x_75;
x_44 = x_76;
x_45 = x_77;
x_46 = x_78;
x_47 = x_79;
x_48 = x_80;
x_49 = x_81;
x_50 = x_82;
x_51 = x_83;
x_52 = x_84;
x_53 = lean_box(0);
goto block_69;
}
else
{
lean_object* x_90; 
x_90 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_74, x_75, x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = l_Lean_MessageData_ofExpr(x_91);
x_93 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_86, x_92, x_81, x_82, x_83, x_84);
if (lean_obj_tag(x_93) == 0)
{
lean_dec_ref(x_93);
x_38 = x_70;
x_39 = x_71;
x_40 = x_72;
x_41 = x_73;
x_42 = x_74;
x_43 = x_75;
x_44 = x_76;
x_45 = x_77;
x_46 = x_78;
x_47 = x_79;
x_48 = x_80;
x_49 = x_81;
x_50 = x_82;
x_51 = x_83;
x_52 = x_84;
x_53 = lean_box(0);
goto block_69;
}
else
{
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
x_94 = !lean_is_exclusive(x_90);
if (x_94 == 0)
{
return x_90;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
lean_dec(x_90);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
}
block_210:
{
lean_object* x_109; 
lean_inc_ref(x_106);
x_109 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(x_1, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_111 = lean_ctor_get(x_110, 0);
x_112 = lean_box(0);
x_113 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_111, x_112);
if (x_113 == 0)
{
lean_object* x_114; 
lean_inc(x_107);
lean_inc_ref(x_106);
lean_inc(x_105);
lean_inc_ref(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc_ref(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_114 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(x_110, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_115, 1);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_119 = lean_ctor_get(x_115, 0);
x_120 = lean_ctor_get(x_117, 0);
x_121 = lean_ctor_get(x_117, 1);
x_122 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_123 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_122, x_106);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_free_object(x_117);
lean_free_object(x_115);
lean_inc(x_121);
lean_inc(x_120);
x_70 = x_120;
x_71 = x_121;
x_72 = x_119;
x_73 = x_120;
x_74 = x_121;
x_75 = x_98;
x_76 = x_99;
x_77 = x_100;
x_78 = x_101;
x_79 = x_102;
x_80 = x_103;
x_81 = x_104;
x_82 = x_105;
x_83 = x_106;
x_84 = x_107;
x_85 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_126; 
x_126 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_120, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_121, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
x_130 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1;
x_131 = l_Lean_MessageData_ofExpr(x_127);
lean_ctor_set_tag(x_117, 7);
lean_ctor_set(x_117, 1, x_131);
lean_ctor_set(x_117, 0, x_130);
x_132 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
lean_ctor_set_tag(x_115, 7);
lean_ctor_set(x_115, 1, x_132);
lean_ctor_set(x_115, 0, x_117);
x_133 = l_Lean_MessageData_ofExpr(x_129);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_115);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_122, x_134, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_135) == 0)
{
lean_dec_ref(x_135);
lean_inc(x_121);
lean_inc(x_120);
x_70 = x_120;
x_71 = x_121;
x_72 = x_119;
x_73 = x_120;
x_74 = x_121;
x_75 = x_98;
x_76 = x_99;
x_77 = x_100;
x_78 = x_101;
x_79 = x_102;
x_80 = x_103;
x_81 = x_104;
x_82 = x_105;
x_83 = x_106;
x_84 = x_107;
x_85 = lean_box(0);
goto block_97;
}
else
{
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
return x_135;
}
}
else
{
uint8_t x_136; 
lean_dec(x_127);
lean_free_object(x_117);
lean_dec(x_121);
lean_dec(x_120);
lean_free_object(x_115);
lean_dec(x_119);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_136 = !lean_is_exclusive(x_128);
if (x_136 == 0)
{
return x_128;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
lean_dec(x_128);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_free_object(x_117);
lean_dec(x_121);
lean_dec(x_120);
lean_free_object(x_115);
lean_dec(x_119);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_139 = !lean_is_exclusive(x_126);
if (x_139 == 0)
{
return x_126;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_126, 0);
lean_inc(x_140);
lean_dec(x_126);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_142 = lean_ctor_get(x_115, 0);
x_143 = lean_ctor_get(x_117, 0);
x_144 = lean_ctor_get(x_117, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_117);
x_145 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_146 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_145, x_106);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
x_148 = lean_unbox(x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_free_object(x_115);
lean_inc(x_144);
lean_inc(x_143);
x_70 = x_143;
x_71 = x_144;
x_72 = x_142;
x_73 = x_143;
x_74 = x_144;
x_75 = x_98;
x_76 = x_99;
x_77 = x_100;
x_78 = x_101;
x_79 = x_102;
x_80 = x_103;
x_81 = x_104;
x_82 = x_105;
x_83 = x_106;
x_84 = x_107;
x_85 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_149; 
x_149 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_143, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec_ref(x_149);
x_151 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_144, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec_ref(x_151);
x_153 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1;
x_154 = l_Lean_MessageData_ofExpr(x_150);
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
lean_ctor_set_tag(x_115, 7);
lean_ctor_set(x_115, 1, x_156);
lean_ctor_set(x_115, 0, x_155);
x_157 = l_Lean_MessageData_ofExpr(x_152);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_115);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_145, x_158, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_159) == 0)
{
lean_dec_ref(x_159);
lean_inc(x_144);
lean_inc(x_143);
x_70 = x_143;
x_71 = x_144;
x_72 = x_142;
x_73 = x_143;
x_74 = x_144;
x_75 = x_98;
x_76 = x_99;
x_77 = x_100;
x_78 = x_101;
x_79 = x_102;
x_80 = x_103;
x_81 = x_104;
x_82 = x_105;
x_83 = x_106;
x_84 = x_107;
x_85 = lean_box(0);
goto block_97;
}
else
{
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_150);
lean_dec(x_144);
lean_dec(x_143);
lean_free_object(x_115);
lean_dec(x_142);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_160 = lean_ctor_get(x_151, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_161 = x_151;
} else {
 lean_dec_ref(x_151);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_144);
lean_dec(x_143);
lean_free_object(x_115);
lean_dec(x_142);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_163 = lean_ctor_get(x_149, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_164 = x_149;
} else {
 lean_dec_ref(x_149);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 1, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_163);
return x_165;
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_166 = lean_ctor_get(x_115, 1);
x_167 = lean_ctor_get(x_115, 0);
lean_inc(x_166);
lean_inc(x_167);
lean_dec(x_115);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_170 = x_166;
} else {
 lean_dec_ref(x_166);
 x_170 = lean_box(0);
}
x_171 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_172 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_171, x_106);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec_ref(x_172);
x_174 = lean_unbox(x_173);
lean_dec(x_173);
if (x_174 == 0)
{
lean_dec(x_170);
lean_inc(x_169);
lean_inc(x_168);
x_70 = x_168;
x_71 = x_169;
x_72 = x_167;
x_73 = x_168;
x_74 = x_169;
x_75 = x_98;
x_76 = x_99;
x_77 = x_100;
x_78 = x_101;
x_79 = x_102;
x_80 = x_103;
x_81 = x_104;
x_82 = x_105;
x_83 = x_106;
x_84 = x_107;
x_85 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_175; 
x_175 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_168, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_169, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1;
x_180 = l_Lean_MessageData_ofExpr(x_176);
if (lean_is_scalar(x_170)) {
 x_181 = lean_alloc_ctor(7, 2, 0);
} else {
 x_181 = x_170;
 lean_ctor_set_tag(x_181, 7);
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
x_183 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_MessageData_ofExpr(x_178);
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_171, x_185, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_186) == 0)
{
lean_dec_ref(x_186);
lean_inc(x_169);
lean_inc(x_168);
x_70 = x_168;
x_71 = x_169;
x_72 = x_167;
x_73 = x_168;
x_74 = x_169;
x_75 = x_98;
x_76 = x_99;
x_77 = x_100;
x_78 = x_101;
x_79 = x_102;
x_80 = x_103;
x_81 = x_104;
x_82 = x_105;
x_83 = x_106;
x_84 = x_107;
x_85 = lean_box(0);
goto block_97;
}
else
{
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_187 = lean_ctor_get(x_177, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_188 = x_177;
} else {
 lean_dec_ref(x_177);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_190 = lean_ctor_get(x_175, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_191 = x_175;
} else {
 lean_dec_ref(x_175);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 1, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_190);
return x_192;
}
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_193 = !lean_is_exclusive(x_114);
if (x_193 == 0)
{
return x_114;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_114, 0);
lean_inc(x_194);
lean_dec(x_114);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3;
x_197 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_196, x_106);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec_ref(x_197);
x_199 = lean_unbox(x_198);
lean_dec(x_198);
if (x_199 == 0)
{
lean_dec(x_110);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_200; 
x_200 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(x_110, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_110);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec_ref(x_200);
x_202 = l_Lean_MessageData_ofExpr(x_201);
x_203 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_196, x_202, x_104, x_105, x_106, x_107);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
if (lean_obj_tag(x_203) == 0)
{
lean_dec_ref(x_203);
x_13 = lean_box(0);
goto block_16;
}
else
{
return x_203;
}
}
else
{
uint8_t x_204; 
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
x_204 = !lean_is_exclusive(x_200);
if (x_204 == 0)
{
return x_200;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_200, 0);
lean_inc(x_205);
lean_dec(x_200);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_205);
return x_206;
}
}
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_207 = !lean_is_exclusive(x_109);
if (x_207 == 0)
{
return x_109;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_109, 0);
lean_inc(x_208);
lean_dec(x_109);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_208);
return x_209;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1;
x_9 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(x_8, x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_9);
x_14 = l_Lean_MessageData_ofExpr(x_1);
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofExpr(x_2);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_8, x_18, x_3, x_4, x_5, x_6);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = l_Lean_MessageData_ofExpr(x_1);
x_25 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MessageData_ofExpr(x_2);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(x_8, x_28, x_3, x_4, x_5, x_6);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_1, x_16, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_23 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_2, x_16, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc(x_26);
lean_inc(x_20);
x_27 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Grind_Linarith_Expr_norm(x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_23);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_31, 2, x_20);
lean_ctor_set(x_31, 3, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_34 = lean_box(0);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
}
else
{
lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = lean_box(0);
lean_ctor_set(x_23, 0, x_35);
return x_23;
}
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
if (lean_obj_tag(x_36) == 1)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc(x_37);
lean_inc(x_20);
x_38 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_38, 0, x_20);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Grind_Linarith_Expr_norm(x_38);
x_40 = lean_box(0);
x_41 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_2);
lean_ctor_set(x_42, 2, x_20);
lean_ctor_set(x_42, 3, x_37);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_36);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = !lean_is_exclusive(x_23);
if (x_49 == 0)
{
return x_23;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_23, 0);
lean_inc(x_50);
lean_dec(x_23);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_52 = !lean_is_exclusive(x_21);
if (x_52 == 0)
{
return x_21;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_21, 0);
lean_inc(x_53);
lean_dec(x_21);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_55 = lean_box(0);
lean_ctor_set(x_17, 0, x_55);
return x_17;
}
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_17, 0);
lean_inc(x_56);
lean_dec(x_17);
if (lean_obj_tag(x_56) == 1)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_60 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_2, x_16, x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
if (lean_obj_tag(x_61) == 1)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec_ref(x_61);
lean_inc(x_63);
lean_inc(x_57);
x_64 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Grind_Linarith_Expr_norm(x_64);
x_66 = lean_box(0);
x_67 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_62);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_2);
lean_ctor_set(x_68, 2, x_57);
lean_ctor_set(x_68, 3, x_63);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
x_70 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_57);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_62;
}
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_61);
lean_dec(x_57);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_73 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_74 = lean_alloc_ctor(0, 1, 0);
} else {
 x_74 = x_62;
}
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_57);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_75 = lean_ctor_get(x_60, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_76 = x_60;
} else {
 lean_dec_ref(x_60);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_57);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_78 = lean_ctor_get(x_58, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_79 = x_58;
} else {
 lean_dec_ref(x_58);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_56);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_83 = !lean_is_exclusive(x_17);
if (x_83 == 0)
{
return x_17;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_17, 0);
lean_inc(x_84);
lean_dec(x_17);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_86 = !lean_is_exclusive(x_14);
if (x_86 == 0)
{
return x_14;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_14, 0);
lean_inc(x_87);
lean_dec(x_14);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_2);
x_19 = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_dec(x_23);
x_24 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_27);
x_29 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_18, x_28, x_25, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; lean_object* x_33; 
lean_free_object(x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_27);
x_35 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_22, x_28, x_34, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_38);
lean_inc(x_32);
lean_ctor_set_tag(x_20, 3);
lean_ctor_set(x_20, 1, x_38);
lean_ctor_set(x_20, 0, x_32);
x_39 = l_Lean_Grind_Linarith_Expr_norm(x_20);
x_40 = lean_box(0);
x_41 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_35);
lean_inc(x_38);
lean_inc(x_32);
lean_inc(x_26);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_42 = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_2);
lean_ctor_set(x_42, 2, x_26);
lean_ctor_set(x_42, 3, x_32);
lean_ctor_set(x_42, 4, x_38);
lean_inc(x_39);
x_43 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_28);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_27);
x_44 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_43, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_44);
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_46 = l_Lean_Grind_Linarith_Poly_mul(x_39, x_45);
x_47 = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_1);
lean_ctor_set(x_47, 2, x_26);
lean_ctor_set(x_47, 3, x_38);
lean_ctor_set(x_47, 4, x_32);
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_28);
x_49 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_48, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_49;
}
else
{
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_44;
}
}
else
{
lean_object* x_50; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_50 = lean_box(0);
lean_ctor_set(x_35, 0, x_50);
return x_35;
}
}
else
{
lean_object* x_51; 
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_51 = lean_box(0);
lean_ctor_set(x_35, 0, x_51);
return x_35;
}
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_35, 0);
lean_inc(x_52);
lean_dec(x_35);
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
lean_inc(x_53);
lean_inc(x_32);
lean_ctor_set_tag(x_20, 3);
lean_ctor_set(x_20, 1, x_53);
lean_ctor_set(x_20, 0, x_32);
x_54 = l_Lean_Grind_Linarith_Expr_norm(x_20);
x_55 = lean_box(0);
x_56 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_inc(x_53);
lean_inc(x_32);
lean_inc(x_26);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_57 = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_2);
lean_ctor_set(x_57, 2, x_26);
lean_ctor_set(x_57, 3, x_32);
lean_ctor_set(x_57, 4, x_53);
lean_inc(x_54);
x_58 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_28);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_27);
x_59 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_58, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_59);
x_60 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_61 = l_Lean_Grind_Linarith_Poly_mul(x_54, x_60);
x_62 = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(x_62, 0, x_2);
lean_ctor_set(x_62, 1, x_1);
lean_ctor_set(x_62, 2, x_26);
lean_ctor_set(x_62, 3, x_53);
lean_ctor_set(x_62, 4, x_32);
x_63 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*2, x_28);
x_64 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_63, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_64;
}
else
{
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_59;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_52);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_69 = !lean_is_exclusive(x_35);
if (x_69 == 0)
{
return x_35;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_35, 0);
lean_inc(x_70);
lean_dec(x_35);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_20);
lean_dec(x_22);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_33);
if (x_72 == 0)
{
return x_33;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_33, 0);
lean_inc(x_73);
lean_dec(x_33);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_20);
lean_dec(x_22);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_75 = lean_box(0);
lean_ctor_set(x_29, 0, x_75);
return x_29;
}
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_29, 0);
lean_inc(x_76);
lean_dec(x_29);
if (lean_obj_tag(x_76) == 1)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_27);
x_80 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_22, x_28, x_79, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_obj_tag(x_81) == 1)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec_ref(x_81);
lean_inc(x_83);
lean_inc(x_77);
lean_ctor_set_tag(x_20, 3);
lean_ctor_set(x_20, 1, x_83);
lean_ctor_set(x_20, 0, x_77);
x_84 = l_Lean_Grind_Linarith_Expr_norm(x_20);
x_85 = lean_box(0);
x_86 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_82);
lean_inc(x_83);
lean_inc(x_77);
lean_inc(x_26);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_87 = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_2);
lean_ctor_set(x_87, 2, x_26);
lean_ctor_set(x_87, 3, x_77);
lean_ctor_set(x_87, 4, x_83);
lean_inc(x_84);
x_88 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*2, x_28);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_27);
x_89 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_88, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_89);
x_90 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_91 = l_Lean_Grind_Linarith_Poly_mul(x_84, x_90);
x_92 = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(x_92, 0, x_2);
lean_ctor_set(x_92, 1, x_1);
lean_ctor_set(x_92, 2, x_26);
lean_ctor_set(x_92, 3, x_83);
lean_ctor_set(x_92, 4, x_77);
x_93 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*2, x_28);
x_94 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_93, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_94;
}
else
{
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_77);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_89;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_77);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_95 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_96 = lean_alloc_ctor(0, 1, 0);
} else {
 x_96 = x_82;
}
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_81);
lean_dec(x_77);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_97 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_98 = lean_alloc_ctor(0, 1, 0);
} else {
 x_98 = x_82;
}
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_77);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_99 = lean_ctor_get(x_80, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_100 = x_80;
} else {
 lean_dec_ref(x_80);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_77);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_20);
lean_dec(x_22);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_102 = lean_ctor_get(x_78, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_103 = x_78;
} else {
 lean_dec_ref(x_78);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_102);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_76);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_20);
lean_dec(x_22);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_20);
lean_dec(x_22);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_107 = !lean_is_exclusive(x_29);
if (x_107 == 0)
{
return x_29;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_29, 0);
lean_inc(x_108);
lean_dec(x_29);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_free_object(x_20);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_110 = !lean_is_exclusive(x_24);
if (x_110 == 0)
{
return x_24;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_24, 0);
lean_inc(x_111);
lean_dec(x_24);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_20, 0);
lean_inc(x_113);
lean_dec(x_20);
x_114 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = lean_ctor_get(x_15, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_15, 1);
lean_inc(x_117);
lean_dec(x_15);
x_118 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_117);
x_119 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_18, x_118, x_115, x_117, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
if (lean_obj_tag(x_120) == 1)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_121);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec_ref(x_120);
x_123 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_117);
x_125 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_113, x_118, x_124, x_117, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
if (lean_obj_tag(x_126) == 1)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec_ref(x_126);
lean_inc(x_128);
lean_inc(x_122);
x_129 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_129, 0, x_122);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_Grind_Linarith_Expr_norm(x_129);
x_131 = lean_box(0);
x_132 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_130, x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_127);
lean_inc(x_128);
lean_inc(x_122);
lean_inc(x_116);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_133 = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(x_133, 0, x_1);
lean_ctor_set(x_133, 1, x_2);
lean_ctor_set(x_133, 2, x_116);
lean_ctor_set(x_133, 3, x_122);
lean_ctor_set(x_133, 4, x_128);
lean_inc(x_130);
x_134 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set_uint8(x_134, sizeof(void*)*2, x_118);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_117);
x_135 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_134, x_117, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec_ref(x_135);
x_136 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0;
x_137 = l_Lean_Grind_Linarith_Poly_mul(x_130, x_136);
x_138 = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(x_138, 0, x_2);
lean_ctor_set(x_138, 1, x_1);
lean_ctor_set(x_138, 2, x_116);
lean_ctor_set(x_138, 3, x_128);
lean_ctor_set(x_138, 4, x_122);
x_139 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*2, x_118);
x_140 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_139, x_117, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_140;
}
else
{
lean_dec(x_130);
lean_dec(x_128);
lean_dec(x_122);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_135;
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_130);
lean_dec(x_128);
lean_dec(x_122);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_141 = lean_box(0);
if (lean_is_scalar(x_127)) {
 x_142 = lean_alloc_ctor(0, 1, 0);
} else {
 x_142 = x_127;
}
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_126);
lean_dec(x_122);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_143 = lean_box(0);
if (lean_is_scalar(x_127)) {
 x_144 = lean_alloc_ctor(0, 1, 0);
} else {
 x_144 = x_127;
}
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_122);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_145 = lean_ctor_get(x_125, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_146 = x_125;
} else {
 lean_dec_ref(x_125);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 1, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_122);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_113);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_148 = lean_ctor_get(x_123, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_149 = x_123;
} else {
 lean_dec_ref(x_123);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_113);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_151 = lean_box(0);
if (lean_is_scalar(x_121)) {
 x_152 = lean_alloc_ctor(0, 1, 0);
} else {
 x_152 = x_121;
}
lean_ctor_set(x_152, 0, x_151);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_113);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_153 = lean_ctor_get(x_119, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_154 = x_119;
} else {
 lean_dec_ref(x_119);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_113);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_156 = lean_ctor_get(x_114, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_157 = x_114;
} else {
 lean_dec_ref(x_114);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 1, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_156);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_159 = !lean_is_exclusive(x_19);
if (x_159 == 0)
{
return x_19;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_19, 0);
lean_inc(x_160);
lean_dec(x_19);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_162 = !lean_is_exclusive(x_16);
if (x_162 == 0)
{
return x_16;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_16, 0);
lean_inc(x_163);
lean_dec(x_16);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_165 = !lean_is_exclusive(x_14);
if (x_165 == 0)
{
return x_14;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_14, 0);
lean_inc(x_166);
lean_dec(x_14);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_dec(x_20);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_2);
x_21 = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_dec(x_25);
x_26 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_dec(x_15);
x_30 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_29);
x_31 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_19, x_30, x_27, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; lean_object* x_35; 
lean_free_object(x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_29);
x_37 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_24, x_30, x_36, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
lean_inc(x_40);
lean_inc(x_34);
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 1, x_40);
lean_ctor_set(x_22, 0, x_34);
x_41 = l_Lean_Grind_Linarith_Expr_norm(x_22);
x_42 = lean_box(0);
x_43 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_free_object(x_37);
x_44 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_2);
lean_ctor_set(x_44, 2, x_28);
lean_ctor_set(x_44, 3, x_34);
lean_ctor_set(x_44, 4, x_40);
lean_ctor_set(x_17, 1, x_44);
lean_ctor_set(x_17, 0, x_41);
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(x_17, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_46 = lean_box(0);
lean_ctor_set(x_37, 0, x_46);
return x_37;
}
}
else
{
lean_object* x_47; 
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_47 = lean_box(0);
lean_ctor_set(x_37, 0, x_47);
return x_37;
}
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_37, 0);
lean_inc(x_48);
lean_dec(x_37);
if (lean_obj_tag(x_48) == 1)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
lean_inc(x_49);
lean_inc(x_34);
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 1, x_49);
lean_ctor_set(x_22, 0, x_34);
x_50 = l_Lean_Grind_Linarith_Expr_norm(x_22);
x_51 = lean_box(0);
x_52 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_2);
lean_ctor_set(x_53, 2, x_28);
lean_ctor_set(x_53, 3, x_34);
lean_ctor_set(x_53, 4, x_49);
lean_ctor_set(x_17, 1, x_53);
lean_ctor_set(x_17, 0, x_50);
x_54 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(x_17, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_48);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_37);
if (x_59 == 0)
{
return x_37;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_37, 0);
lean_inc(x_60);
lean_dec(x_37);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_22);
lean_dec(x_24);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_62 = !lean_is_exclusive(x_35);
if (x_62 == 0)
{
return x_35;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_35, 0);
lean_inc(x_63);
lean_dec(x_35);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_22);
lean_dec(x_24);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = lean_box(0);
lean_ctor_set(x_31, 0, x_65);
return x_31;
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_31, 0);
lean_inc(x_66);
lean_dec(x_31);
if (lean_obj_tag(x_66) == 1)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_29);
x_70 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_24, x_30, x_69, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec_ref(x_71);
lean_inc(x_73);
lean_inc(x_67);
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 1, x_73);
lean_ctor_set(x_22, 0, x_67);
x_74 = l_Lean_Grind_Linarith_Expr_norm(x_22);
x_75 = lean_box(0);
x_76 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_72);
x_77 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_2);
lean_ctor_set(x_77, 2, x_28);
lean_ctor_set(x_77, 3, x_67);
lean_ctor_set(x_77, 4, x_73);
lean_ctor_set(x_17, 1, x_77);
lean_ctor_set(x_17, 0, x_74);
x_78 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(x_17, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_67);
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_79 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_72;
}
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_71);
lean_dec(x_67);
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_81 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_82 = lean_alloc_ctor(0, 1, 0);
} else {
 x_82 = x_72;
}
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_67);
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_83 = lean_ctor_get(x_70, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_84 = x_70;
} else {
 lean_dec_ref(x_70);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 1, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_67);
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_22);
lean_dec(x_24);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_66);
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_22);
lean_dec(x_24);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_22);
lean_dec(x_24);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_91 = !lean_is_exclusive(x_31);
if (x_91 == 0)
{
return x_31;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_31, 0);
lean_inc(x_92);
lean_dec(x_31);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_free_object(x_22);
lean_dec(x_24);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_94 = !lean_is_exclusive(x_26);
if (x_94 == 0)
{
return x_26;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_26, 0);
lean_inc(x_95);
lean_dec(x_26);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_22, 0);
lean_inc(x_97);
lean_dec(x_22);
x_98 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = lean_ctor_get(x_15, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_15, 1);
lean_inc(x_101);
lean_dec(x_15);
x_102 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_101);
x_103 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_19, x_102, x_99, x_101, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
if (lean_obj_tag(x_104) == 1)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_105);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec_ref(x_104);
x_107 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_101);
x_109 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_97, x_102, x_108, x_101, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_obj_tag(x_110) == 1)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec_ref(x_110);
lean_inc(x_112);
lean_inc(x_106);
x_113 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_Grind_Linarith_Expr_norm(x_113);
x_115 = lean_box(0);
x_116 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_114, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_111);
x_117 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_117, 0, x_1);
lean_ctor_set(x_117, 1, x_2);
lean_ctor_set(x_117, 2, x_100);
lean_ctor_set(x_117, 3, x_106);
lean_ctor_set(x_117, 4, x_112);
lean_ctor_set(x_17, 1, x_117);
lean_ctor_set(x_17, 0, x_114);
x_118 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(x_17, x_101, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_106);
lean_dec(x_101);
lean_dec(x_100);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_119 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_120 = lean_alloc_ctor(0, 1, 0);
} else {
 x_120 = x_111;
}
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_110);
lean_dec(x_106);
lean_dec(x_101);
lean_dec(x_100);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_121 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_122 = lean_alloc_ctor(0, 1, 0);
} else {
 x_122 = x_111;
}
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_106);
lean_dec(x_101);
lean_dec(x_100);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_123 = lean_ctor_get(x_109, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_124 = x_109;
} else {
 lean_dec_ref(x_109);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_106);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_97);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_126 = lean_ctor_get(x_107, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_127 = x_107;
} else {
 lean_dec_ref(x_107);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 1, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_97);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_129 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_130 = lean_alloc_ctor(0, 1, 0);
} else {
 x_130 = x_105;
}
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_97);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_131 = lean_ctor_get(x_103, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_132 = x_103;
} else {
 lean_dec_ref(x_103);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_131);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_97);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_134 = lean_ctor_get(x_98, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_135 = x_98;
} else {
 lean_dec_ref(x_98);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_134);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_137 = !lean_is_exclusive(x_21);
if (x_137 == 0)
{
return x_21;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_21, 0);
lean_inc(x_138);
lean_dec(x_21);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_17, 0);
lean_inc(x_140);
lean_dec(x_17);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_2);
x_141 = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec_ref(x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_144 = x_142;
} else {
 lean_dec_ref(x_142);
 x_144 = lean_box(0);
}
x_145 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = lean_ctor_get(x_15, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_15, 1);
lean_inc(x_148);
lean_dec(x_15);
x_149 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_148);
x_150 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_140, x_149, x_146, x_148, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
if (lean_obj_tag(x_151) == 1)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_152);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
lean_dec_ref(x_151);
x_154 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec_ref(x_154);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_148);
x_156 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_143, x_149, x_155, x_148, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
if (lean_obj_tag(x_157) == 1)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec_ref(x_157);
lean_inc(x_159);
lean_inc(x_153);
if (lean_is_scalar(x_144)) {
 x_160 = lean_alloc_ctor(3, 2, 0);
} else {
 x_160 = x_144;
 lean_ctor_set_tag(x_160, 3);
}
lean_ctor_set(x_160, 0, x_153);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_Grind_Linarith_Expr_norm(x_160);
x_162 = lean_box(0);
x_163 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_161, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
x_164 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_164, 0, x_1);
lean_ctor_set(x_164, 1, x_2);
lean_ctor_set(x_164, 2, x_147);
lean_ctor_set(x_164, 3, x_153);
lean_ctor_set(x_164, 4, x_159);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_161);
lean_ctor_set(x_165, 1, x_164);
x_166 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(x_165, x_148, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_167 = lean_box(0);
if (lean_is_scalar(x_158)) {
 x_168 = lean_alloc_ctor(0, 1, 0);
} else {
 x_168 = x_158;
}
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_157);
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_169 = lean_box(0);
if (lean_is_scalar(x_158)) {
 x_170 = lean_alloc_ctor(0, 1, 0);
} else {
 x_170 = x_158;
}
lean_ctor_set(x_170, 0, x_169);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_171 = lean_ctor_get(x_156, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_172 = x_156;
} else {
 lean_dec_ref(x_156);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 1, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_174 = lean_ctor_get(x_154, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 x_175 = x_154;
} else {
 lean_dec_ref(x_154);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 1, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_174);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_151);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_177 = lean_box(0);
if (lean_is_scalar(x_152)) {
 x_178 = lean_alloc_ctor(0, 1, 0);
} else {
 x_178 = x_152;
}
lean_ctor_set(x_178, 0, x_177);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_179 = lean_ctor_get(x_150, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_180 = x_150;
} else {
 lean_dec_ref(x_150);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 1, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_140);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_182 = lean_ctor_get(x_145, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_183 = x_145;
} else {
 lean_dec_ref(x_145);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_140);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_185 = lean_ctor_get(x_141, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_186 = x_141;
} else {
 lean_dec_ref(x_141);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 1, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_185);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_188 = !lean_is_exclusive(x_16);
if (x_188 == 0)
{
return x_16;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_16, 0);
lean_inc(x_189);
lean_dec(x_16);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_191 = !lean_is_exclusive(x_14);
if (x_191 == 0)
{
return x_14;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_14, 0);
lean_inc(x_192);
lean_dec(x_14);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_192);
return x_193;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(x_1, x_2, x_3, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Meta_Grind_Arith_Linear_isCommRing(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
x_28 = l_Lean_Meta_Grind_Arith_Linear_isCommRing(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_17, 0);
lean_inc(x_37);
lean_dec(x_17);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_15);
x_39 = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(x_1, x_2, x_3, x_10);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_42; lean_object* x_43; 
lean_free_object(x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_ctor_get(x_44, 9);
lean_inc(x_45);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(x_1, x_2, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_46;
}
else
{
lean_object* x_47; 
lean_dec_ref(x_45);
x_47 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(x_1, x_2, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_42);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_41);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_51 = lean_box(0);
lean_ctor_set(x_39, 0, x_51);
return x_39;
}
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
lean_dec(x_39);
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_ctor_get(x_55, 9);
lean_inc(x_56);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(x_1, x_2, x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_57;
}
else
{
lean_object* x_58; 
lean_dec_ref(x_56);
x_58 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(x_1, x_2, x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_53);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_60 = x_54;
} else {
 lean_dec_ref(x_54);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_52);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_64 = !lean_is_exclusive(x_39);
if (x_64 == 0)
{
return x_39;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_39, 0);
lean_inc(x_65);
lean_dec(x_39);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_67 = !lean_is_exclusive(x_14);
if (x_67 == 0)
{
return x_14;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_14, 0);
lean_inc(x_68);
lean_dec(x_14);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_processNewEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = 0;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_box(x_14);
lean_inc_ref(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_box(x_14);
lean_inc_ref(x_2);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 3);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_inc(x_27);
lean_inc(x_21);
x_28 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Grind_CommRing_Expr_toPoly(x_28);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_21);
lean_ctor_set(x_30, 3, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_32 = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
lean_dec_ref(x_1);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
lean_dec_ref(x_2);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_66; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_ctor_get(x_33, 0);
x_66 = lean_nat_dec_le(x_35, x_37);
if (x_66 == 0)
{
lean_dec(x_37);
x_39 = x_35;
goto block_65;
}
else
{
lean_dec(x_35);
x_39 = x_37;
goto block_65;
}
block_65:
{
lean_object* x_40; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_39);
lean_inc_ref(x_38);
x_40 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_38, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_41, x_14, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
lean_inc(x_45);
x_46 = l_Lean_Grind_Linarith_Expr_norm(x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_33);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_44);
lean_dec(x_33);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = lean_box(0);
lean_ctor_set(x_42, 0, x_50);
return x_42;
}
}
else
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
if (lean_obj_tag(x_51) == 1)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
lean_inc(x_52);
x_53 = l_Lean_Grind_Linarith_Expr_norm(x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_33);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
lean_dec(x_33);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_33);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_42);
if (x_59 == 0)
{
return x_42;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_42, 0);
lean_inc(x_60);
lean_dec(x_42);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_39);
lean_dec(x_33);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_40);
if (x_62 == 0)
{
return x_40;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_40, 0);
lean_inc(x_63);
lean_dec(x_40);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_36);
if (x_67 == 0)
{
return x_36;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_36, 0);
lean_inc(x_68);
lean_dec(x_36);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_33);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_70 = !lean_is_exclusive(x_34);
if (x_70 == 0)
{
return x_34;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_34, 0);
lean_inc(x_71);
lean_dec(x_34);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_32);
if (x_73 == 0)
{
return x_32;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_32, 0);
lean_inc(x_74);
lean_dec(x_32);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_76 = lean_box(0);
lean_ctor_set(x_24, 0, x_76);
return x_24;
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_24, 0);
lean_inc(x_77);
lean_dec(x_24);
if (lean_obj_tag(x_77) == 1)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
lean_inc(x_78);
lean_inc(x_21);
x_79 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_79, 0, x_21);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Grind_CommRing_Expr_toPoly(x_79);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_81 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_2);
lean_ctor_set(x_81, 2, x_21);
lean_ctor_set(x_81, 3, x_78);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_83 = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
lean_dec_ref(x_1);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
lean_dec_ref(x_2);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_110; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_ctor_get(x_84, 0);
x_110 = lean_nat_dec_le(x_86, x_88);
if (x_110 == 0)
{
lean_dec(x_88);
x_90 = x_86;
goto block_109;
}
else
{
lean_dec(x_86);
x_90 = x_88;
goto block_109;
}
block_109:
{
lean_object* x_91; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_90);
lean_inc_ref(x_89);
x_91 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_89, x_90, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_93 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_92, x_14, x_90, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_obj_tag(x_94) == 1)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_95);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec_ref(x_94);
lean_inc(x_96);
x_97 = l_Lean_Grind_Linarith_Expr_norm(x_96);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_84);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_99, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_94);
lean_dec(x_84);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_101 = lean_box(0);
if (lean_is_scalar(x_95)) {
 x_102 = lean_alloc_ctor(0, 1, 0);
} else {
 x_102 = x_95;
}
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_84);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_103 = lean_ctor_get(x_93, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_104 = x_93;
} else {
 lean_dec_ref(x_93);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_90);
lean_dec(x_84);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_106 = lean_ctor_get(x_91, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_107 = x_91;
} else {
 lean_dec_ref(x_91);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_106);
return x_108;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = lean_ctor_get(x_87, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_112 = x_87;
} else {
 lean_dec_ref(x_87);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_84);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_114 = lean_ctor_get(x_85, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_115 = x_85;
} else {
 lean_dec_ref(x_85);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_117 = lean_ctor_get(x_83, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_118 = x_83;
} else {
 lean_dec_ref(x_83);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_77);
lean_dec(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_122 = !lean_is_exclusive(x_24);
if (x_122 == 0)
{
return x_24;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_24, 0);
lean_inc(x_123);
lean_dec(x_24);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_125 = lean_box(0);
lean_ctor_set(x_18, 0, x_125);
return x_18;
}
}
else
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_18, 0);
lean_inc(x_126);
lean_dec(x_18);
if (lean_obj_tag(x_126) == 1)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = lean_box(x_14);
lean_inc_ref(x_2);
x_129 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 3);
lean_closure_set(x_129, 0, x_2);
lean_closure_set(x_129, 1, x_128);
lean_closure_set(x_129, 2, x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_130 = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(x_129, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
if (lean_obj_tag(x_131) == 1)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_132);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_dec_ref(x_131);
lean_inc(x_133);
lean_inc(x_127);
x_134 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_134, 0, x_127);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_Grind_CommRing_Expr_toPoly(x_134);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_136 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_136, 0, x_1);
lean_ctor_set(x_136, 1, x_2);
lean_ctor_set(x_136, 2, x_127);
lean_ctor_set(x_136, 3, x_133);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_138 = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(x_137, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec_ref(x_138);
x_140 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
lean_dec_ref(x_1);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
lean_dec_ref(x_2);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_165; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = lean_ctor_get(x_139, 0);
x_165 = lean_nat_dec_le(x_141, x_143);
if (x_165 == 0)
{
lean_dec(x_143);
x_145 = x_141;
goto block_164;
}
else
{
lean_dec(x_141);
x_145 = x_143;
goto block_164;
}
block_164:
{
lean_object* x_146; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_145);
lean_inc_ref(x_144);
x_146 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_144, x_145, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_148 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_147, x_14, x_145, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_obj_tag(x_149) == 1)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_150);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
lean_dec_ref(x_149);
lean_inc(x_151);
x_152 = l_Lean_Grind_Linarith_Expr_norm(x_151);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_139);
lean_ctor_set(x_153, 1, x_151);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_154, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_149);
lean_dec(x_139);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_156 = lean_box(0);
if (lean_is_scalar(x_150)) {
 x_157 = lean_alloc_ctor(0, 1, 0);
} else {
 x_157 = x_150;
}
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_139);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_158 = lean_ctor_get(x_148, 0);
lean_inc(x_158);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_159 = x_148;
} else {
 lean_dec_ref(x_148);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_145);
lean_dec(x_139);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_161 = lean_ctor_get(x_146, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_162 = x_146;
} else {
 lean_dec_ref(x_146);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 1, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_161);
return x_163;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_166 = lean_ctor_get(x_142, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_167 = x_142;
} else {
 lean_dec_ref(x_142);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 1, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_139);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_169 = lean_ctor_get(x_140, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_170 = x_140;
} else {
 lean_dec_ref(x_140);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_169);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_172 = lean_ctor_get(x_138, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_173 = x_138;
} else {
 lean_dec_ref(x_138);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_172);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_131);
lean_dec(x_127);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_175 = lean_box(0);
if (lean_is_scalar(x_132)) {
 x_176 = lean_alloc_ctor(0, 1, 0);
} else {
 x_176 = x_132;
}
lean_ctor_set(x_176, 0, x_175);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_127);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_177 = lean_ctor_get(x_130, 0);
lean_inc(x_177);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_178 = x_130;
} else {
 lean_dec_ref(x_130);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 1, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_126);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_180);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_182 = !lean_is_exclusive(x_18);
if (x_182 == 0)
{
return x_18;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_18, 0);
lean_inc(x_183);
lean_dec(x_18);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_1, x_16, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_23 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_2, x_16, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc(x_26);
lean_inc(x_20);
x_27 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Grind_Linarith_Expr_norm(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_2);
lean_ctor_set(x_29, 2, x_20);
lean_ctor_set(x_29, 3, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = lean_box(0);
lean_ctor_set(x_23, 0, x_32);
return x_23;
}
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
lean_inc(x_34);
lean_inc(x_20);
x_35 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Grind_Linarith_Expr_norm(x_35);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_2);
lean_ctor_set(x_37, 2, x_20);
lean_ctor_set(x_37, 3, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_33);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_23, 0);
lean_inc(x_43);
lean_dec(x_23);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_21);
if (x_45 == 0)
{
return x_21;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_21, 0);
lean_inc(x_46);
lean_dec(x_21);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_48 = lean_box(0);
lean_ctor_set(x_17, 0, x_48);
return x_17;
}
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_17, 0);
lean_inc(x_49);
lean_dec(x_17);
if (lean_obj_tag(x_49) == 1)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_53 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_2, x_16, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_obj_tag(x_54) == 1)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_55);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec_ref(x_54);
lean_inc(x_56);
lean_inc(x_50);
x_57 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Grind_Linarith_Expr_norm(x_57);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_2);
lean_ctor_set(x_59, 2, x_50);
lean_ctor_set(x_59, 3, x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_62 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_63 = lean_alloc_ctor(0, 1, 0);
} else {
 x_63 = x_55;
}
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_50);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_64 = lean_ctor_get(x_53, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_65 = x_53;
} else {
 lean_dec_ref(x_53);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_50);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_67 = lean_ctor_get(x_51, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_68 = x_51;
} else {
 lean_dec_ref(x_51);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_49);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_17);
if (x_72 == 0)
{
return x_17;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_17, 0);
lean_inc(x_73);
lean_dec(x_17);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_14);
if (x_75 == 0)
{
return x_14;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_14, 0);
lean_inc(x_76);
lean_dec(x_14);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_15);
x_17 = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_20 = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_dec(x_24);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_2);
x_25 = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_dec(x_29);
x_30 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_19);
x_33 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_23, x_32, x_31, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_19);
x_39 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_28, x_32, x_38, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
lean_inc(x_42);
lean_inc(x_36);
lean_ctor_set_tag(x_26, 3);
lean_ctor_set(x_26, 1, x_42);
lean_ctor_set(x_26, 0, x_36);
x_43 = l_Lean_Grind_Linarith_Expr_norm(x_26);
x_44 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_2);
lean_ctor_set(x_44, 2, x_18);
lean_ctor_set(x_44, 3, x_36);
lean_ctor_set(x_44, 4, x_42);
lean_ctor_set(x_21, 1, x_44);
lean_ctor_set(x_21, 0, x_43);
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_21, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_41);
lean_dec(x_36);
lean_free_object(x_26);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_46 = lean_box(0);
lean_ctor_set(x_39, 0, x_46);
return x_39;
}
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
lean_dec(x_39);
if (lean_obj_tag(x_47) == 1)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_inc(x_48);
lean_inc(x_36);
lean_ctor_set_tag(x_26, 3);
lean_ctor_set(x_26, 1, x_48);
lean_ctor_set(x_26, 0, x_36);
x_49 = l_Lean_Grind_Linarith_Expr_norm(x_26);
x_50 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_2);
lean_ctor_set(x_50, 2, x_18);
lean_ctor_set(x_50, 3, x_36);
lean_ctor_set(x_50, 4, x_48);
lean_ctor_set(x_21, 1, x_50);
lean_ctor_set(x_21, 0, x_49);
x_51 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_21, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_47);
lean_dec(x_36);
lean_free_object(x_26);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_36);
lean_free_object(x_26);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_39);
if (x_54 == 0)
{
return x_39;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_39, 0);
lean_inc(x_55);
lean_dec(x_39);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_36);
lean_free_object(x_26);
lean_dec(x_28);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_37);
if (x_57 == 0)
{
return x_37;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_37, 0);
lean_inc(x_58);
lean_dec(x_37);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; 
lean_dec(x_35);
lean_free_object(x_26);
lean_dec(x_28);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_60 = lean_box(0);
lean_ctor_set(x_33, 0, x_60);
return x_33;
}
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_33, 0);
lean_inc(x_61);
lean_dec(x_33);
if (lean_obj_tag(x_61) == 1)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_19);
x_65 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_28, x_32, x_64, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_obj_tag(x_66) == 1)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec_ref(x_66);
lean_inc(x_68);
lean_inc(x_62);
lean_ctor_set_tag(x_26, 3);
lean_ctor_set(x_26, 1, x_68);
lean_ctor_set(x_26, 0, x_62);
x_69 = l_Lean_Grind_Linarith_Expr_norm(x_26);
x_70 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_2);
lean_ctor_set(x_70, 2, x_18);
lean_ctor_set(x_70, 3, x_62);
lean_ctor_set(x_70, 4, x_68);
lean_ctor_set(x_21, 1, x_70);
lean_ctor_set(x_21, 0, x_69);
x_71 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_21, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_66);
lean_dec(x_62);
lean_free_object(x_26);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_72 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_73 = lean_alloc_ctor(0, 1, 0);
} else {
 x_73 = x_67;
}
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_62);
lean_free_object(x_26);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_74 = lean_ctor_get(x_65, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_62);
lean_free_object(x_26);
lean_dec(x_28);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_77 = lean_ctor_get(x_63, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_78 = x_63;
} else {
 lean_dec_ref(x_63);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_61);
lean_free_object(x_26);
lean_dec(x_28);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_free_object(x_26);
lean_dec(x_28);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_82 = !lean_is_exclusive(x_33);
if (x_82 == 0)
{
return x_33;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_33, 0);
lean_inc(x_83);
lean_dec(x_33);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_free_object(x_26);
lean_dec(x_28);
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_85 = !lean_is_exclusive(x_30);
if (x_85 == 0)
{
return x_30;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_30, 0);
lean_inc(x_86);
lean_dec(x_30);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_26, 0);
lean_inc(x_88);
lean_dec(x_26);
x_89 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_19);
x_92 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_23, x_91, x_90, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
if (lean_obj_tag(x_93) == 1)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_94);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec_ref(x_93);
x_96 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_19);
x_98 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_88, x_91, x_97, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
if (lean_obj_tag(x_99) == 1)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_100);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec_ref(x_99);
lean_inc(x_101);
lean_inc(x_95);
x_102 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_102, 0, x_95);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Grind_Linarith_Expr_norm(x_102);
x_104 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_2);
lean_ctor_set(x_104, 2, x_18);
lean_ctor_set(x_104, 3, x_95);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set(x_21, 1, x_104);
lean_ctor_set(x_21, 0, x_103);
x_105 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_21, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_99);
lean_dec(x_95);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_106 = lean_box(0);
if (lean_is_scalar(x_100)) {
 x_107 = lean_alloc_ctor(0, 1, 0);
} else {
 x_107 = x_100;
}
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_95);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_108 = lean_ctor_get(x_98, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_109 = x_98;
} else {
 lean_dec_ref(x_98);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_95);
lean_dec(x_88);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_111 = lean_ctor_get(x_96, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 x_112 = x_96;
} else {
 lean_dec_ref(x_96);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_93);
lean_dec(x_88);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_114 = lean_box(0);
if (lean_is_scalar(x_94)) {
 x_115 = lean_alloc_ctor(0, 1, 0);
} else {
 x_115 = x_94;
}
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_88);
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_116 = lean_ctor_get(x_92, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_117 = x_92;
} else {
 lean_dec_ref(x_92);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_116);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_88);
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_119 = lean_ctor_get(x_89, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_120 = x_89;
} else {
 lean_dec_ref(x_89);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 1, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_119);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_122 = !lean_is_exclusive(x_25);
if (x_122 == 0)
{
return x_25;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_25, 0);
lean_inc(x_123);
lean_dec(x_25);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_21, 0);
lean_inc(x_125);
lean_dec(x_21);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_2);
x_126 = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_129 = x_127;
} else {
 lean_dec_ref(x_127);
 x_129 = lean_box(0);
}
x_130 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_19);
x_133 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_125, x_132, x_131, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
if (lean_obj_tag(x_134) == 1)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_135);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec_ref(x_134);
x_137 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_19);
x_139 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_128, x_132, x_138, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 x_141 = x_139;
} else {
 lean_dec_ref(x_139);
 x_141 = lean_box(0);
}
if (lean_obj_tag(x_140) == 1)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_141);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec_ref(x_140);
lean_inc(x_142);
lean_inc(x_136);
if (lean_is_scalar(x_129)) {
 x_143 = lean_alloc_ctor(3, 2, 0);
} else {
 x_143 = x_129;
 lean_ctor_set_tag(x_143, 3);
}
lean_ctor_set(x_143, 0, x_136);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_Grind_Linarith_Expr_norm(x_143);
x_145 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_145, 0, x_1);
lean_ctor_set(x_145, 1, x_2);
lean_ctor_set(x_145, 2, x_18);
lean_ctor_set(x_145, 3, x_136);
lean_ctor_set(x_145, 4, x_142);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_146, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_140);
lean_dec(x_136);
lean_dec(x_129);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_148 = lean_box(0);
if (lean_is_scalar(x_141)) {
 x_149 = lean_alloc_ctor(0, 1, 0);
} else {
 x_149 = x_141;
}
lean_ctor_set(x_149, 0, x_148);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_136);
lean_dec(x_129);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_150 = lean_ctor_get(x_139, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 x_151 = x_139;
} else {
 lean_dec_ref(x_139);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 1, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_136);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_153 = lean_ctor_get(x_137, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_154 = x_137;
} else {
 lean_dec_ref(x_137);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_134);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_156 = lean_box(0);
if (lean_is_scalar(x_135)) {
 x_157 = lean_alloc_ctor(0, 1, 0);
} else {
 x_157 = x_135;
}
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_158 = lean_ctor_get(x_133, 0);
lean_inc(x_158);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_159 = x_133;
} else {
 lean_dec_ref(x_133);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_125);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_161 = lean_ctor_get(x_130, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_162 = x_130;
} else {
 lean_dec_ref(x_130);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 1, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_161);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_125);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_164 = lean_ctor_get(x_126, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 x_165 = x_126;
} else {
 lean_dec_ref(x_126);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_164);
return x_166;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_167 = !lean_is_exclusive(x_20);
if (x_167 == 0)
{
return x_20;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_20, 0);
lean_inc(x_168);
lean_dec(x_20);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
return x_169;
}
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_170 = !lean_is_exclusive(x_14);
if (x_170 == 0)
{
return x_14;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_14, 0);
lean_inc(x_171);
lean_dec(x_14);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(x_1, x_2, x_3, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Meta_Grind_Arith_Linear_isCommRing(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(x_1, x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(x_1, x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_14);
x_24 = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(x_1, x_2, x_3, x_10);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(x_1, x_2, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = lean_box(0);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(x_1, x_2, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
return x_13;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_13, 0);
lean_inc(x_39);
lean_dec(x_13);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__0 = _init_l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__0);
l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__1 = _init_l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg___closed__1);
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__0 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__0();
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__1 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__1);
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__2 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0);
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
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0 = _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3);
l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0 = _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__0);
l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2);
l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5);
l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0);
l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1);
l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0);
l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__0);
l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0 = _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1 = _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2 = _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2);
l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3 = _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__4 = _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4);
l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0 = _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1 = _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2 = _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2);
l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3 = _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__4 = _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

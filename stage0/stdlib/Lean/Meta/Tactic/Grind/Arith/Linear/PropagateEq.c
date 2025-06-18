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
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__4;
lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__3___lambda__1(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__1;
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__6;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__2___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__3___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__1;
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1;
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__11;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__4;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__2;
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__5;
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1;
lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrdered(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
static lean_object* l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEqImpl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_process_linarith_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__8;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_process_linarith_diseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__1;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__2;
lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_506_(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__2;
lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEqImpl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___closed__1;
uint8_t l_Lean_Meta_Grind_isSameExpr_unsafe__1(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedIndexSet;
lean_object* l_Lean_Grind_Linarith_Poly_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEqImpl___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEqImpl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__4;
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__2;
lean_object* l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__2;
lean_object* l_Lean_Grind_Linarith_Poly_coeff(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Expr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___boxed(lean_object**);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_toIntModuleExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_combine_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__5;
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = l_Lean_Level_succ___override(x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___closed__2;
x_21 = l_Lean_Expr_const___override(x_20, x_19);
x_22 = lean_ctor_get(x_15, 2);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l_Lean_mkApp3(x_21, x_22, x_1, x_2);
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
x_26 = lean_ctor_get(x_24, 3);
lean_inc(x_26);
x_27 = l_Lean_Level_succ___override(x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___closed__2;
x_31 = l_Lean_Expr_const___override(x_30, x_29);
x_32 = lean_ctor_get(x_24, 2);
lean_inc(x_32);
lean_dec(x_24);
x_33 = l_Lean_mkApp3(x_31, x_32, x_1, x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__5(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 16);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2(x_14, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
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
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linarith", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__11() {
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
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
lean_dec(x_12);
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
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = l_Lean_Grind_Linarith_Poly_coeff(x_29, x_27);
x_31 = lean_int_neg(x_30);
lean_inc(x_1);
x_32 = l_Lean_Grind_Linarith_Poly_mul(x_1, x_31);
lean_dec(x_31);
x_33 = l_Lean_Grind_Linarith_Poly_mul(x_29, x_24);
x_34 = lean_unsigned_to_nat(100000000u);
x_35 = l_Lean_Grind_Linarith_Poly_combine_x27(x_34, x_32, x_33);
x_36 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_37 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_30);
lean_free_object(x_22);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_1);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_box(0);
x_42 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___lambda__1(x_28, x_35, x_27, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 1);
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
x_46 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
lean_dec(x_1);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__5(x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_105; uint8_t x_106; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_MessageData_ofExpr(x_47);
x_59 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_58);
lean_ctor_set(x_37, 0, x_59);
x_60 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_60);
lean_ctor_set(x_22, 0, x_37);
x_61 = l_Lean_MessageData_ofExpr(x_50);
x_62 = l_Lean_MessageData_ofExpr(x_53);
x_63 = l_Lean_MessageData_ofExpr(x_56);
x_105 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_106 = lean_int_dec_lt(x_24, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_nat_abs(x_24);
lean_dec(x_24);
x_108 = l_Nat_reprFast(x_107);
x_64 = x_108;
goto block_104;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_nat_abs(x_24);
lean_dec(x_24);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_sub(x_109, x_110);
lean_dec(x_109);
x_112 = lean_nat_add(x_111, x_110);
lean_dec(x_111);
x_113 = l_Nat_reprFast(x_112);
x_114 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__11;
x_115 = lean_string_append(x_114, x_113);
lean_dec(x_113);
x_64 = x_115;
goto block_104;
}
block_104:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
if (lean_is_scalar(x_21)) {
 x_65 = lean_alloc_ctor(3, 1, 0);
} else {
 x_65 = x_21;
 lean_ctor_set_tag(x_65, 3);
}
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Lean_MessageData_ofFormat(x_65);
if (lean_is_scalar(x_25)) {
 x_67 = lean_alloc_ctor(7, 2, 0);
} else {
 x_67 = x_25;
 lean_ctor_set_tag(x_67, 7);
}
lean_ctor_set(x_67, 0, x_22);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_60);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_61);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_60);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_62);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_60);
x_73 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_74 = lean_int_dec_lt(x_30, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_nat_abs(x_30);
lean_dec(x_30);
x_76 = l_Nat_reprFast(x_75);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = l_Lean_MessageData_ofFormat(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_60);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_63);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_59);
x_83 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_36, x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___lambda__1(x_28, x_35, x_27, x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_85);
lean_dec(x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_87 = lean_nat_abs(x_30);
lean_dec(x_30);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_sub(x_87, x_88);
lean_dec(x_87);
x_90 = lean_nat_add(x_89, x_88);
lean_dec(x_89);
x_91 = l_Nat_reprFast(x_90);
x_92 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__11;
x_93 = lean_string_append(x_92, x_91);
lean_dec(x_91);
x_94 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = l_Lean_MessageData_ofFormat(x_94);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_72);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_60);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_63);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_59);
x_100 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_36, x_99, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___lambda__1(x_28, x_35, x_27, x_101, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_102);
lean_dec(x_101);
return x_103;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_47);
lean_free_object(x_37);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_116 = !lean_is_exclusive(x_55);
if (x_116 == 0)
{
return x_55;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_55, 0);
x_118 = lean_ctor_get(x_55, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_55);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_50);
lean_dec(x_47);
lean_free_object(x_37);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_120 = !lean_is_exclusive(x_52);
if (x_120 == 0)
{
return x_52;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_52, 0);
x_122 = lean_ctor_get(x_52, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_52);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_47);
lean_free_object(x_37);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_124 = !lean_is_exclusive(x_49);
if (x_124 == 0)
{
return x_49;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_49, 0);
x_126 = lean_ctor_get(x_49, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_49);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_free_object(x_37);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_128 = !lean_is_exclusive(x_46);
if (x_128 == 0)
{
return x_46;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_46, 0);
x_130 = lean_ctor_get(x_46, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_46);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_37, 1);
lean_inc(x_132);
lean_dec(x_37);
x_133 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_132);
lean_dec(x_1);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__5(x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_193; uint8_t x_194; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = l_Lean_MessageData_ofExpr(x_134);
x_146 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_148 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_148);
lean_ctor_set(x_22, 0, x_147);
x_149 = l_Lean_MessageData_ofExpr(x_137);
x_150 = l_Lean_MessageData_ofExpr(x_140);
x_151 = l_Lean_MessageData_ofExpr(x_143);
x_193 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_194 = lean_int_dec_lt(x_24, x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_nat_abs(x_24);
lean_dec(x_24);
x_196 = l_Nat_reprFast(x_195);
x_152 = x_196;
goto block_192;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_197 = lean_nat_abs(x_24);
lean_dec(x_24);
x_198 = lean_unsigned_to_nat(1u);
x_199 = lean_nat_sub(x_197, x_198);
lean_dec(x_197);
x_200 = lean_nat_add(x_199, x_198);
lean_dec(x_199);
x_201 = l_Nat_reprFast(x_200);
x_202 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__11;
x_203 = lean_string_append(x_202, x_201);
lean_dec(x_201);
x_152 = x_203;
goto block_192;
}
block_192:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
if (lean_is_scalar(x_21)) {
 x_153 = lean_alloc_ctor(3, 1, 0);
} else {
 x_153 = x_21;
 lean_ctor_set_tag(x_153, 3);
}
lean_ctor_set(x_153, 0, x_152);
x_154 = l_Lean_MessageData_ofFormat(x_153);
if (lean_is_scalar(x_25)) {
 x_155 = lean_alloc_ctor(7, 2, 0);
} else {
 x_155 = x_25;
 lean_ctor_set_tag(x_155, 7);
}
lean_ctor_set(x_155, 0, x_22);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_148);
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_149);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_148);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_150);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_148);
x_161 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_162 = lean_int_dec_lt(x_30, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_163 = lean_nat_abs(x_30);
lean_dec(x_30);
x_164 = l_Nat_reprFast(x_163);
x_165 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = l_Lean_MessageData_ofFormat(x_165);
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_160);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_148);
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_151);
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_146);
x_171 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_36, x_170, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_144);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___lambda__1(x_28, x_35, x_27, x_172, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_173);
lean_dec(x_172);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_175 = lean_nat_abs(x_30);
lean_dec(x_30);
x_176 = lean_unsigned_to_nat(1u);
x_177 = lean_nat_sub(x_175, x_176);
lean_dec(x_175);
x_178 = lean_nat_add(x_177, x_176);
lean_dec(x_177);
x_179 = l_Nat_reprFast(x_178);
x_180 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__11;
x_181 = lean_string_append(x_180, x_179);
lean_dec(x_179);
x_182 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_182, 0, x_181);
x_183 = l_Lean_MessageData_ofFormat(x_182);
x_184 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_184, 0, x_160);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_148);
x_186 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_151);
x_187 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_146);
x_188 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_36, x_187, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_144);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___lambda__1(x_28, x_35, x_27, x_189, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_190);
lean_dec(x_189);
return x_191;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_140);
lean_dec(x_137);
lean_dec(x_134);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_204 = lean_ctor_get(x_142, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_142, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_206 = x_142;
} else {
 lean_dec_ref(x_142);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_137);
lean_dec(x_134);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_208 = lean_ctor_get(x_139, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_139, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_210 = x_139;
} else {
 lean_dec_ref(x_139);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_134);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_212 = lean_ctor_get(x_136, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_136, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_214 = x_136;
} else {
 lean_dec_ref(x_136);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_216 = lean_ctor_get(x_133, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_133, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_218 = x_133;
} else {
 lean_dec_ref(x_133);
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
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_220 = lean_ctor_get(x_22, 0);
x_221 = lean_ctor_get(x_22, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_22);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = l_Lean_Grind_Linarith_Poly_coeff(x_222, x_220);
x_224 = lean_int_neg(x_223);
lean_inc(x_1);
x_225 = l_Lean_Grind_Linarith_Poly_mul(x_1, x_224);
lean_dec(x_224);
x_226 = l_Lean_Grind_Linarith_Poly_mul(x_222, x_24);
x_227 = lean_unsigned_to_nat(100000000u);
x_228 = l_Lean_Grind_Linarith_Poly_combine_x27(x_227, x_225, x_226);
x_229 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_230 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_229, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_unbox(x_231);
lean_dec(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_223);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_1);
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec(x_230);
x_234 = lean_box(0);
x_235 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___lambda__1(x_221, x_228, x_220, x_234, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_233);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_230, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_237 = x_230;
} else {
 lean_dec_ref(x_230);
 x_237 = lean_box(0);
}
x_238 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_236);
lean_dec(x_1);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_220, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_221, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__5(x_228, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_246);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_299; uint8_t x_300; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = l_Lean_MessageData_ofExpr(x_239);
x_251 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
if (lean_is_scalar(x_237)) {
 x_252 = lean_alloc_ctor(7, 2, 0);
} else {
 x_252 = x_237;
 lean_ctor_set_tag(x_252, 7);
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
x_253 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = l_Lean_MessageData_ofExpr(x_242);
x_256 = l_Lean_MessageData_ofExpr(x_245);
x_257 = l_Lean_MessageData_ofExpr(x_248);
x_299 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_300 = lean_int_dec_lt(x_24, x_299);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_nat_abs(x_24);
lean_dec(x_24);
x_302 = l_Nat_reprFast(x_301);
x_258 = x_302;
goto block_298;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_303 = lean_nat_abs(x_24);
lean_dec(x_24);
x_304 = lean_unsigned_to_nat(1u);
x_305 = lean_nat_sub(x_303, x_304);
lean_dec(x_303);
x_306 = lean_nat_add(x_305, x_304);
lean_dec(x_305);
x_307 = l_Nat_reprFast(x_306);
x_308 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__11;
x_309 = lean_string_append(x_308, x_307);
lean_dec(x_307);
x_258 = x_309;
goto block_298;
}
block_298:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
if (lean_is_scalar(x_21)) {
 x_259 = lean_alloc_ctor(3, 1, 0);
} else {
 x_259 = x_21;
 lean_ctor_set_tag(x_259, 3);
}
lean_ctor_set(x_259, 0, x_258);
x_260 = l_Lean_MessageData_ofFormat(x_259);
if (lean_is_scalar(x_25)) {
 x_261 = lean_alloc_ctor(7, 2, 0);
} else {
 x_261 = x_25;
 lean_ctor_set_tag(x_261, 7);
}
lean_ctor_set(x_261, 0, x_254);
lean_ctor_set(x_261, 1, x_260);
x_262 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_253);
x_263 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_255);
x_264 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_253);
x_265 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_256);
x_266 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_253);
x_267 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_268 = lean_int_dec_lt(x_223, x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_269 = lean_nat_abs(x_223);
lean_dec(x_223);
x_270 = l_Nat_reprFast(x_269);
x_271 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_271, 0, x_270);
x_272 = l_Lean_MessageData_ofFormat(x_271);
x_273 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_273, 0, x_266);
lean_ctor_set(x_273, 1, x_272);
x_274 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_253);
x_275 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_257);
x_276 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_251);
x_277 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_229, x_276, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_249);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___lambda__1(x_221, x_228, x_220, x_278, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_279);
lean_dec(x_278);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_281 = lean_nat_abs(x_223);
lean_dec(x_223);
x_282 = lean_unsigned_to_nat(1u);
x_283 = lean_nat_sub(x_281, x_282);
lean_dec(x_281);
x_284 = lean_nat_add(x_283, x_282);
lean_dec(x_283);
x_285 = l_Nat_reprFast(x_284);
x_286 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__11;
x_287 = lean_string_append(x_286, x_285);
lean_dec(x_285);
x_288 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_288, 0, x_287);
x_289 = l_Lean_MessageData_ofFormat(x_288);
x_290 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_290, 0, x_266);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_253);
x_292 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_257);
x_293 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_251);
x_294 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_229, x_293, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_249);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
x_297 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___lambda__1(x_221, x_228, x_220, x_295, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_296);
lean_dec(x_295);
return x_297;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_245);
lean_dec(x_242);
lean_dec(x_239);
lean_dec(x_237);
lean_dec(x_228);
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_310 = lean_ctor_get(x_247, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_247, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_312 = x_247;
} else {
 lean_dec_ref(x_247);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_242);
lean_dec(x_239);
lean_dec(x_237);
lean_dec(x_228);
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_314 = lean_ctor_get(x_244, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_244, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_316 = x_244;
} else {
 lean_dec_ref(x_244);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_239);
lean_dec(x_237);
lean_dec(x_228);
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_318 = lean_ctor_get(x_241, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_241, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_320 = x_241;
} else {
 lean_dec_ref(x_241);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_319);
return x_321;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_237);
lean_dec(x_228);
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_322 = lean_ctor_get(x_238, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_238, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_324 = x_238;
} else {
 lean_dec_ref(x_238);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 2, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
}
}
}
else
{
uint8_t x_326; 
lean_dec(x_1);
x_326 = !lean_is_exclusive(x_12);
if (x_326 == 0)
{
return x_12;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_12, 0);
x_328 = lean_ctor_get(x_12, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_12);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = l_Lean_Grind_Linarith_Poly_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__5(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 16);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2(x_14, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
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
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
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
lean_dec(x_14);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_int_emod(x_3, x_4);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_20 = lean_int_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_21, 0);
lean_dec(x_31);
x_32 = l_Lean_Grind_Linarith_Poly_mul(x_16, x_3);
x_33 = lean_int_neg(x_4);
x_34 = l_Lean_Grind_Linarith_Poly_mul(x_17, x_33);
x_35 = lean_unsigned_to_nat(100000000u);
x_36 = l_Lean_Grind_Linarith_Poly_combine_x27(x_35, x_32, x_34);
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_1);
lean_ctor_set(x_37, 3, x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_21, 0, x_39);
return x_21;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = l_Lean_Grind_Linarith_Poly_mul(x_16, x_3);
x_42 = lean_int_neg(x_4);
x_43 = l_Lean_Grind_Linarith_Poly_mul(x_17, x_42);
x_44 = lean_unsigned_to_nat(100000000u);
x_45 = l_Lean_Grind_Linarith_Poly_combine_x27(x_44, x_41, x_43);
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_3);
lean_ctor_set(x_46, 2, x_1);
lean_ctor_set(x_46, 3, x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_21);
if (x_50 == 0)
{
return x_21;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_21, 0);
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_21);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_int_neg(x_3);
lean_dec(x_3);
x_55 = lean_int_ediv(x_54, x_4);
lean_dec(x_54);
x_56 = l_Lean_Grind_Linarith_Poly_mul(x_16, x_55);
x_57 = lean_unsigned_to_nat(100000000u);
x_58 = l_Lean_Grind_Linarith_Poly_combine_x27(x_57, x_56, x_17);
x_59 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_1);
lean_ctor_set(x_59, 2, x_2);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_15);
return x_62;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1;
x_17 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___lambda__1(x_3, x_5, x_4, x_1, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_20);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 1);
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_MessageData_ofExpr(x_27);
x_36 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_35);
lean_ctor_set(x_17, 0, x_36);
x_37 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_MessageData_ofExpr(x_30);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
x_42 = l_Lean_MessageData_ofExpr(x_33);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_36);
x_45 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_16, x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_34);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___lambda__1(x_3, x_5, x_4, x_1, x_46, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_47);
lean_dec(x_46);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_30);
lean_dec(x_27);
lean_free_object(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_32);
if (x_49 == 0)
{
return x_32;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_32, 0);
x_51 = lean_ctor_get(x_32, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_32);
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
lean_dec(x_27);
lean_free_object(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_29);
if (x_53 == 0)
{
return x_29;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_29, 0);
x_55 = lean_ctor_get(x_29, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_29);
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
lean_free_object(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_26);
if (x_57 == 0)
{
return x_26;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_26, 0);
x_59 = lean_ctor_get(x_26, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_26);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_17, 1);
lean_inc(x_61);
lean_dec(x_17);
x_62 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_MessageData_ofExpr(x_63);
x_72 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_MessageData_ofExpr(x_66);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
x_79 = l_Lean_MessageData_ofExpr(x_69);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_72);
x_82 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_16, x_81, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_70);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___lambda__1(x_3, x_5, x_4, x_1, x_83, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_84);
lean_dec(x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_86 = lean_ctor_get(x_68, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_68, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_88 = x_68;
} else {
 lean_dec_ref(x_68);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_63);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_90 = lean_ctor_get(x_65, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_65, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_92 = x_65;
} else {
 lean_dec_ref(x_65);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_94 = lean_ctor_get(x_62, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_62, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_96 = x_62;
} else {
 lean_dec_ref(x_62);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_22, 1);
x_32 = lean_ctor_get(x_22, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_nat_dec_eq(x_21, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_21);
x_35 = lean_box(0);
lean_ctor_set(x_22, 0, x_35);
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_22);
x_36 = lean_box(0);
x_37 = l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___lambda__1(x_21, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_ctor_get(x_23, 0);
lean_inc(x_39);
lean_dec(x_23);
x_40 = lean_nat_dec_eq(x_21, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_21);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_box(0);
x_44 = l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___lambda__1(x_21, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
return x_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__1;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = lean_alloc_ctor(10, 6, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_3);
lean_ctor_set(x_20, 3, x_4);
lean_ctor_set(x_20, 4, x_5);
lean_ctor_set(x_20, 5, x_6);
x_21 = 0;
lean_inc(x_7);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_23 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__2;
x_26 = l_Lean_Grind_Linarith_Poly_mul(x_7, x_25);
x_27 = l_Lean_Grind_CommRing_Poly_mulConst(x_25, x_5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_27);
x_28 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_27, x_8, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_31 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_29, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_alloc_ctor(10, 6, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_1);
lean_ctor_set(x_41, 2, x_4);
lean_ctor_set(x_41, 3, x_3);
lean_ctor_set(x_41, 4, x_27);
lean_ctor_set(x_41, 5, x_40);
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_26);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_21);
x_43 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_42, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_39);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_28);
if (x_48 == 0)
{
return x_28;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_28, 0);
x_50 = lean_ctor_get(x_28, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_28);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_23);
if (x_52 == 0)
{
return x_23;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_23, 0);
x_54 = lean_ctor_get(x_23, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_23);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = lean_box(x_13);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 12, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Meta_Grind_Arith_Linear_withRingM___rarg(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_11);
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
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_box(x_13);
lean_inc(x_2);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 12, 2);
lean_closure_set(x_27, 0, x_2);
lean_closure_set(x_27, 1, x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Meta_Grind_Arith_Linear_withRingM___rarg(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_25);
lean_dec(x_11);
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
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = l_Lean_Meta_Grind_getGeneration(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Grind_getGeneration(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_nat_dec_le(x_39, x_43);
lean_inc(x_37);
lean_inc(x_25);
lean_ctor_set_tag(x_41, 4);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 0, x_25);
x_46 = l_Lean_Grind_CommRing_Expr_toPoly(x_41);
if (x_45 == 0)
{
lean_dec(x_43);
x_47 = x_39;
goto block_86;
}
else
{
lean_dec(x_39);
x_47 = x_43;
goto block_86;
}
block_86:
{
lean_object* x_48; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_47);
lean_inc(x_46);
x_48 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_46, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
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
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
lean_dec(x_52);
x_63 = l_Lean_Grind_Linarith_Expr_norm(x_62);
x_64 = lean_box(0);
x_65 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_506_(x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_free_object(x_51);
x_66 = lean_box(0);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1(x_1, x_2, x_25, x_37, x_46, x_62, x_63, x_47, x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_60);
return x_67;
}
else
{
lean_object* x_68; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_68 = lean_box(0);
lean_ctor_set(x_51, 0, x_68);
return x_51;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_51, 1);
lean_inc(x_69);
lean_dec(x_51);
x_70 = lean_ctor_get(x_52, 0);
lean_inc(x_70);
lean_dec(x_52);
x_71 = l_Lean_Grind_Linarith_Expr_norm(x_70);
x_72 = lean_box(0);
x_73 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_506_(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_box(0);
x_75 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1(x_1, x_2, x_25, x_37, x_46, x_70, x_71, x_47, x_74, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_69);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_69);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_78 = !lean_is_exclusive(x_51);
if (x_78 == 0)
{
return x_51;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_51, 0);
x_80 = lean_ctor_get(x_51, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_51);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_82 = !lean_is_exclusive(x_48);
if (x_82 == 0)
{
return x_48;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_48, 0);
x_84 = lean_ctor_get(x_48, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_48);
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
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_41, 0);
x_88 = lean_ctor_get(x_41, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_41);
x_89 = lean_nat_dec_le(x_39, x_87);
lean_inc(x_37);
lean_inc(x_25);
x_90 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_90, 0, x_25);
lean_ctor_set(x_90, 1, x_37);
x_91 = l_Lean_Grind_CommRing_Expr_toPoly(x_90);
if (x_89 == 0)
{
lean_dec(x_87);
x_92 = x_39;
goto block_120;
}
else
{
lean_dec(x_39);
x_92 = x_87;
goto block_120;
}
block_120:
{
lean_object* x_93; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_92);
lean_inc(x_91);
x_93 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_91, x_92, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_88);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_96 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_94, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
x_100 = lean_box(0);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_103 = x_96;
} else {
 lean_dec_ref(x_96);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_97, 0);
lean_inc(x_104);
lean_dec(x_97);
x_105 = l_Lean_Grind_Linarith_Expr_norm(x_104);
x_106 = lean_box(0);
x_107 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_506_(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_103);
x_108 = lean_box(0);
x_109 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1(x_1, x_2, x_25, x_37, x_91, x_104, x_105, x_92, x_108, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_102);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_110 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_103;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_102);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_112 = lean_ctor_get(x_96, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_96, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_114 = x_96;
} else {
 lean_dec_ref(x_96);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_116 = lean_ctor_get(x_93, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_93, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_118 = x_93;
} else {
 lean_dec_ref(x_93);
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
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_25);
lean_dec(x_11);
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
x_121 = !lean_is_exclusive(x_28);
if (x_121 == 0)
{
return x_28;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_28, 0);
x_123 = lean_ctor_get(x_28, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_28);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_11);
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
x_125 = !lean_is_exclusive(x_16);
if (x_125 == 0)
{
return x_16;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_16, 0);
x_127 = lean_ctor_get(x_16, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_16);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___boxed(lean_object** _args) {
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
lean_object* x_20; 
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_9);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_4);
x_18 = 0;
lean_inc(x_5);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__2;
x_23 = l_Lean_Grind_Linarith_Poly_mul(x_5, x_22);
x_24 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_1);
lean_ctor_set(x_24, 2, x_4);
lean_ctor_set(x_24, 3, x_3);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_18);
x_26 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
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
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
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
lean_dec(x_25);
lean_inc(x_35);
lean_inc(x_23);
x_36 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Grind_Linarith_Expr_norm(x_36);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_506_(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_free_object(x_24);
x_40 = lean_box(0);
x_41 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___lambda__1(x_1, x_2, x_23, x_35, x_37, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_33);
return x_41;
}
else
{
lean_object* x_42; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_11);
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
x_42 = lean_box(0);
lean_ctor_set(x_24, 0, x_42);
return x_24;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_24, 1);
lean_inc(x_43);
lean_dec(x_24);
x_44 = lean_ctor_get(x_25, 0);
lean_inc(x_44);
lean_dec(x_25);
lean_inc(x_44);
lean_inc(x_23);
x_45 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_45, 0, x_23);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Grind_Linarith_Expr_norm(x_45);
lean_dec(x_45);
x_47 = lean_box(0);
x_48 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_506_(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___lambda__1(x_1, x_2, x_23, x_44, x_46, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_23);
lean_dec(x_11);
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
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_23);
lean_dec(x_11);
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
x_53 = !lean_is_exclusive(x_24);
if (x_53 == 0)
{
return x_24;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_24, 0);
x_55 = lean_ctor_get(x_24, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_24);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_11);
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
x_57 = !lean_is_exclusive(x_14);
if (x_57 == 0)
{
return x_14;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_14, 0);
x_59 = lean_ctor_get(x_14, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_14);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
return x_17;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__2;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__3;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instInhabitedNat;
x_2 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instInhabitedNat;
x_2 = l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__4;
x_2 = l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__6;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__7;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__8;
x_13 = lean_panic_fn(x_12, x_1);
x_14 = lean_apply_10(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_nat_abs(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Linear.EqCnstr.norm", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__2;
x_3 = lean_unsigned_to_nat(86u);
x_4 = lean_unsigned_to_nat(42u);
x_5 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__3;
x_6 = l_mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_inc(x_13);
x_14 = l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_1);
x_15 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__4;
x_16 = l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_23 = lean_int_dec_lt(x_20, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_18);
lean_free_object(x_14);
lean_dec(x_13);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__1(x_20, x_21, x_1, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_20);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__2;
x_27 = l_Lean_Grind_Linarith_Poly_mul(x_13, x_26);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 0, x_27);
x_28 = lean_box(0);
x_29 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__1(x_20, x_21, x_18, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_20);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_33 = lean_int_dec_lt(x_30, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_free_object(x_14);
lean_dec(x_13);
x_34 = lean_box(0);
x_35 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__1(x_30, x_31, x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_30);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__2;
x_37 = l_Lean_Grind_Linarith_Poly_mul(x_13, x_36);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 0, x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_14);
x_39 = lean_box(0);
x_40 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__1(x_30, x_31, x_38, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_30);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_14, 0);
lean_inc(x_41);
lean_dec(x_14);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
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
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_46 = lean_int_dec_lt(x_42, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_44);
lean_dec(x_13);
x_47 = lean_box(0);
x_48 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__1(x_42, x_43, x_1, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_42);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__2;
x_50 = l_Lean_Grind_Linarith_Poly_mul(x_13, x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_1);
if (lean_is_scalar(x_44)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_44;
}
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_box(0);
x_54 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__1(x_42, x_43, x_52, x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_42);
return x_54;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___boxed), 12, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1;
x_16 = lean_unbox(x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = lean_apply_12(x_15, x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = l_Lean_Grind_Linarith_Poly_gcdCoeffs(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_20);
x_23 = lean_nat_to_int(x_20);
x_24 = l_Lean_Grind_Linarith_Poly_div(x_19, x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_box(0);
x_28 = lean_apply_12(x_15, x_26, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
lean_dec(x_19);
x_29 = lean_box(0);
x_30 = lean_apply_12(x_15, x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_30;
}
}
}
else
{
uint8_t x_31; 
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
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__3;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__5;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__6;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 6);
lean_inc(x_19);
x_20 = lean_ctor_get(x_9, 7);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 8);
lean_inc(x_21);
x_22 = lean_ctor_get(x_9, 9);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 10);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*13);
x_25 = lean_ctor_get(x_9, 11);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_9, sizeof(void*)*13 + 1);
x_27 = lean_ctor_get(x_9, 12);
lean_inc(x_27);
x_28 = lean_nat_dec_eq(x_16, x_17);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_9, 12);
lean_dec(x_30);
x_31 = lean_ctor_get(x_9, 11);
lean_dec(x_31);
x_32 = lean_ctor_get(x_9, 10);
lean_dec(x_32);
x_33 = lean_ctor_get(x_9, 9);
lean_dec(x_33);
x_34 = lean_ctor_get(x_9, 8);
lean_dec(x_34);
x_35 = lean_ctor_get(x_9, 7);
lean_dec(x_35);
x_36 = lean_ctor_get(x_9, 6);
lean_dec(x_36);
x_37 = lean_ctor_get(x_9, 5);
lean_dec(x_37);
x_38 = lean_ctor_get(x_9, 4);
lean_dec(x_38);
x_39 = lean_ctor_get(x_9, 3);
lean_dec(x_39);
x_40 = lean_ctor_get(x_9, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_9, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_9, 0);
lean_dec(x_42);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_16, x_43);
lean_dec(x_16);
lean_ctor_set(x_9, 3, x_44);
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_9);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
lean_ctor_set(x_45, 0, x_1);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
x_60 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_61 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_53);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_52);
lean_free_object(x_51);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_box(0);
x_66 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___lambda__1(x_55, x_58, x_1, x_59, x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_64);
return x_66;
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_61);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_61, 1);
x_69 = lean_ctor_get(x_61, 0);
lean_dec(x_69);
x_70 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_MessageData_ofExpr(x_71);
x_80 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_79);
lean_ctor_set(x_61, 0, x_80);
x_81 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
lean_ctor_set_tag(x_52, 7);
lean_ctor_set(x_52, 1, x_81);
lean_ctor_set(x_52, 0, x_61);
x_82 = l_Lean_MessageData_ofExpr(x_74);
lean_ctor_set_tag(x_51, 7);
lean_ctor_set(x_51, 1, x_82);
lean_ctor_set(x_51, 0, x_52);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_51);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_MessageData_ofExpr(x_77);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_80);
x_87 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_60, x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_78);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___lambda__1(x_55, x_58, x_1, x_59, x_88, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_89);
lean_dec(x_88);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec(x_74);
lean_dec(x_71);
lean_free_object(x_61);
lean_free_object(x_52);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_9);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_76);
if (x_91 == 0)
{
return x_76;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_76, 0);
x_93 = lean_ctor_get(x_76, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_76);
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
lean_dec(x_71);
lean_free_object(x_61);
lean_free_object(x_52);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_9);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_73);
if (x_95 == 0)
{
return x_73;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_73, 0);
x_97 = lean_ctor_get(x_73, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_73);
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
lean_free_object(x_61);
lean_free_object(x_52);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_9);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_70);
if (x_99 == 0)
{
return x_70;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_70, 0);
x_101 = lean_ctor_get(x_70, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_70);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_61, 1);
lean_inc(x_103);
lean_dec(x_61);
x_104 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = l_Lean_MessageData_ofExpr(x_105);
x_114 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
lean_ctor_set_tag(x_52, 7);
lean_ctor_set(x_52, 1, x_116);
lean_ctor_set(x_52, 0, x_115);
x_117 = l_Lean_MessageData_ofExpr(x_108);
lean_ctor_set_tag(x_51, 7);
lean_ctor_set(x_51, 1, x_117);
lean_ctor_set(x_51, 0, x_52);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_51);
lean_ctor_set(x_118, 1, x_116);
x_119 = l_Lean_MessageData_ofExpr(x_111);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_114);
x_122 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_60, x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_112);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___lambda__1(x_55, x_58, x_1, x_59, x_123, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_123);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_108);
lean_dec(x_105);
lean_free_object(x_52);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_9);
lean_dec(x_1);
x_126 = lean_ctor_get(x_110, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_110, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_128 = x_110;
} else {
 lean_dec_ref(x_110);
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
lean_dec(x_105);
lean_free_object(x_52);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_9);
lean_dec(x_1);
x_130 = lean_ctor_get(x_107, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_107, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_132 = x_107;
} else {
 lean_dec_ref(x_107);
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
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_free_object(x_52);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_9);
lean_dec(x_1);
x_134 = lean_ctor_get(x_104, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_104, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_136 = x_104;
} else {
 lean_dec_ref(x_104);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_138 = lean_ctor_get(x_52, 0);
x_139 = lean_ctor_get(x_52, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_52);
x_140 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_141 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_140, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_53);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_unbox(x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_free_object(x_51);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
x_145 = lean_box(0);
x_146 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___lambda__1(x_55, x_138, x_1, x_139, x_145, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_144);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_141, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_148 = x_141;
} else {
 lean_dec_ref(x_141);
 x_148 = lean_box(0);
}
x_149 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_147);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_138, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Lean_MessageData_ofExpr(x_150);
x_159 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
if (lean_is_scalar(x_148)) {
 x_160 = lean_alloc_ctor(7, 2, 0);
} else {
 x_160 = x_148;
 lean_ctor_set_tag(x_160, 7);
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_MessageData_ofExpr(x_153);
lean_ctor_set_tag(x_51, 7);
lean_ctor_set(x_51, 1, x_163);
lean_ctor_set(x_51, 0, x_162);
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_51);
lean_ctor_set(x_164, 1, x_161);
x_165 = l_Lean_MessageData_ofExpr(x_156);
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_159);
x_168 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_140, x_167, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_157);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___lambda__1(x_55, x_138, x_1, x_139, x_169, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_170);
lean_dec(x_169);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_153);
lean_dec(x_150);
lean_dec(x_148);
lean_dec(x_139);
lean_dec(x_138);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_9);
lean_dec(x_1);
x_172 = lean_ctor_get(x_155, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_155, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_174 = x_155;
} else {
 lean_dec_ref(x_155);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_150);
lean_dec(x_148);
lean_dec(x_139);
lean_dec(x_138);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_9);
lean_dec(x_1);
x_176 = lean_ctor_get(x_152, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_152, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_178 = x_152;
} else {
 lean_dec_ref(x_152);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_148);
lean_dec(x_139);
lean_dec(x_138);
lean_free_object(x_51);
lean_dec(x_55);
lean_dec(x_9);
lean_dec(x_1);
x_180 = lean_ctor_get(x_149, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_149, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_182 = x_149;
} else {
 lean_dec_ref(x_149);
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
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_184 = lean_ctor_get(x_51, 0);
lean_inc(x_184);
lean_dec(x_51);
x_185 = lean_ctor_get(x_52, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_52, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_187 = x_52;
} else {
 lean_dec_ref(x_52);
 x_187 = lean_box(0);
}
x_188 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_189 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_188, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_53);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_unbox(x_190);
lean_dec(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_187);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
lean_dec(x_189);
x_193 = lean_box(0);
x_194 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___lambda__1(x_184, x_185, x_1, x_186, x_193, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_192);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_189, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_196 = x_189;
} else {
 lean_dec_ref(x_189);
 x_196 = lean_box(0);
}
x_197 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_184, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_195);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_185, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = l_Lean_MessageData_ofExpr(x_198);
x_207 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
if (lean_is_scalar(x_196)) {
 x_208 = lean_alloc_ctor(7, 2, 0);
} else {
 x_208 = x_196;
 lean_ctor_set_tag(x_208, 7);
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
x_209 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
if (lean_is_scalar(x_187)) {
 x_210 = lean_alloc_ctor(7, 2, 0);
} else {
 x_210 = x_187;
 lean_ctor_set_tag(x_210, 7);
}
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_MessageData_ofExpr(x_201);
x_212 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_209);
x_214 = l_Lean_MessageData_ofExpr(x_204);
x_215 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_207);
x_217 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_188, x_216, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_205);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___lambda__1(x_184, x_185, x_1, x_186, x_218, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_219);
lean_dec(x_218);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_201);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_1);
x_221 = lean_ctor_get(x_203, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_203, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_223 = x_203;
} else {
 lean_dec_ref(x_203);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_1);
x_225 = lean_ctor_get(x_200, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_200, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_227 = x_200;
} else {
 lean_dec_ref(x_200);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_196);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_1);
x_229 = lean_ctor_get(x_197, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_197, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_231 = x_197;
} else {
 lean_dec_ref(x_197);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_9);
lean_dec(x_1);
x_233 = !lean_is_exclusive(x_45);
if (x_233 == 0)
{
return x_45;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_45, 0);
x_235 = lean_ctor_get(x_45, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_45);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_9);
x_237 = lean_unsigned_to_nat(1u);
x_238 = lean_nat_add(x_16, x_237);
lean_dec(x_16);
x_239 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_239, 0, x_13);
lean_ctor_set(x_239, 1, x_14);
lean_ctor_set(x_239, 2, x_15);
lean_ctor_set(x_239, 3, x_238);
lean_ctor_set(x_239, 4, x_17);
lean_ctor_set(x_239, 5, x_18);
lean_ctor_set(x_239, 6, x_19);
lean_ctor_set(x_239, 7, x_20);
lean_ctor_set(x_239, 8, x_21);
lean_ctor_set(x_239, 9, x_22);
lean_ctor_set(x_239, 10, x_23);
lean_ctor_set(x_239, 11, x_25);
lean_ctor_set(x_239, 12, x_27);
lean_ctor_set_uint8(x_239, sizeof(void*)*13, x_24);
lean_ctor_set_uint8(x_239, sizeof(void*)*13 + 1, x_26);
x_240 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_239, x_10, x_11);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_239);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_243 = x_240;
} else {
 lean_dec_ref(x_240);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_1);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_245 = lean_ctor_get(x_241, 0);
lean_inc(x_245);
lean_dec(x_241);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_240, 1);
lean_inc(x_247);
lean_dec(x_240);
x_248 = lean_ctor_get(x_245, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_249 = x_245;
} else {
 lean_dec_ref(x_245);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_246, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_246, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_252 = x_246;
} else {
 lean_dec_ref(x_246);
 x_252 = lean_box(0);
}
x_253 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_254 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_253, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_239, x_10, x_247);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_unbox(x_255);
lean_dec(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_252);
lean_dec(x_249);
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_dec(x_254);
x_258 = lean_box(0);
x_259 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___lambda__1(x_248, x_250, x_1, x_251, x_258, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_239, x_10, x_257);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_254, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_261 = x_254;
} else {
 lean_dec_ref(x_254);
 x_261 = lean_box(0);
}
x_262 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_248, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_239, x_10, x_260);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_239, x_10, x_264);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_250, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_239, x_10, x_267);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = l_Lean_MessageData_ofExpr(x_263);
x_272 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
if (lean_is_scalar(x_261)) {
 x_273 = lean_alloc_ctor(7, 2, 0);
} else {
 x_273 = x_261;
 lean_ctor_set_tag(x_273, 7);
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
x_274 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
if (lean_is_scalar(x_252)) {
 x_275 = lean_alloc_ctor(7, 2, 0);
} else {
 x_275 = x_252;
 lean_ctor_set_tag(x_275, 7);
}
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
x_276 = l_Lean_MessageData_ofExpr(x_266);
if (lean_is_scalar(x_249)) {
 x_277 = lean_alloc_ctor(7, 2, 0);
} else {
 x_277 = x_249;
 lean_ctor_set_tag(x_277, 7);
}
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_274);
x_279 = l_Lean_MessageData_ofExpr(x_269);
x_280 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_272);
x_282 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_253, x_281, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_239, x_10, x_270);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___lambda__1(x_248, x_250, x_1, x_251, x_283, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_239, x_10, x_284);
lean_dec(x_283);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_266);
lean_dec(x_263);
lean_dec(x_261);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_239);
lean_dec(x_1);
x_286 = lean_ctor_get(x_268, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_268, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_288 = x_268;
} else {
 lean_dec_ref(x_268);
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
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_263);
lean_dec(x_261);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_239);
lean_dec(x_1);
x_290 = lean_ctor_get(x_265, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_265, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_292 = x_265;
} else {
 lean_dec_ref(x_265);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_261);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_239);
lean_dec(x_1);
x_294 = lean_ctor_get(x_262, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_262, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_296 = x_262;
} else {
 lean_dec_ref(x_262);
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
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_239);
lean_dec(x_1);
x_298 = lean_ctor_get(x_240, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_240, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_300 = x_240;
} else {
 lean_dec_ref(x_240);
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
}
else
{
lean_object* x_302; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_302 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_302;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_alloc_ctor(11, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_3);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_19 = lean_nat_to_int(x_1);
x_20 = l_Lean_Grind_Linarith_Poly_mul(x_17, x_19);
lean_dec(x_19);
x_21 = lean_int_neg(x_4);
x_22 = l_Lean_Grind_Linarith_Poly_mul(x_16, x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(100000000u);
x_24 = l_Lean_Grind_Linarith_Poly_combine_x27(x_23, x_20, x_22);
x_25 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1;
x_26 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___lambda__1(x_2, x_3, x_5, x_24, x_18, x_30, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_29);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 1);
x_34 = lean_ctor_get(x_26, 0);
lean_dec(x_34);
x_35 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__2(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_MessageData_ofExpr(x_36);
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_44);
lean_ctor_set(x_26, 0, x_45);
x_46 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_MessageData_ofExpr(x_39);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
x_51 = l_Lean_MessageData_ofExpr(x_42);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
x_54 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_25, x_53, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_43);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___lambda__1(x_2, x_3, x_5, x_24, x_18, x_55, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_56);
lean_dec(x_55);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_39);
lean_dec(x_36);
lean_free_object(x_26);
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_41);
if (x_58 == 0)
{
return x_41;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_41, 0);
x_60 = lean_ctor_get(x_41, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_41);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_36);
lean_free_object(x_26);
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_38);
if (x_62 == 0)
{
return x_38;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_38, 0);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_38);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_free_object(x_26);
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_35);
if (x_66 == 0)
{
return x_35;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_35, 0);
x_68 = lean_ctor_get(x_35, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_35);
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
x_70 = lean_ctor_get(x_26, 1);
lean_inc(x_70);
lean_dec(x_26);
x_71 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__2(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_MessageData_ofExpr(x_72);
x_81 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_MessageData_ofExpr(x_75);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
x_88 = l_Lean_MessageData_ofExpr(x_78);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_81);
x_91 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_25, x_90, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_79);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___lambda__1(x_2, x_3, x_5, x_24, x_18, x_92, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_93);
lean_dec(x_92);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_95 = lean_ctor_get(x_77, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_97 = x_77;
} else {
 lean_dec_ref(x_77);
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
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_72);
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_99 = lean_ctor_get(x_74, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_74, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_101 = x_74;
} else {
 lean_dec_ref(x_74);
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
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_103 = lean_ctor_get(x_71, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_71, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_105 = x_71;
} else {
 lean_dec_ref(x_71);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___lambda__1(x_1, x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_16;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_9, x_8);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
x_23 = lean_array_uget(x_7, x_9);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(x_1, x_2, x_3, x_24, x_25, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_29 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_27, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_31 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_30);
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
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = 1;
x_36 = lean_usize_add(x_9, x_35);
lean_inc(x_6);
{
size_t _tmp_8 = x_36;
lean_object* _tmp_9 = x_6;
lean_object* _tmp_19 = x_34;
x_9 = _tmp_8;
x_10 = _tmp_9;
x_20 = _tmp_19;
}
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_31, 0);
lean_dec(x_39);
x_40 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___closed__2;
lean_ctor_set(x_31, 0, x_40);
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_dec(x_31);
x_42 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___closed__2;
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
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
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_box(0);
x_16 = lean_array_size(x_4);
x_17 = 0;
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__1;
x_19 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1(x_1, x_2, x_3, x_4, x_15, x_18, x_4, x_16, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
uint8_t x_28; 
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
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___boxed(lean_object** _args) {
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
x_21 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_22 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_23 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_21, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_8, x_7);
if (x_10 == 0)
{
lean_dec(x_5);
return x_9;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_uget(x_6, x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
lean_inc(x_13);
x_15 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__3(x_1, x_2, x_11, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; 
lean_dec(x_13);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_5);
x_18 = 1;
x_19 = lean_usize_add(x_8, x_18);
x_8 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
lean_inc(x_21);
x_22 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__3(x_1, x_2, x_11, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_8, x_27);
x_8 = x_28;
x_9 = x_26;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_4);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_uget(x_5, x_7);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = l_Lean_Grind_Linarith_Poly_coeff(x_15, x_1);
lean_dec(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_18 = lean_int_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_10);
x_20 = lean_array_push(x_14, x_19);
lean_ctor_set(x_11, 1, x_20);
lean_inc(x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_11);
x_22 = 1;
x_23 = lean_usize_add(x_7, x_22);
x_7 = x_23;
x_8 = x_21;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_16);
x_25 = l_Lean_PersistentArray_push___rarg(x_13, x_10);
lean_ctor_set(x_11, 0, x_25);
lean_inc(x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_11);
x_27 = 1;
x_28 = lean_usize_add(x_7, x_27);
x_7 = x_28;
x_8 = x_26;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
x_33 = l_Lean_Grind_Linarith_Poly_coeff(x_32, x_1);
lean_dec(x_32);
x_34 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_35 = lean_int_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_10);
x_37 = lean_array_push(x_31, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_4);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_38);
x_40 = 1;
x_41 = lean_usize_add(x_7, x_40);
x_7 = x_41;
x_8 = x_39;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
lean_dec(x_33);
x_43 = l_Lean_PersistentArray_push___rarg(x_30, x_10);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_31);
lean_inc(x_4);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_44);
x_46 = 1;
x_47 = lean_usize_add(x_7, x_46);
x_7 = x_47;
x_8 = x_45;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__3___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_10 = lean_array_size(x_6);
x_11 = 0;
x_12 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__4(x_1, x_2, x_6, x_7, x_8, x_6, x_10, x_11, x_9);
lean_dec(x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
lean_object* x_15; 
lean_dec(x_12);
lean_free_object(x_3);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
x_20 = lean_array_size(x_16);
x_21 = 0;
x_22 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__4(x_1, x_2, x_16, x_17, x_18, x_16, x_20, x_21, x_19);
lean_dec(x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
x_32 = lean_array_size(x_28);
x_33 = 0;
x_34 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__5(x_1, x_28, x_29, x_30, x_28, x_32, x_33, x_31);
lean_dec(x_28);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_ctor_set(x_3, 0, x_36);
return x_3;
}
else
{
lean_object* x_37; 
lean_dec(x_34);
lean_free_object(x_3);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_3, 0);
lean_inc(x_38);
lean_dec(x_3);
x_39 = lean_box(0);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
x_42 = lean_array_size(x_38);
x_43 = 0;
x_44 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__5(x_1, x_38, x_39, x_40, x_38, x_42, x_43, x_41);
lean_dec(x_38);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; 
lean_dec(x_44);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_4);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_uget(x_5, x_7);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = l_Lean_Grind_Linarith_Poly_coeff(x_15, x_1);
lean_dec(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_18 = lean_int_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_10);
x_20 = lean_array_push(x_14, x_19);
lean_ctor_set(x_11, 1, x_20);
lean_inc(x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_11);
x_22 = 1;
x_23 = lean_usize_add(x_7, x_22);
x_7 = x_23;
x_8 = x_21;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_16);
x_25 = l_Lean_PersistentArray_push___rarg(x_13, x_10);
lean_ctor_set(x_11, 0, x_25);
lean_inc(x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_11);
x_27 = 1;
x_28 = lean_usize_add(x_7, x_27);
x_7 = x_28;
x_8 = x_26;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
x_33 = l_Lean_Grind_Linarith_Poly_coeff(x_32, x_1);
lean_dec(x_32);
x_34 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_35 = lean_int_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_10);
x_37 = lean_array_push(x_31, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_4);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_38);
x_40 = 1;
x_41 = lean_usize_add(x_7, x_40);
x_7 = x_41;
x_8 = x_39;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
lean_dec(x_33);
x_43 = l_Lean_PersistentArray_push___rarg(x_30, x_10);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_31);
lean_inc(x_4);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_44);
x_46 = 1;
x_47 = lean_usize_add(x_7, x_46);
x_7 = x_47;
x_8 = x_45;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__3(x_1, x_3, x_4, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
x_12 = lean_array_size(x_9);
x_13 = 0;
x_14 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__6(x_1, x_8, x_9, x_10, x_9, x_12, x_13, x_11);
lean_dec(x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__3;
x_2 = l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__5;
x_4 = l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__2(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__5(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__3___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__6(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__2___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1(x_1, x_2);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArray(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_307 = lean_ctor_get(x_17, 29);
lean_inc(x_307);
lean_dec(x_17);
x_308 = lean_ctor_get(x_307, 2);
lean_inc(x_308);
x_309 = lean_nat_dec_lt(x_4, x_308);
lean_dec(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_307);
x_310 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1;
x_311 = l_outOfBounds___rarg(x_310);
x_19 = x_311;
goto block_306;
}
else
{
lean_object* x_312; lean_object* x_313; 
x_312 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1;
x_313 = l_Lean_PersistentArray_get_x21___rarg(x_312, x_307, x_4);
x_19 = x_313;
goto block_306;
}
block_306:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1(x_1, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_take(x_7, x_18);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 14);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_24, 14);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_25, 3);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_array_get_size(x_33);
x_35 = lean_nat_dec_lt(x_6, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_21);
x_36 = lean_st_ref_set(x_7, x_24, x_27);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_37);
lean_dec(x_22);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_array_fget(x_33, x_6);
x_40 = lean_box(0);
x_41 = lean_array_fset(x_33, x_6, x_40);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_39, 29);
x_44 = l_Lean_PersistentArray_set___rarg(x_43, x_4, x_21);
lean_ctor_set(x_39, 29, x_44);
x_45 = lean_array_fset(x_41, x_6, x_39);
lean_ctor_set(x_26, 0, x_45);
x_46 = lean_st_ref_set(x_7, x_24, x_27);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_47);
lean_dec(x_22);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
x_51 = lean_ctor_get(x_39, 2);
x_52 = lean_ctor_get(x_39, 3);
x_53 = lean_ctor_get(x_39, 4);
x_54 = lean_ctor_get(x_39, 5);
x_55 = lean_ctor_get(x_39, 6);
x_56 = lean_ctor_get(x_39, 7);
x_57 = lean_ctor_get(x_39, 8);
x_58 = lean_ctor_get(x_39, 9);
x_59 = lean_ctor_get(x_39, 10);
x_60 = lean_ctor_get(x_39, 11);
x_61 = lean_ctor_get(x_39, 12);
x_62 = lean_ctor_get(x_39, 13);
x_63 = lean_ctor_get(x_39, 14);
x_64 = lean_ctor_get(x_39, 15);
x_65 = lean_ctor_get(x_39, 16);
x_66 = lean_ctor_get(x_39, 17);
x_67 = lean_ctor_get(x_39, 18);
x_68 = lean_ctor_get(x_39, 19);
x_69 = lean_ctor_get(x_39, 20);
x_70 = lean_ctor_get(x_39, 21);
x_71 = lean_ctor_get(x_39, 22);
x_72 = lean_ctor_get(x_39, 23);
x_73 = lean_ctor_get(x_39, 24);
x_74 = lean_ctor_get(x_39, 25);
x_75 = lean_ctor_get(x_39, 26);
x_76 = lean_ctor_get(x_39, 27);
x_77 = lean_ctor_get(x_39, 28);
x_78 = lean_ctor_get(x_39, 29);
x_79 = lean_ctor_get(x_39, 30);
x_80 = lean_ctor_get(x_39, 31);
x_81 = lean_ctor_get(x_39, 32);
x_82 = lean_ctor_get_uint8(x_39, sizeof(void*)*39);
x_83 = lean_ctor_get(x_39, 33);
x_84 = lean_ctor_get(x_39, 34);
x_85 = lean_ctor_get(x_39, 35);
x_86 = lean_ctor_get(x_39, 36);
x_87 = lean_ctor_get(x_39, 37);
x_88 = lean_ctor_get(x_39, 38);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
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
lean_dec(x_39);
x_89 = l_Lean_PersistentArray_set___rarg(x_78, x_4, x_21);
x_90 = lean_alloc_ctor(0, 39, 1);
lean_ctor_set(x_90, 0, x_49);
lean_ctor_set(x_90, 1, x_50);
lean_ctor_set(x_90, 2, x_51);
lean_ctor_set(x_90, 3, x_52);
lean_ctor_set(x_90, 4, x_53);
lean_ctor_set(x_90, 5, x_54);
lean_ctor_set(x_90, 6, x_55);
lean_ctor_set(x_90, 7, x_56);
lean_ctor_set(x_90, 8, x_57);
lean_ctor_set(x_90, 9, x_58);
lean_ctor_set(x_90, 10, x_59);
lean_ctor_set(x_90, 11, x_60);
lean_ctor_set(x_90, 12, x_61);
lean_ctor_set(x_90, 13, x_62);
lean_ctor_set(x_90, 14, x_63);
lean_ctor_set(x_90, 15, x_64);
lean_ctor_set(x_90, 16, x_65);
lean_ctor_set(x_90, 17, x_66);
lean_ctor_set(x_90, 18, x_67);
lean_ctor_set(x_90, 19, x_68);
lean_ctor_set(x_90, 20, x_69);
lean_ctor_set(x_90, 21, x_70);
lean_ctor_set(x_90, 22, x_71);
lean_ctor_set(x_90, 23, x_72);
lean_ctor_set(x_90, 24, x_73);
lean_ctor_set(x_90, 25, x_74);
lean_ctor_set(x_90, 26, x_75);
lean_ctor_set(x_90, 27, x_76);
lean_ctor_set(x_90, 28, x_77);
lean_ctor_set(x_90, 29, x_89);
lean_ctor_set(x_90, 30, x_79);
lean_ctor_set(x_90, 31, x_80);
lean_ctor_set(x_90, 32, x_81);
lean_ctor_set(x_90, 33, x_83);
lean_ctor_set(x_90, 34, x_84);
lean_ctor_set(x_90, 35, x_85);
lean_ctor_set(x_90, 36, x_86);
lean_ctor_set(x_90, 37, x_87);
lean_ctor_set(x_90, 38, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*39, x_82);
x_91 = lean_array_fset(x_41, x_6, x_90);
lean_ctor_set(x_26, 0, x_91);
x_92 = lean_st_ref_set(x_7, x_24, x_27);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_93);
lean_dec(x_22);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_95 = lean_ctor_get(x_26, 0);
x_96 = lean_ctor_get(x_26, 1);
x_97 = lean_ctor_get(x_26, 2);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_26);
x_98 = lean_array_get_size(x_95);
x_99 = lean_nat_dec_lt(x_6, x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_21);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_96);
lean_ctor_set(x_100, 2, x_97);
lean_ctor_set(x_25, 3, x_100);
x_101 = lean_st_ref_set(x_7, x_24, x_27);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_102);
lean_dec(x_22);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_104 = lean_array_fget(x_95, x_6);
x_105 = lean_box(0);
x_106 = lean_array_fset(x_95, x_6, x_105);
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 2);
lean_inc(x_109);
x_110 = lean_ctor_get(x_104, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_104, 4);
lean_inc(x_111);
x_112 = lean_ctor_get(x_104, 5);
lean_inc(x_112);
x_113 = lean_ctor_get(x_104, 6);
lean_inc(x_113);
x_114 = lean_ctor_get(x_104, 7);
lean_inc(x_114);
x_115 = lean_ctor_get(x_104, 8);
lean_inc(x_115);
x_116 = lean_ctor_get(x_104, 9);
lean_inc(x_116);
x_117 = lean_ctor_get(x_104, 10);
lean_inc(x_117);
x_118 = lean_ctor_get(x_104, 11);
lean_inc(x_118);
x_119 = lean_ctor_get(x_104, 12);
lean_inc(x_119);
x_120 = lean_ctor_get(x_104, 13);
lean_inc(x_120);
x_121 = lean_ctor_get(x_104, 14);
lean_inc(x_121);
x_122 = lean_ctor_get(x_104, 15);
lean_inc(x_122);
x_123 = lean_ctor_get(x_104, 16);
lean_inc(x_123);
x_124 = lean_ctor_get(x_104, 17);
lean_inc(x_124);
x_125 = lean_ctor_get(x_104, 18);
lean_inc(x_125);
x_126 = lean_ctor_get(x_104, 19);
lean_inc(x_126);
x_127 = lean_ctor_get(x_104, 20);
lean_inc(x_127);
x_128 = lean_ctor_get(x_104, 21);
lean_inc(x_128);
x_129 = lean_ctor_get(x_104, 22);
lean_inc(x_129);
x_130 = lean_ctor_get(x_104, 23);
lean_inc(x_130);
x_131 = lean_ctor_get(x_104, 24);
lean_inc(x_131);
x_132 = lean_ctor_get(x_104, 25);
lean_inc(x_132);
x_133 = lean_ctor_get(x_104, 26);
lean_inc(x_133);
x_134 = lean_ctor_get(x_104, 27);
lean_inc(x_134);
x_135 = lean_ctor_get(x_104, 28);
lean_inc(x_135);
x_136 = lean_ctor_get(x_104, 29);
lean_inc(x_136);
x_137 = lean_ctor_get(x_104, 30);
lean_inc(x_137);
x_138 = lean_ctor_get(x_104, 31);
lean_inc(x_138);
x_139 = lean_ctor_get(x_104, 32);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_104, sizeof(void*)*39);
x_141 = lean_ctor_get(x_104, 33);
lean_inc(x_141);
x_142 = lean_ctor_get(x_104, 34);
lean_inc(x_142);
x_143 = lean_ctor_get(x_104, 35);
lean_inc(x_143);
x_144 = lean_ctor_get(x_104, 36);
lean_inc(x_144);
x_145 = lean_ctor_get(x_104, 37);
lean_inc(x_145);
x_146 = lean_ctor_get(x_104, 38);
lean_inc(x_146);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 lean_ctor_release(x_104, 3);
 lean_ctor_release(x_104, 4);
 lean_ctor_release(x_104, 5);
 lean_ctor_release(x_104, 6);
 lean_ctor_release(x_104, 7);
 lean_ctor_release(x_104, 8);
 lean_ctor_release(x_104, 9);
 lean_ctor_release(x_104, 10);
 lean_ctor_release(x_104, 11);
 lean_ctor_release(x_104, 12);
 lean_ctor_release(x_104, 13);
 lean_ctor_release(x_104, 14);
 lean_ctor_release(x_104, 15);
 lean_ctor_release(x_104, 16);
 lean_ctor_release(x_104, 17);
 lean_ctor_release(x_104, 18);
 lean_ctor_release(x_104, 19);
 lean_ctor_release(x_104, 20);
 lean_ctor_release(x_104, 21);
 lean_ctor_release(x_104, 22);
 lean_ctor_release(x_104, 23);
 lean_ctor_release(x_104, 24);
 lean_ctor_release(x_104, 25);
 lean_ctor_release(x_104, 26);
 lean_ctor_release(x_104, 27);
 lean_ctor_release(x_104, 28);
 lean_ctor_release(x_104, 29);
 lean_ctor_release(x_104, 30);
 lean_ctor_release(x_104, 31);
 lean_ctor_release(x_104, 32);
 lean_ctor_release(x_104, 33);
 lean_ctor_release(x_104, 34);
 lean_ctor_release(x_104, 35);
 lean_ctor_release(x_104, 36);
 lean_ctor_release(x_104, 37);
 lean_ctor_release(x_104, 38);
 x_147 = x_104;
} else {
 lean_dec_ref(x_104);
 x_147 = lean_box(0);
}
x_148 = l_Lean_PersistentArray_set___rarg(x_136, x_4, x_21);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(0, 39, 1);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_107);
lean_ctor_set(x_149, 1, x_108);
lean_ctor_set(x_149, 2, x_109);
lean_ctor_set(x_149, 3, x_110);
lean_ctor_set(x_149, 4, x_111);
lean_ctor_set(x_149, 5, x_112);
lean_ctor_set(x_149, 6, x_113);
lean_ctor_set(x_149, 7, x_114);
lean_ctor_set(x_149, 8, x_115);
lean_ctor_set(x_149, 9, x_116);
lean_ctor_set(x_149, 10, x_117);
lean_ctor_set(x_149, 11, x_118);
lean_ctor_set(x_149, 12, x_119);
lean_ctor_set(x_149, 13, x_120);
lean_ctor_set(x_149, 14, x_121);
lean_ctor_set(x_149, 15, x_122);
lean_ctor_set(x_149, 16, x_123);
lean_ctor_set(x_149, 17, x_124);
lean_ctor_set(x_149, 18, x_125);
lean_ctor_set(x_149, 19, x_126);
lean_ctor_set(x_149, 20, x_127);
lean_ctor_set(x_149, 21, x_128);
lean_ctor_set(x_149, 22, x_129);
lean_ctor_set(x_149, 23, x_130);
lean_ctor_set(x_149, 24, x_131);
lean_ctor_set(x_149, 25, x_132);
lean_ctor_set(x_149, 26, x_133);
lean_ctor_set(x_149, 27, x_134);
lean_ctor_set(x_149, 28, x_135);
lean_ctor_set(x_149, 29, x_148);
lean_ctor_set(x_149, 30, x_137);
lean_ctor_set(x_149, 31, x_138);
lean_ctor_set(x_149, 32, x_139);
lean_ctor_set(x_149, 33, x_141);
lean_ctor_set(x_149, 34, x_142);
lean_ctor_set(x_149, 35, x_143);
lean_ctor_set(x_149, 36, x_144);
lean_ctor_set(x_149, 37, x_145);
lean_ctor_set(x_149, 38, x_146);
lean_ctor_set_uint8(x_149, sizeof(void*)*39, x_140);
x_150 = lean_array_fset(x_106, x_6, x_149);
x_151 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_96);
lean_ctor_set(x_151, 2, x_97);
lean_ctor_set(x_25, 3, x_151);
x_152 = lean_st_ref_set(x_7, x_24, x_27);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_154 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_153);
lean_dec(x_22);
return x_154;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_155 = lean_ctor_get(x_25, 0);
x_156 = lean_ctor_get(x_25, 1);
x_157 = lean_ctor_get(x_25, 2);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_25);
x_158 = lean_ctor_get(x_26, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_26, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_26, 2);
lean_inc(x_160);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_161 = x_26;
} else {
 lean_dec_ref(x_26);
 x_161 = lean_box(0);
}
x_162 = lean_array_get_size(x_158);
x_163 = lean_nat_dec_lt(x_6, x_162);
lean_dec(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_21);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 3, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_159);
lean_ctor_set(x_164, 2, x_160);
x_165 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_165, 0, x_155);
lean_ctor_set(x_165, 1, x_156);
lean_ctor_set(x_165, 2, x_157);
lean_ctor_set(x_165, 3, x_164);
lean_ctor_set(x_24, 14, x_165);
x_166 = lean_st_ref_set(x_7, x_24, x_27);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_167);
lean_dec(x_22);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_169 = lean_array_fget(x_158, x_6);
x_170 = lean_box(0);
x_171 = lean_array_fset(x_158, x_6, x_170);
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_169, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_169, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_169, 4);
lean_inc(x_176);
x_177 = lean_ctor_get(x_169, 5);
lean_inc(x_177);
x_178 = lean_ctor_get(x_169, 6);
lean_inc(x_178);
x_179 = lean_ctor_get(x_169, 7);
lean_inc(x_179);
x_180 = lean_ctor_get(x_169, 8);
lean_inc(x_180);
x_181 = lean_ctor_get(x_169, 9);
lean_inc(x_181);
x_182 = lean_ctor_get(x_169, 10);
lean_inc(x_182);
x_183 = lean_ctor_get(x_169, 11);
lean_inc(x_183);
x_184 = lean_ctor_get(x_169, 12);
lean_inc(x_184);
x_185 = lean_ctor_get(x_169, 13);
lean_inc(x_185);
x_186 = lean_ctor_get(x_169, 14);
lean_inc(x_186);
x_187 = lean_ctor_get(x_169, 15);
lean_inc(x_187);
x_188 = lean_ctor_get(x_169, 16);
lean_inc(x_188);
x_189 = lean_ctor_get(x_169, 17);
lean_inc(x_189);
x_190 = lean_ctor_get(x_169, 18);
lean_inc(x_190);
x_191 = lean_ctor_get(x_169, 19);
lean_inc(x_191);
x_192 = lean_ctor_get(x_169, 20);
lean_inc(x_192);
x_193 = lean_ctor_get(x_169, 21);
lean_inc(x_193);
x_194 = lean_ctor_get(x_169, 22);
lean_inc(x_194);
x_195 = lean_ctor_get(x_169, 23);
lean_inc(x_195);
x_196 = lean_ctor_get(x_169, 24);
lean_inc(x_196);
x_197 = lean_ctor_get(x_169, 25);
lean_inc(x_197);
x_198 = lean_ctor_get(x_169, 26);
lean_inc(x_198);
x_199 = lean_ctor_get(x_169, 27);
lean_inc(x_199);
x_200 = lean_ctor_get(x_169, 28);
lean_inc(x_200);
x_201 = lean_ctor_get(x_169, 29);
lean_inc(x_201);
x_202 = lean_ctor_get(x_169, 30);
lean_inc(x_202);
x_203 = lean_ctor_get(x_169, 31);
lean_inc(x_203);
x_204 = lean_ctor_get(x_169, 32);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_169, sizeof(void*)*39);
x_206 = lean_ctor_get(x_169, 33);
lean_inc(x_206);
x_207 = lean_ctor_get(x_169, 34);
lean_inc(x_207);
x_208 = lean_ctor_get(x_169, 35);
lean_inc(x_208);
x_209 = lean_ctor_get(x_169, 36);
lean_inc(x_209);
x_210 = lean_ctor_get(x_169, 37);
lean_inc(x_210);
x_211 = lean_ctor_get(x_169, 38);
lean_inc(x_211);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 lean_ctor_release(x_169, 4);
 lean_ctor_release(x_169, 5);
 lean_ctor_release(x_169, 6);
 lean_ctor_release(x_169, 7);
 lean_ctor_release(x_169, 8);
 lean_ctor_release(x_169, 9);
 lean_ctor_release(x_169, 10);
 lean_ctor_release(x_169, 11);
 lean_ctor_release(x_169, 12);
 lean_ctor_release(x_169, 13);
 lean_ctor_release(x_169, 14);
 lean_ctor_release(x_169, 15);
 lean_ctor_release(x_169, 16);
 lean_ctor_release(x_169, 17);
 lean_ctor_release(x_169, 18);
 lean_ctor_release(x_169, 19);
 lean_ctor_release(x_169, 20);
 lean_ctor_release(x_169, 21);
 lean_ctor_release(x_169, 22);
 lean_ctor_release(x_169, 23);
 lean_ctor_release(x_169, 24);
 lean_ctor_release(x_169, 25);
 lean_ctor_release(x_169, 26);
 lean_ctor_release(x_169, 27);
 lean_ctor_release(x_169, 28);
 lean_ctor_release(x_169, 29);
 lean_ctor_release(x_169, 30);
 lean_ctor_release(x_169, 31);
 lean_ctor_release(x_169, 32);
 lean_ctor_release(x_169, 33);
 lean_ctor_release(x_169, 34);
 lean_ctor_release(x_169, 35);
 lean_ctor_release(x_169, 36);
 lean_ctor_release(x_169, 37);
 lean_ctor_release(x_169, 38);
 x_212 = x_169;
} else {
 lean_dec_ref(x_169);
 x_212 = lean_box(0);
}
x_213 = l_Lean_PersistentArray_set___rarg(x_201, x_4, x_21);
if (lean_is_scalar(x_212)) {
 x_214 = lean_alloc_ctor(0, 39, 1);
} else {
 x_214 = x_212;
}
lean_ctor_set(x_214, 0, x_172);
lean_ctor_set(x_214, 1, x_173);
lean_ctor_set(x_214, 2, x_174);
lean_ctor_set(x_214, 3, x_175);
lean_ctor_set(x_214, 4, x_176);
lean_ctor_set(x_214, 5, x_177);
lean_ctor_set(x_214, 6, x_178);
lean_ctor_set(x_214, 7, x_179);
lean_ctor_set(x_214, 8, x_180);
lean_ctor_set(x_214, 9, x_181);
lean_ctor_set(x_214, 10, x_182);
lean_ctor_set(x_214, 11, x_183);
lean_ctor_set(x_214, 12, x_184);
lean_ctor_set(x_214, 13, x_185);
lean_ctor_set(x_214, 14, x_186);
lean_ctor_set(x_214, 15, x_187);
lean_ctor_set(x_214, 16, x_188);
lean_ctor_set(x_214, 17, x_189);
lean_ctor_set(x_214, 18, x_190);
lean_ctor_set(x_214, 19, x_191);
lean_ctor_set(x_214, 20, x_192);
lean_ctor_set(x_214, 21, x_193);
lean_ctor_set(x_214, 22, x_194);
lean_ctor_set(x_214, 23, x_195);
lean_ctor_set(x_214, 24, x_196);
lean_ctor_set(x_214, 25, x_197);
lean_ctor_set(x_214, 26, x_198);
lean_ctor_set(x_214, 27, x_199);
lean_ctor_set(x_214, 28, x_200);
lean_ctor_set(x_214, 29, x_213);
lean_ctor_set(x_214, 30, x_202);
lean_ctor_set(x_214, 31, x_203);
lean_ctor_set(x_214, 32, x_204);
lean_ctor_set(x_214, 33, x_206);
lean_ctor_set(x_214, 34, x_207);
lean_ctor_set(x_214, 35, x_208);
lean_ctor_set(x_214, 36, x_209);
lean_ctor_set(x_214, 37, x_210);
lean_ctor_set(x_214, 38, x_211);
lean_ctor_set_uint8(x_214, sizeof(void*)*39, x_205);
x_215 = lean_array_fset(x_171, x_6, x_214);
if (lean_is_scalar(x_161)) {
 x_216 = lean_alloc_ctor(0, 3, 0);
} else {
 x_216 = x_161;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_159);
lean_ctor_set(x_216, 2, x_160);
x_217 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_217, 0, x_155);
lean_ctor_set(x_217, 1, x_156);
lean_ctor_set(x_217, 2, x_157);
lean_ctor_set(x_217, 3, x_216);
lean_ctor_set(x_24, 14, x_217);
x_218 = lean_st_ref_set(x_7, x_24, x_27);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_220 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_219);
lean_dec(x_22);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_221 = lean_ctor_get(x_24, 0);
x_222 = lean_ctor_get(x_24, 1);
x_223 = lean_ctor_get(x_24, 2);
x_224 = lean_ctor_get(x_24, 3);
x_225 = lean_ctor_get(x_24, 4);
x_226 = lean_ctor_get(x_24, 5);
x_227 = lean_ctor_get(x_24, 6);
x_228 = lean_ctor_get(x_24, 7);
x_229 = lean_ctor_get_uint8(x_24, sizeof(void*)*16);
x_230 = lean_ctor_get(x_24, 8);
x_231 = lean_ctor_get(x_24, 9);
x_232 = lean_ctor_get(x_24, 10);
x_233 = lean_ctor_get(x_24, 11);
x_234 = lean_ctor_get(x_24, 12);
x_235 = lean_ctor_get(x_24, 13);
x_236 = lean_ctor_get(x_24, 15);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_24);
x_237 = lean_ctor_get(x_25, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_25, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_25, 2);
lean_inc(x_239);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 x_240 = x_25;
} else {
 lean_dec_ref(x_25);
 x_240 = lean_box(0);
}
x_241 = lean_ctor_get(x_26, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_26, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_26, 2);
lean_inc(x_243);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_244 = x_26;
} else {
 lean_dec_ref(x_26);
 x_244 = lean_box(0);
}
x_245 = lean_array_get_size(x_241);
x_246 = lean_nat_dec_lt(x_6, x_245);
lean_dec(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_21);
if (lean_is_scalar(x_244)) {
 x_247 = lean_alloc_ctor(0, 3, 0);
} else {
 x_247 = x_244;
}
lean_ctor_set(x_247, 0, x_241);
lean_ctor_set(x_247, 1, x_242);
lean_ctor_set(x_247, 2, x_243);
if (lean_is_scalar(x_240)) {
 x_248 = lean_alloc_ctor(0, 4, 0);
} else {
 x_248 = x_240;
}
lean_ctor_set(x_248, 0, x_237);
lean_ctor_set(x_248, 1, x_238);
lean_ctor_set(x_248, 2, x_239);
lean_ctor_set(x_248, 3, x_247);
x_249 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_249, 0, x_221);
lean_ctor_set(x_249, 1, x_222);
lean_ctor_set(x_249, 2, x_223);
lean_ctor_set(x_249, 3, x_224);
lean_ctor_set(x_249, 4, x_225);
lean_ctor_set(x_249, 5, x_226);
lean_ctor_set(x_249, 6, x_227);
lean_ctor_set(x_249, 7, x_228);
lean_ctor_set(x_249, 8, x_230);
lean_ctor_set(x_249, 9, x_231);
lean_ctor_set(x_249, 10, x_232);
lean_ctor_set(x_249, 11, x_233);
lean_ctor_set(x_249, 12, x_234);
lean_ctor_set(x_249, 13, x_235);
lean_ctor_set(x_249, 14, x_248);
lean_ctor_set(x_249, 15, x_236);
lean_ctor_set_uint8(x_249, sizeof(void*)*16, x_229);
x_250 = lean_st_ref_set(x_7, x_249, x_27);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec(x_250);
x_252 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_251);
lean_dec(x_22);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_253 = lean_array_fget(x_241, x_6);
x_254 = lean_box(0);
x_255 = lean_array_fset(x_241, x_6, x_254);
x_256 = lean_ctor_get(x_253, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_253, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_253, 2);
lean_inc(x_258);
x_259 = lean_ctor_get(x_253, 3);
lean_inc(x_259);
x_260 = lean_ctor_get(x_253, 4);
lean_inc(x_260);
x_261 = lean_ctor_get(x_253, 5);
lean_inc(x_261);
x_262 = lean_ctor_get(x_253, 6);
lean_inc(x_262);
x_263 = lean_ctor_get(x_253, 7);
lean_inc(x_263);
x_264 = lean_ctor_get(x_253, 8);
lean_inc(x_264);
x_265 = lean_ctor_get(x_253, 9);
lean_inc(x_265);
x_266 = lean_ctor_get(x_253, 10);
lean_inc(x_266);
x_267 = lean_ctor_get(x_253, 11);
lean_inc(x_267);
x_268 = lean_ctor_get(x_253, 12);
lean_inc(x_268);
x_269 = lean_ctor_get(x_253, 13);
lean_inc(x_269);
x_270 = lean_ctor_get(x_253, 14);
lean_inc(x_270);
x_271 = lean_ctor_get(x_253, 15);
lean_inc(x_271);
x_272 = lean_ctor_get(x_253, 16);
lean_inc(x_272);
x_273 = lean_ctor_get(x_253, 17);
lean_inc(x_273);
x_274 = lean_ctor_get(x_253, 18);
lean_inc(x_274);
x_275 = lean_ctor_get(x_253, 19);
lean_inc(x_275);
x_276 = lean_ctor_get(x_253, 20);
lean_inc(x_276);
x_277 = lean_ctor_get(x_253, 21);
lean_inc(x_277);
x_278 = lean_ctor_get(x_253, 22);
lean_inc(x_278);
x_279 = lean_ctor_get(x_253, 23);
lean_inc(x_279);
x_280 = lean_ctor_get(x_253, 24);
lean_inc(x_280);
x_281 = lean_ctor_get(x_253, 25);
lean_inc(x_281);
x_282 = lean_ctor_get(x_253, 26);
lean_inc(x_282);
x_283 = lean_ctor_get(x_253, 27);
lean_inc(x_283);
x_284 = lean_ctor_get(x_253, 28);
lean_inc(x_284);
x_285 = lean_ctor_get(x_253, 29);
lean_inc(x_285);
x_286 = lean_ctor_get(x_253, 30);
lean_inc(x_286);
x_287 = lean_ctor_get(x_253, 31);
lean_inc(x_287);
x_288 = lean_ctor_get(x_253, 32);
lean_inc(x_288);
x_289 = lean_ctor_get_uint8(x_253, sizeof(void*)*39);
x_290 = lean_ctor_get(x_253, 33);
lean_inc(x_290);
x_291 = lean_ctor_get(x_253, 34);
lean_inc(x_291);
x_292 = lean_ctor_get(x_253, 35);
lean_inc(x_292);
x_293 = lean_ctor_get(x_253, 36);
lean_inc(x_293);
x_294 = lean_ctor_get(x_253, 37);
lean_inc(x_294);
x_295 = lean_ctor_get(x_253, 38);
lean_inc(x_295);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 lean_ctor_release(x_253, 2);
 lean_ctor_release(x_253, 3);
 lean_ctor_release(x_253, 4);
 lean_ctor_release(x_253, 5);
 lean_ctor_release(x_253, 6);
 lean_ctor_release(x_253, 7);
 lean_ctor_release(x_253, 8);
 lean_ctor_release(x_253, 9);
 lean_ctor_release(x_253, 10);
 lean_ctor_release(x_253, 11);
 lean_ctor_release(x_253, 12);
 lean_ctor_release(x_253, 13);
 lean_ctor_release(x_253, 14);
 lean_ctor_release(x_253, 15);
 lean_ctor_release(x_253, 16);
 lean_ctor_release(x_253, 17);
 lean_ctor_release(x_253, 18);
 lean_ctor_release(x_253, 19);
 lean_ctor_release(x_253, 20);
 lean_ctor_release(x_253, 21);
 lean_ctor_release(x_253, 22);
 lean_ctor_release(x_253, 23);
 lean_ctor_release(x_253, 24);
 lean_ctor_release(x_253, 25);
 lean_ctor_release(x_253, 26);
 lean_ctor_release(x_253, 27);
 lean_ctor_release(x_253, 28);
 lean_ctor_release(x_253, 29);
 lean_ctor_release(x_253, 30);
 lean_ctor_release(x_253, 31);
 lean_ctor_release(x_253, 32);
 lean_ctor_release(x_253, 33);
 lean_ctor_release(x_253, 34);
 lean_ctor_release(x_253, 35);
 lean_ctor_release(x_253, 36);
 lean_ctor_release(x_253, 37);
 lean_ctor_release(x_253, 38);
 x_296 = x_253;
} else {
 lean_dec_ref(x_253);
 x_296 = lean_box(0);
}
x_297 = l_Lean_PersistentArray_set___rarg(x_285, x_4, x_21);
if (lean_is_scalar(x_296)) {
 x_298 = lean_alloc_ctor(0, 39, 1);
} else {
 x_298 = x_296;
}
lean_ctor_set(x_298, 0, x_256);
lean_ctor_set(x_298, 1, x_257);
lean_ctor_set(x_298, 2, x_258);
lean_ctor_set(x_298, 3, x_259);
lean_ctor_set(x_298, 4, x_260);
lean_ctor_set(x_298, 5, x_261);
lean_ctor_set(x_298, 6, x_262);
lean_ctor_set(x_298, 7, x_263);
lean_ctor_set(x_298, 8, x_264);
lean_ctor_set(x_298, 9, x_265);
lean_ctor_set(x_298, 10, x_266);
lean_ctor_set(x_298, 11, x_267);
lean_ctor_set(x_298, 12, x_268);
lean_ctor_set(x_298, 13, x_269);
lean_ctor_set(x_298, 14, x_270);
lean_ctor_set(x_298, 15, x_271);
lean_ctor_set(x_298, 16, x_272);
lean_ctor_set(x_298, 17, x_273);
lean_ctor_set(x_298, 18, x_274);
lean_ctor_set(x_298, 19, x_275);
lean_ctor_set(x_298, 20, x_276);
lean_ctor_set(x_298, 21, x_277);
lean_ctor_set(x_298, 22, x_278);
lean_ctor_set(x_298, 23, x_279);
lean_ctor_set(x_298, 24, x_280);
lean_ctor_set(x_298, 25, x_281);
lean_ctor_set(x_298, 26, x_282);
lean_ctor_set(x_298, 27, x_283);
lean_ctor_set(x_298, 28, x_284);
lean_ctor_set(x_298, 29, x_297);
lean_ctor_set(x_298, 30, x_286);
lean_ctor_set(x_298, 31, x_287);
lean_ctor_set(x_298, 32, x_288);
lean_ctor_set(x_298, 33, x_290);
lean_ctor_set(x_298, 34, x_291);
lean_ctor_set(x_298, 35, x_292);
lean_ctor_set(x_298, 36, x_293);
lean_ctor_set(x_298, 37, x_294);
lean_ctor_set(x_298, 38, x_295);
lean_ctor_set_uint8(x_298, sizeof(void*)*39, x_289);
x_299 = lean_array_fset(x_255, x_6, x_298);
if (lean_is_scalar(x_244)) {
 x_300 = lean_alloc_ctor(0, 3, 0);
} else {
 x_300 = x_244;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_242);
lean_ctor_set(x_300, 2, x_243);
if (lean_is_scalar(x_240)) {
 x_301 = lean_alloc_ctor(0, 4, 0);
} else {
 x_301 = x_240;
}
lean_ctor_set(x_301, 0, x_237);
lean_ctor_set(x_301, 1, x_238);
lean_ctor_set(x_301, 2, x_239);
lean_ctor_set(x_301, 3, x_300);
x_302 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_302, 0, x_221);
lean_ctor_set(x_302, 1, x_222);
lean_ctor_set(x_302, 2, x_223);
lean_ctor_set(x_302, 3, x_224);
lean_ctor_set(x_302, 4, x_225);
lean_ctor_set(x_302, 5, x_226);
lean_ctor_set(x_302, 6, x_227);
lean_ctor_set(x_302, 7, x_228);
lean_ctor_set(x_302, 8, x_230);
lean_ctor_set(x_302, 9, x_231);
lean_ctor_set(x_302, 10, x_232);
lean_ctor_set(x_302, 11, x_233);
lean_ctor_set(x_302, 12, x_234);
lean_ctor_set(x_302, 13, x_235);
lean_ctor_set(x_302, 14, x_301);
lean_ctor_set(x_302, 15, x_236);
lean_ctor_set_uint8(x_302, sizeof(void*)*16, x_229);
x_303 = lean_st_ref_set(x_7, x_302, x_27);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
lean_dec(x_303);
x_305 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_304);
lean_dec(x_22);
return x_305;
}
}
}
}
else
{
uint8_t x_314; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_314 = !lean_is_exclusive(x_16);
if (x_314 == 0)
{
return x_16;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_16, 0);
x_316 = lean_ctor_get(x_16, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_16);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1(x_2, x_1, x_3, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
return x_20;
}
else
{
uint8_t x_21; 
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
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_15, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_box(0);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_307 = lean_ctor_get(x_17, 30);
lean_inc(x_307);
lean_dec(x_17);
x_308 = lean_ctor_get(x_307, 2);
lean_inc(x_308);
x_309 = lean_nat_dec_lt(x_4, x_308);
lean_dec(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_307);
x_310 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1;
x_311 = l_outOfBounds___rarg(x_310);
x_19 = x_311;
goto block_306;
}
else
{
lean_object* x_312; lean_object* x_313; 
x_312 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1;
x_313 = l_Lean_PersistentArray_get_x21___rarg(x_312, x_307, x_4);
x_19 = x_313;
goto block_306;
}
block_306:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1(x_1, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_take(x_7, x_18);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 14);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_24, 14);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_25, 3);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_array_get_size(x_33);
x_35 = lean_nat_dec_lt(x_6, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_21);
x_36 = lean_st_ref_set(x_7, x_24, x_27);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_37);
lean_dec(x_22);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_array_fget(x_33, x_6);
x_40 = lean_box(0);
x_41 = lean_array_fset(x_33, x_6, x_40);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_39, 30);
x_44 = l_Lean_PersistentArray_set___rarg(x_43, x_4, x_21);
lean_ctor_set(x_39, 30, x_44);
x_45 = lean_array_fset(x_41, x_6, x_39);
lean_ctor_set(x_26, 0, x_45);
x_46 = lean_st_ref_set(x_7, x_24, x_27);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_47);
lean_dec(x_22);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
x_51 = lean_ctor_get(x_39, 2);
x_52 = lean_ctor_get(x_39, 3);
x_53 = lean_ctor_get(x_39, 4);
x_54 = lean_ctor_get(x_39, 5);
x_55 = lean_ctor_get(x_39, 6);
x_56 = lean_ctor_get(x_39, 7);
x_57 = lean_ctor_get(x_39, 8);
x_58 = lean_ctor_get(x_39, 9);
x_59 = lean_ctor_get(x_39, 10);
x_60 = lean_ctor_get(x_39, 11);
x_61 = lean_ctor_get(x_39, 12);
x_62 = lean_ctor_get(x_39, 13);
x_63 = lean_ctor_get(x_39, 14);
x_64 = lean_ctor_get(x_39, 15);
x_65 = lean_ctor_get(x_39, 16);
x_66 = lean_ctor_get(x_39, 17);
x_67 = lean_ctor_get(x_39, 18);
x_68 = lean_ctor_get(x_39, 19);
x_69 = lean_ctor_get(x_39, 20);
x_70 = lean_ctor_get(x_39, 21);
x_71 = lean_ctor_get(x_39, 22);
x_72 = lean_ctor_get(x_39, 23);
x_73 = lean_ctor_get(x_39, 24);
x_74 = lean_ctor_get(x_39, 25);
x_75 = lean_ctor_get(x_39, 26);
x_76 = lean_ctor_get(x_39, 27);
x_77 = lean_ctor_get(x_39, 28);
x_78 = lean_ctor_get(x_39, 29);
x_79 = lean_ctor_get(x_39, 30);
x_80 = lean_ctor_get(x_39, 31);
x_81 = lean_ctor_get(x_39, 32);
x_82 = lean_ctor_get_uint8(x_39, sizeof(void*)*39);
x_83 = lean_ctor_get(x_39, 33);
x_84 = lean_ctor_get(x_39, 34);
x_85 = lean_ctor_get(x_39, 35);
x_86 = lean_ctor_get(x_39, 36);
x_87 = lean_ctor_get(x_39, 37);
x_88 = lean_ctor_get(x_39, 38);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
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
lean_dec(x_39);
x_89 = l_Lean_PersistentArray_set___rarg(x_79, x_4, x_21);
x_90 = lean_alloc_ctor(0, 39, 1);
lean_ctor_set(x_90, 0, x_49);
lean_ctor_set(x_90, 1, x_50);
lean_ctor_set(x_90, 2, x_51);
lean_ctor_set(x_90, 3, x_52);
lean_ctor_set(x_90, 4, x_53);
lean_ctor_set(x_90, 5, x_54);
lean_ctor_set(x_90, 6, x_55);
lean_ctor_set(x_90, 7, x_56);
lean_ctor_set(x_90, 8, x_57);
lean_ctor_set(x_90, 9, x_58);
lean_ctor_set(x_90, 10, x_59);
lean_ctor_set(x_90, 11, x_60);
lean_ctor_set(x_90, 12, x_61);
lean_ctor_set(x_90, 13, x_62);
lean_ctor_set(x_90, 14, x_63);
lean_ctor_set(x_90, 15, x_64);
lean_ctor_set(x_90, 16, x_65);
lean_ctor_set(x_90, 17, x_66);
lean_ctor_set(x_90, 18, x_67);
lean_ctor_set(x_90, 19, x_68);
lean_ctor_set(x_90, 20, x_69);
lean_ctor_set(x_90, 21, x_70);
lean_ctor_set(x_90, 22, x_71);
lean_ctor_set(x_90, 23, x_72);
lean_ctor_set(x_90, 24, x_73);
lean_ctor_set(x_90, 25, x_74);
lean_ctor_set(x_90, 26, x_75);
lean_ctor_set(x_90, 27, x_76);
lean_ctor_set(x_90, 28, x_77);
lean_ctor_set(x_90, 29, x_78);
lean_ctor_set(x_90, 30, x_89);
lean_ctor_set(x_90, 31, x_80);
lean_ctor_set(x_90, 32, x_81);
lean_ctor_set(x_90, 33, x_83);
lean_ctor_set(x_90, 34, x_84);
lean_ctor_set(x_90, 35, x_85);
lean_ctor_set(x_90, 36, x_86);
lean_ctor_set(x_90, 37, x_87);
lean_ctor_set(x_90, 38, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*39, x_82);
x_91 = lean_array_fset(x_41, x_6, x_90);
lean_ctor_set(x_26, 0, x_91);
x_92 = lean_st_ref_set(x_7, x_24, x_27);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_93);
lean_dec(x_22);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_95 = lean_ctor_get(x_26, 0);
x_96 = lean_ctor_get(x_26, 1);
x_97 = lean_ctor_get(x_26, 2);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_26);
x_98 = lean_array_get_size(x_95);
x_99 = lean_nat_dec_lt(x_6, x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_21);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_96);
lean_ctor_set(x_100, 2, x_97);
lean_ctor_set(x_25, 3, x_100);
x_101 = lean_st_ref_set(x_7, x_24, x_27);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_102);
lean_dec(x_22);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_104 = lean_array_fget(x_95, x_6);
x_105 = lean_box(0);
x_106 = lean_array_fset(x_95, x_6, x_105);
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 2);
lean_inc(x_109);
x_110 = lean_ctor_get(x_104, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_104, 4);
lean_inc(x_111);
x_112 = lean_ctor_get(x_104, 5);
lean_inc(x_112);
x_113 = lean_ctor_get(x_104, 6);
lean_inc(x_113);
x_114 = lean_ctor_get(x_104, 7);
lean_inc(x_114);
x_115 = lean_ctor_get(x_104, 8);
lean_inc(x_115);
x_116 = lean_ctor_get(x_104, 9);
lean_inc(x_116);
x_117 = lean_ctor_get(x_104, 10);
lean_inc(x_117);
x_118 = lean_ctor_get(x_104, 11);
lean_inc(x_118);
x_119 = lean_ctor_get(x_104, 12);
lean_inc(x_119);
x_120 = lean_ctor_get(x_104, 13);
lean_inc(x_120);
x_121 = lean_ctor_get(x_104, 14);
lean_inc(x_121);
x_122 = lean_ctor_get(x_104, 15);
lean_inc(x_122);
x_123 = lean_ctor_get(x_104, 16);
lean_inc(x_123);
x_124 = lean_ctor_get(x_104, 17);
lean_inc(x_124);
x_125 = lean_ctor_get(x_104, 18);
lean_inc(x_125);
x_126 = lean_ctor_get(x_104, 19);
lean_inc(x_126);
x_127 = lean_ctor_get(x_104, 20);
lean_inc(x_127);
x_128 = lean_ctor_get(x_104, 21);
lean_inc(x_128);
x_129 = lean_ctor_get(x_104, 22);
lean_inc(x_129);
x_130 = lean_ctor_get(x_104, 23);
lean_inc(x_130);
x_131 = lean_ctor_get(x_104, 24);
lean_inc(x_131);
x_132 = lean_ctor_get(x_104, 25);
lean_inc(x_132);
x_133 = lean_ctor_get(x_104, 26);
lean_inc(x_133);
x_134 = lean_ctor_get(x_104, 27);
lean_inc(x_134);
x_135 = lean_ctor_get(x_104, 28);
lean_inc(x_135);
x_136 = lean_ctor_get(x_104, 29);
lean_inc(x_136);
x_137 = lean_ctor_get(x_104, 30);
lean_inc(x_137);
x_138 = lean_ctor_get(x_104, 31);
lean_inc(x_138);
x_139 = lean_ctor_get(x_104, 32);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_104, sizeof(void*)*39);
x_141 = lean_ctor_get(x_104, 33);
lean_inc(x_141);
x_142 = lean_ctor_get(x_104, 34);
lean_inc(x_142);
x_143 = lean_ctor_get(x_104, 35);
lean_inc(x_143);
x_144 = lean_ctor_get(x_104, 36);
lean_inc(x_144);
x_145 = lean_ctor_get(x_104, 37);
lean_inc(x_145);
x_146 = lean_ctor_get(x_104, 38);
lean_inc(x_146);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 lean_ctor_release(x_104, 3);
 lean_ctor_release(x_104, 4);
 lean_ctor_release(x_104, 5);
 lean_ctor_release(x_104, 6);
 lean_ctor_release(x_104, 7);
 lean_ctor_release(x_104, 8);
 lean_ctor_release(x_104, 9);
 lean_ctor_release(x_104, 10);
 lean_ctor_release(x_104, 11);
 lean_ctor_release(x_104, 12);
 lean_ctor_release(x_104, 13);
 lean_ctor_release(x_104, 14);
 lean_ctor_release(x_104, 15);
 lean_ctor_release(x_104, 16);
 lean_ctor_release(x_104, 17);
 lean_ctor_release(x_104, 18);
 lean_ctor_release(x_104, 19);
 lean_ctor_release(x_104, 20);
 lean_ctor_release(x_104, 21);
 lean_ctor_release(x_104, 22);
 lean_ctor_release(x_104, 23);
 lean_ctor_release(x_104, 24);
 lean_ctor_release(x_104, 25);
 lean_ctor_release(x_104, 26);
 lean_ctor_release(x_104, 27);
 lean_ctor_release(x_104, 28);
 lean_ctor_release(x_104, 29);
 lean_ctor_release(x_104, 30);
 lean_ctor_release(x_104, 31);
 lean_ctor_release(x_104, 32);
 lean_ctor_release(x_104, 33);
 lean_ctor_release(x_104, 34);
 lean_ctor_release(x_104, 35);
 lean_ctor_release(x_104, 36);
 lean_ctor_release(x_104, 37);
 lean_ctor_release(x_104, 38);
 x_147 = x_104;
} else {
 lean_dec_ref(x_104);
 x_147 = lean_box(0);
}
x_148 = l_Lean_PersistentArray_set___rarg(x_137, x_4, x_21);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(0, 39, 1);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_107);
lean_ctor_set(x_149, 1, x_108);
lean_ctor_set(x_149, 2, x_109);
lean_ctor_set(x_149, 3, x_110);
lean_ctor_set(x_149, 4, x_111);
lean_ctor_set(x_149, 5, x_112);
lean_ctor_set(x_149, 6, x_113);
lean_ctor_set(x_149, 7, x_114);
lean_ctor_set(x_149, 8, x_115);
lean_ctor_set(x_149, 9, x_116);
lean_ctor_set(x_149, 10, x_117);
lean_ctor_set(x_149, 11, x_118);
lean_ctor_set(x_149, 12, x_119);
lean_ctor_set(x_149, 13, x_120);
lean_ctor_set(x_149, 14, x_121);
lean_ctor_set(x_149, 15, x_122);
lean_ctor_set(x_149, 16, x_123);
lean_ctor_set(x_149, 17, x_124);
lean_ctor_set(x_149, 18, x_125);
lean_ctor_set(x_149, 19, x_126);
lean_ctor_set(x_149, 20, x_127);
lean_ctor_set(x_149, 21, x_128);
lean_ctor_set(x_149, 22, x_129);
lean_ctor_set(x_149, 23, x_130);
lean_ctor_set(x_149, 24, x_131);
lean_ctor_set(x_149, 25, x_132);
lean_ctor_set(x_149, 26, x_133);
lean_ctor_set(x_149, 27, x_134);
lean_ctor_set(x_149, 28, x_135);
lean_ctor_set(x_149, 29, x_136);
lean_ctor_set(x_149, 30, x_148);
lean_ctor_set(x_149, 31, x_138);
lean_ctor_set(x_149, 32, x_139);
lean_ctor_set(x_149, 33, x_141);
lean_ctor_set(x_149, 34, x_142);
lean_ctor_set(x_149, 35, x_143);
lean_ctor_set(x_149, 36, x_144);
lean_ctor_set(x_149, 37, x_145);
lean_ctor_set(x_149, 38, x_146);
lean_ctor_set_uint8(x_149, sizeof(void*)*39, x_140);
x_150 = lean_array_fset(x_106, x_6, x_149);
x_151 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_96);
lean_ctor_set(x_151, 2, x_97);
lean_ctor_set(x_25, 3, x_151);
x_152 = lean_st_ref_set(x_7, x_24, x_27);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_154 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_153);
lean_dec(x_22);
return x_154;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_155 = lean_ctor_get(x_25, 0);
x_156 = lean_ctor_get(x_25, 1);
x_157 = lean_ctor_get(x_25, 2);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_25);
x_158 = lean_ctor_get(x_26, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_26, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_26, 2);
lean_inc(x_160);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_161 = x_26;
} else {
 lean_dec_ref(x_26);
 x_161 = lean_box(0);
}
x_162 = lean_array_get_size(x_158);
x_163 = lean_nat_dec_lt(x_6, x_162);
lean_dec(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_21);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 3, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_159);
lean_ctor_set(x_164, 2, x_160);
x_165 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_165, 0, x_155);
lean_ctor_set(x_165, 1, x_156);
lean_ctor_set(x_165, 2, x_157);
lean_ctor_set(x_165, 3, x_164);
lean_ctor_set(x_24, 14, x_165);
x_166 = lean_st_ref_set(x_7, x_24, x_27);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_167);
lean_dec(x_22);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_169 = lean_array_fget(x_158, x_6);
x_170 = lean_box(0);
x_171 = lean_array_fset(x_158, x_6, x_170);
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_169, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_169, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_169, 4);
lean_inc(x_176);
x_177 = lean_ctor_get(x_169, 5);
lean_inc(x_177);
x_178 = lean_ctor_get(x_169, 6);
lean_inc(x_178);
x_179 = lean_ctor_get(x_169, 7);
lean_inc(x_179);
x_180 = lean_ctor_get(x_169, 8);
lean_inc(x_180);
x_181 = lean_ctor_get(x_169, 9);
lean_inc(x_181);
x_182 = lean_ctor_get(x_169, 10);
lean_inc(x_182);
x_183 = lean_ctor_get(x_169, 11);
lean_inc(x_183);
x_184 = lean_ctor_get(x_169, 12);
lean_inc(x_184);
x_185 = lean_ctor_get(x_169, 13);
lean_inc(x_185);
x_186 = lean_ctor_get(x_169, 14);
lean_inc(x_186);
x_187 = lean_ctor_get(x_169, 15);
lean_inc(x_187);
x_188 = lean_ctor_get(x_169, 16);
lean_inc(x_188);
x_189 = lean_ctor_get(x_169, 17);
lean_inc(x_189);
x_190 = lean_ctor_get(x_169, 18);
lean_inc(x_190);
x_191 = lean_ctor_get(x_169, 19);
lean_inc(x_191);
x_192 = lean_ctor_get(x_169, 20);
lean_inc(x_192);
x_193 = lean_ctor_get(x_169, 21);
lean_inc(x_193);
x_194 = lean_ctor_get(x_169, 22);
lean_inc(x_194);
x_195 = lean_ctor_get(x_169, 23);
lean_inc(x_195);
x_196 = lean_ctor_get(x_169, 24);
lean_inc(x_196);
x_197 = lean_ctor_get(x_169, 25);
lean_inc(x_197);
x_198 = lean_ctor_get(x_169, 26);
lean_inc(x_198);
x_199 = lean_ctor_get(x_169, 27);
lean_inc(x_199);
x_200 = lean_ctor_get(x_169, 28);
lean_inc(x_200);
x_201 = lean_ctor_get(x_169, 29);
lean_inc(x_201);
x_202 = lean_ctor_get(x_169, 30);
lean_inc(x_202);
x_203 = lean_ctor_get(x_169, 31);
lean_inc(x_203);
x_204 = lean_ctor_get(x_169, 32);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_169, sizeof(void*)*39);
x_206 = lean_ctor_get(x_169, 33);
lean_inc(x_206);
x_207 = lean_ctor_get(x_169, 34);
lean_inc(x_207);
x_208 = lean_ctor_get(x_169, 35);
lean_inc(x_208);
x_209 = lean_ctor_get(x_169, 36);
lean_inc(x_209);
x_210 = lean_ctor_get(x_169, 37);
lean_inc(x_210);
x_211 = lean_ctor_get(x_169, 38);
lean_inc(x_211);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 lean_ctor_release(x_169, 4);
 lean_ctor_release(x_169, 5);
 lean_ctor_release(x_169, 6);
 lean_ctor_release(x_169, 7);
 lean_ctor_release(x_169, 8);
 lean_ctor_release(x_169, 9);
 lean_ctor_release(x_169, 10);
 lean_ctor_release(x_169, 11);
 lean_ctor_release(x_169, 12);
 lean_ctor_release(x_169, 13);
 lean_ctor_release(x_169, 14);
 lean_ctor_release(x_169, 15);
 lean_ctor_release(x_169, 16);
 lean_ctor_release(x_169, 17);
 lean_ctor_release(x_169, 18);
 lean_ctor_release(x_169, 19);
 lean_ctor_release(x_169, 20);
 lean_ctor_release(x_169, 21);
 lean_ctor_release(x_169, 22);
 lean_ctor_release(x_169, 23);
 lean_ctor_release(x_169, 24);
 lean_ctor_release(x_169, 25);
 lean_ctor_release(x_169, 26);
 lean_ctor_release(x_169, 27);
 lean_ctor_release(x_169, 28);
 lean_ctor_release(x_169, 29);
 lean_ctor_release(x_169, 30);
 lean_ctor_release(x_169, 31);
 lean_ctor_release(x_169, 32);
 lean_ctor_release(x_169, 33);
 lean_ctor_release(x_169, 34);
 lean_ctor_release(x_169, 35);
 lean_ctor_release(x_169, 36);
 lean_ctor_release(x_169, 37);
 lean_ctor_release(x_169, 38);
 x_212 = x_169;
} else {
 lean_dec_ref(x_169);
 x_212 = lean_box(0);
}
x_213 = l_Lean_PersistentArray_set___rarg(x_202, x_4, x_21);
if (lean_is_scalar(x_212)) {
 x_214 = lean_alloc_ctor(0, 39, 1);
} else {
 x_214 = x_212;
}
lean_ctor_set(x_214, 0, x_172);
lean_ctor_set(x_214, 1, x_173);
lean_ctor_set(x_214, 2, x_174);
lean_ctor_set(x_214, 3, x_175);
lean_ctor_set(x_214, 4, x_176);
lean_ctor_set(x_214, 5, x_177);
lean_ctor_set(x_214, 6, x_178);
lean_ctor_set(x_214, 7, x_179);
lean_ctor_set(x_214, 8, x_180);
lean_ctor_set(x_214, 9, x_181);
lean_ctor_set(x_214, 10, x_182);
lean_ctor_set(x_214, 11, x_183);
lean_ctor_set(x_214, 12, x_184);
lean_ctor_set(x_214, 13, x_185);
lean_ctor_set(x_214, 14, x_186);
lean_ctor_set(x_214, 15, x_187);
lean_ctor_set(x_214, 16, x_188);
lean_ctor_set(x_214, 17, x_189);
lean_ctor_set(x_214, 18, x_190);
lean_ctor_set(x_214, 19, x_191);
lean_ctor_set(x_214, 20, x_192);
lean_ctor_set(x_214, 21, x_193);
lean_ctor_set(x_214, 22, x_194);
lean_ctor_set(x_214, 23, x_195);
lean_ctor_set(x_214, 24, x_196);
lean_ctor_set(x_214, 25, x_197);
lean_ctor_set(x_214, 26, x_198);
lean_ctor_set(x_214, 27, x_199);
lean_ctor_set(x_214, 28, x_200);
lean_ctor_set(x_214, 29, x_201);
lean_ctor_set(x_214, 30, x_213);
lean_ctor_set(x_214, 31, x_203);
lean_ctor_set(x_214, 32, x_204);
lean_ctor_set(x_214, 33, x_206);
lean_ctor_set(x_214, 34, x_207);
lean_ctor_set(x_214, 35, x_208);
lean_ctor_set(x_214, 36, x_209);
lean_ctor_set(x_214, 37, x_210);
lean_ctor_set(x_214, 38, x_211);
lean_ctor_set_uint8(x_214, sizeof(void*)*39, x_205);
x_215 = lean_array_fset(x_171, x_6, x_214);
if (lean_is_scalar(x_161)) {
 x_216 = lean_alloc_ctor(0, 3, 0);
} else {
 x_216 = x_161;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_159);
lean_ctor_set(x_216, 2, x_160);
x_217 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_217, 0, x_155);
lean_ctor_set(x_217, 1, x_156);
lean_ctor_set(x_217, 2, x_157);
lean_ctor_set(x_217, 3, x_216);
lean_ctor_set(x_24, 14, x_217);
x_218 = lean_st_ref_set(x_7, x_24, x_27);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_220 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_219);
lean_dec(x_22);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_221 = lean_ctor_get(x_24, 0);
x_222 = lean_ctor_get(x_24, 1);
x_223 = lean_ctor_get(x_24, 2);
x_224 = lean_ctor_get(x_24, 3);
x_225 = lean_ctor_get(x_24, 4);
x_226 = lean_ctor_get(x_24, 5);
x_227 = lean_ctor_get(x_24, 6);
x_228 = lean_ctor_get(x_24, 7);
x_229 = lean_ctor_get_uint8(x_24, sizeof(void*)*16);
x_230 = lean_ctor_get(x_24, 8);
x_231 = lean_ctor_get(x_24, 9);
x_232 = lean_ctor_get(x_24, 10);
x_233 = lean_ctor_get(x_24, 11);
x_234 = lean_ctor_get(x_24, 12);
x_235 = lean_ctor_get(x_24, 13);
x_236 = lean_ctor_get(x_24, 15);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_24);
x_237 = lean_ctor_get(x_25, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_25, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_25, 2);
lean_inc(x_239);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 x_240 = x_25;
} else {
 lean_dec_ref(x_25);
 x_240 = lean_box(0);
}
x_241 = lean_ctor_get(x_26, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_26, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_26, 2);
lean_inc(x_243);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_244 = x_26;
} else {
 lean_dec_ref(x_26);
 x_244 = lean_box(0);
}
x_245 = lean_array_get_size(x_241);
x_246 = lean_nat_dec_lt(x_6, x_245);
lean_dec(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_21);
if (lean_is_scalar(x_244)) {
 x_247 = lean_alloc_ctor(0, 3, 0);
} else {
 x_247 = x_244;
}
lean_ctor_set(x_247, 0, x_241);
lean_ctor_set(x_247, 1, x_242);
lean_ctor_set(x_247, 2, x_243);
if (lean_is_scalar(x_240)) {
 x_248 = lean_alloc_ctor(0, 4, 0);
} else {
 x_248 = x_240;
}
lean_ctor_set(x_248, 0, x_237);
lean_ctor_set(x_248, 1, x_238);
lean_ctor_set(x_248, 2, x_239);
lean_ctor_set(x_248, 3, x_247);
x_249 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_249, 0, x_221);
lean_ctor_set(x_249, 1, x_222);
lean_ctor_set(x_249, 2, x_223);
lean_ctor_set(x_249, 3, x_224);
lean_ctor_set(x_249, 4, x_225);
lean_ctor_set(x_249, 5, x_226);
lean_ctor_set(x_249, 6, x_227);
lean_ctor_set(x_249, 7, x_228);
lean_ctor_set(x_249, 8, x_230);
lean_ctor_set(x_249, 9, x_231);
lean_ctor_set(x_249, 10, x_232);
lean_ctor_set(x_249, 11, x_233);
lean_ctor_set(x_249, 12, x_234);
lean_ctor_set(x_249, 13, x_235);
lean_ctor_set(x_249, 14, x_248);
lean_ctor_set(x_249, 15, x_236);
lean_ctor_set_uint8(x_249, sizeof(void*)*16, x_229);
x_250 = lean_st_ref_set(x_7, x_249, x_27);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec(x_250);
x_252 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_251);
lean_dec(x_22);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_253 = lean_array_fget(x_241, x_6);
x_254 = lean_box(0);
x_255 = lean_array_fset(x_241, x_6, x_254);
x_256 = lean_ctor_get(x_253, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_253, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_253, 2);
lean_inc(x_258);
x_259 = lean_ctor_get(x_253, 3);
lean_inc(x_259);
x_260 = lean_ctor_get(x_253, 4);
lean_inc(x_260);
x_261 = lean_ctor_get(x_253, 5);
lean_inc(x_261);
x_262 = lean_ctor_get(x_253, 6);
lean_inc(x_262);
x_263 = lean_ctor_get(x_253, 7);
lean_inc(x_263);
x_264 = lean_ctor_get(x_253, 8);
lean_inc(x_264);
x_265 = lean_ctor_get(x_253, 9);
lean_inc(x_265);
x_266 = lean_ctor_get(x_253, 10);
lean_inc(x_266);
x_267 = lean_ctor_get(x_253, 11);
lean_inc(x_267);
x_268 = lean_ctor_get(x_253, 12);
lean_inc(x_268);
x_269 = lean_ctor_get(x_253, 13);
lean_inc(x_269);
x_270 = lean_ctor_get(x_253, 14);
lean_inc(x_270);
x_271 = lean_ctor_get(x_253, 15);
lean_inc(x_271);
x_272 = lean_ctor_get(x_253, 16);
lean_inc(x_272);
x_273 = lean_ctor_get(x_253, 17);
lean_inc(x_273);
x_274 = lean_ctor_get(x_253, 18);
lean_inc(x_274);
x_275 = lean_ctor_get(x_253, 19);
lean_inc(x_275);
x_276 = lean_ctor_get(x_253, 20);
lean_inc(x_276);
x_277 = lean_ctor_get(x_253, 21);
lean_inc(x_277);
x_278 = lean_ctor_get(x_253, 22);
lean_inc(x_278);
x_279 = lean_ctor_get(x_253, 23);
lean_inc(x_279);
x_280 = lean_ctor_get(x_253, 24);
lean_inc(x_280);
x_281 = lean_ctor_get(x_253, 25);
lean_inc(x_281);
x_282 = lean_ctor_get(x_253, 26);
lean_inc(x_282);
x_283 = lean_ctor_get(x_253, 27);
lean_inc(x_283);
x_284 = lean_ctor_get(x_253, 28);
lean_inc(x_284);
x_285 = lean_ctor_get(x_253, 29);
lean_inc(x_285);
x_286 = lean_ctor_get(x_253, 30);
lean_inc(x_286);
x_287 = lean_ctor_get(x_253, 31);
lean_inc(x_287);
x_288 = lean_ctor_get(x_253, 32);
lean_inc(x_288);
x_289 = lean_ctor_get_uint8(x_253, sizeof(void*)*39);
x_290 = lean_ctor_get(x_253, 33);
lean_inc(x_290);
x_291 = lean_ctor_get(x_253, 34);
lean_inc(x_291);
x_292 = lean_ctor_get(x_253, 35);
lean_inc(x_292);
x_293 = lean_ctor_get(x_253, 36);
lean_inc(x_293);
x_294 = lean_ctor_get(x_253, 37);
lean_inc(x_294);
x_295 = lean_ctor_get(x_253, 38);
lean_inc(x_295);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 lean_ctor_release(x_253, 2);
 lean_ctor_release(x_253, 3);
 lean_ctor_release(x_253, 4);
 lean_ctor_release(x_253, 5);
 lean_ctor_release(x_253, 6);
 lean_ctor_release(x_253, 7);
 lean_ctor_release(x_253, 8);
 lean_ctor_release(x_253, 9);
 lean_ctor_release(x_253, 10);
 lean_ctor_release(x_253, 11);
 lean_ctor_release(x_253, 12);
 lean_ctor_release(x_253, 13);
 lean_ctor_release(x_253, 14);
 lean_ctor_release(x_253, 15);
 lean_ctor_release(x_253, 16);
 lean_ctor_release(x_253, 17);
 lean_ctor_release(x_253, 18);
 lean_ctor_release(x_253, 19);
 lean_ctor_release(x_253, 20);
 lean_ctor_release(x_253, 21);
 lean_ctor_release(x_253, 22);
 lean_ctor_release(x_253, 23);
 lean_ctor_release(x_253, 24);
 lean_ctor_release(x_253, 25);
 lean_ctor_release(x_253, 26);
 lean_ctor_release(x_253, 27);
 lean_ctor_release(x_253, 28);
 lean_ctor_release(x_253, 29);
 lean_ctor_release(x_253, 30);
 lean_ctor_release(x_253, 31);
 lean_ctor_release(x_253, 32);
 lean_ctor_release(x_253, 33);
 lean_ctor_release(x_253, 34);
 lean_ctor_release(x_253, 35);
 lean_ctor_release(x_253, 36);
 lean_ctor_release(x_253, 37);
 lean_ctor_release(x_253, 38);
 x_296 = x_253;
} else {
 lean_dec_ref(x_253);
 x_296 = lean_box(0);
}
x_297 = l_Lean_PersistentArray_set___rarg(x_286, x_4, x_21);
if (lean_is_scalar(x_296)) {
 x_298 = lean_alloc_ctor(0, 39, 1);
} else {
 x_298 = x_296;
}
lean_ctor_set(x_298, 0, x_256);
lean_ctor_set(x_298, 1, x_257);
lean_ctor_set(x_298, 2, x_258);
lean_ctor_set(x_298, 3, x_259);
lean_ctor_set(x_298, 4, x_260);
lean_ctor_set(x_298, 5, x_261);
lean_ctor_set(x_298, 6, x_262);
lean_ctor_set(x_298, 7, x_263);
lean_ctor_set(x_298, 8, x_264);
lean_ctor_set(x_298, 9, x_265);
lean_ctor_set(x_298, 10, x_266);
lean_ctor_set(x_298, 11, x_267);
lean_ctor_set(x_298, 12, x_268);
lean_ctor_set(x_298, 13, x_269);
lean_ctor_set(x_298, 14, x_270);
lean_ctor_set(x_298, 15, x_271);
lean_ctor_set(x_298, 16, x_272);
lean_ctor_set(x_298, 17, x_273);
lean_ctor_set(x_298, 18, x_274);
lean_ctor_set(x_298, 19, x_275);
lean_ctor_set(x_298, 20, x_276);
lean_ctor_set(x_298, 21, x_277);
lean_ctor_set(x_298, 22, x_278);
lean_ctor_set(x_298, 23, x_279);
lean_ctor_set(x_298, 24, x_280);
lean_ctor_set(x_298, 25, x_281);
lean_ctor_set(x_298, 26, x_282);
lean_ctor_set(x_298, 27, x_283);
lean_ctor_set(x_298, 28, x_284);
lean_ctor_set(x_298, 29, x_285);
lean_ctor_set(x_298, 30, x_297);
lean_ctor_set(x_298, 31, x_287);
lean_ctor_set(x_298, 32, x_288);
lean_ctor_set(x_298, 33, x_290);
lean_ctor_set(x_298, 34, x_291);
lean_ctor_set(x_298, 35, x_292);
lean_ctor_set(x_298, 36, x_293);
lean_ctor_set(x_298, 37, x_294);
lean_ctor_set(x_298, 38, x_295);
lean_ctor_set_uint8(x_298, sizeof(void*)*39, x_289);
x_299 = lean_array_fset(x_255, x_6, x_298);
if (lean_is_scalar(x_244)) {
 x_300 = lean_alloc_ctor(0, 3, 0);
} else {
 x_300 = x_244;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_242);
lean_ctor_set(x_300, 2, x_243);
if (lean_is_scalar(x_240)) {
 x_301 = lean_alloc_ctor(0, 4, 0);
} else {
 x_301 = x_240;
}
lean_ctor_set(x_301, 0, x_237);
lean_ctor_set(x_301, 1, x_238);
lean_ctor_set(x_301, 2, x_239);
lean_ctor_set(x_301, 3, x_300);
x_302 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_302, 0, x_221);
lean_ctor_set(x_302, 1, x_222);
lean_ctor_set(x_302, 2, x_223);
lean_ctor_set(x_302, 3, x_224);
lean_ctor_set(x_302, 4, x_225);
lean_ctor_set(x_302, 5, x_226);
lean_ctor_set(x_302, 6, x_227);
lean_ctor_set(x_302, 7, x_228);
lean_ctor_set(x_302, 8, x_230);
lean_ctor_set(x_302, 9, x_231);
lean_ctor_set(x_302, 10, x_232);
lean_ctor_set(x_302, 11, x_233);
lean_ctor_set(x_302, 12, x_234);
lean_ctor_set(x_302, 13, x_235);
lean_ctor_set(x_302, 14, x_301);
lean_ctor_set(x_302, 15, x_236);
lean_ctor_set_uint8(x_302, sizeof(void*)*16, x_229);
x_303 = lean_st_ref_set(x_7, x_302, x_27);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
lean_dec(x_303);
x_305 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(x_2, x_1, x_3, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_304);
lean_dec(x_22);
return x_305;
}
}
}
}
else
{
uint8_t x_314; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_314 = !lean_is_exclusive(x_16);
if (x_314 == 0)
{
return x_16;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_16, 0);
x_316 = lean_ctor_get(x_16, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_16);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lambda__1(x_2, x_1, x_3, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
return x_20;
}
else
{
uint8_t x_21; 
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
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_15, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_box(0);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_4, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 14);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_17, 14);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_18, 3);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_array_get_size(x_26);
x_28 = lean_nat_dec_lt(x_3, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
lean_dec(x_14);
x_29 = lean_st_ref_set(x_4, x_17, x_20);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_array_fget(x_26, x_3);
x_37 = lean_box(0);
x_38 = lean_array_fset(x_26, x_3, x_37);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_36, 38);
x_41 = l_Lean_PersistentArray_push___rarg(x_40, x_14);
lean_ctor_set(x_36, 38, x_41);
x_42 = lean_array_fset(x_38, x_3, x_36);
lean_ctor_set(x_19, 0, x_42);
x_43 = lean_st_ref_set(x_4, x_17, x_20);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_37);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_36, 1);
x_50 = lean_ctor_get(x_36, 2);
x_51 = lean_ctor_get(x_36, 3);
x_52 = lean_ctor_get(x_36, 4);
x_53 = lean_ctor_get(x_36, 5);
x_54 = lean_ctor_get(x_36, 6);
x_55 = lean_ctor_get(x_36, 7);
x_56 = lean_ctor_get(x_36, 8);
x_57 = lean_ctor_get(x_36, 9);
x_58 = lean_ctor_get(x_36, 10);
x_59 = lean_ctor_get(x_36, 11);
x_60 = lean_ctor_get(x_36, 12);
x_61 = lean_ctor_get(x_36, 13);
x_62 = lean_ctor_get(x_36, 14);
x_63 = lean_ctor_get(x_36, 15);
x_64 = lean_ctor_get(x_36, 16);
x_65 = lean_ctor_get(x_36, 17);
x_66 = lean_ctor_get(x_36, 18);
x_67 = lean_ctor_get(x_36, 19);
x_68 = lean_ctor_get(x_36, 20);
x_69 = lean_ctor_get(x_36, 21);
x_70 = lean_ctor_get(x_36, 22);
x_71 = lean_ctor_get(x_36, 23);
x_72 = lean_ctor_get(x_36, 24);
x_73 = lean_ctor_get(x_36, 25);
x_74 = lean_ctor_get(x_36, 26);
x_75 = lean_ctor_get(x_36, 27);
x_76 = lean_ctor_get(x_36, 28);
x_77 = lean_ctor_get(x_36, 29);
x_78 = lean_ctor_get(x_36, 30);
x_79 = lean_ctor_get(x_36, 31);
x_80 = lean_ctor_get(x_36, 32);
x_81 = lean_ctor_get_uint8(x_36, sizeof(void*)*39);
x_82 = lean_ctor_get(x_36, 33);
x_83 = lean_ctor_get(x_36, 34);
x_84 = lean_ctor_get(x_36, 35);
x_85 = lean_ctor_get(x_36, 36);
x_86 = lean_ctor_get(x_36, 37);
x_87 = lean_ctor_get(x_36, 38);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_80);
lean_inc(x_79);
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
lean_dec(x_36);
x_88 = l_Lean_PersistentArray_push___rarg(x_87, x_14);
x_89 = lean_alloc_ctor(0, 39, 1);
lean_ctor_set(x_89, 0, x_48);
lean_ctor_set(x_89, 1, x_49);
lean_ctor_set(x_89, 2, x_50);
lean_ctor_set(x_89, 3, x_51);
lean_ctor_set(x_89, 4, x_52);
lean_ctor_set(x_89, 5, x_53);
lean_ctor_set(x_89, 6, x_54);
lean_ctor_set(x_89, 7, x_55);
lean_ctor_set(x_89, 8, x_56);
lean_ctor_set(x_89, 9, x_57);
lean_ctor_set(x_89, 10, x_58);
lean_ctor_set(x_89, 11, x_59);
lean_ctor_set(x_89, 12, x_60);
lean_ctor_set(x_89, 13, x_61);
lean_ctor_set(x_89, 14, x_62);
lean_ctor_set(x_89, 15, x_63);
lean_ctor_set(x_89, 16, x_64);
lean_ctor_set(x_89, 17, x_65);
lean_ctor_set(x_89, 18, x_66);
lean_ctor_set(x_89, 19, x_67);
lean_ctor_set(x_89, 20, x_68);
lean_ctor_set(x_89, 21, x_69);
lean_ctor_set(x_89, 22, x_70);
lean_ctor_set(x_89, 23, x_71);
lean_ctor_set(x_89, 24, x_72);
lean_ctor_set(x_89, 25, x_73);
lean_ctor_set(x_89, 26, x_74);
lean_ctor_set(x_89, 27, x_75);
lean_ctor_set(x_89, 28, x_76);
lean_ctor_set(x_89, 29, x_77);
lean_ctor_set(x_89, 30, x_78);
lean_ctor_set(x_89, 31, x_79);
lean_ctor_set(x_89, 32, x_80);
lean_ctor_set(x_89, 33, x_82);
lean_ctor_set(x_89, 34, x_83);
lean_ctor_set(x_89, 35, x_84);
lean_ctor_set(x_89, 36, x_85);
lean_ctor_set(x_89, 37, x_86);
lean_ctor_set(x_89, 38, x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*39, x_81);
x_90 = lean_array_fset(x_38, x_3, x_89);
lean_ctor_set(x_19, 0, x_90);
x_91 = lean_st_ref_set(x_4, x_17, x_20);
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
lean_ctor_set(x_94, 0, x_37);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_95 = lean_ctor_get(x_19, 0);
x_96 = lean_ctor_get(x_19, 1);
x_97 = lean_ctor_get(x_19, 2);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_19);
x_98 = lean_array_get_size(x_95);
x_99 = lean_nat_dec_lt(x_3, x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_14);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_96);
lean_ctor_set(x_100, 2, x_97);
lean_ctor_set(x_18, 3, x_100);
x_101 = lean_st_ref_set(x_4, x_17, x_20);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_106 = lean_array_fget(x_95, x_3);
x_107 = lean_box(0);
x_108 = lean_array_fset(x_95, x_3, x_107);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_106, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_106, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_106, 4);
lean_inc(x_113);
x_114 = lean_ctor_get(x_106, 5);
lean_inc(x_114);
x_115 = lean_ctor_get(x_106, 6);
lean_inc(x_115);
x_116 = lean_ctor_get(x_106, 7);
lean_inc(x_116);
x_117 = lean_ctor_get(x_106, 8);
lean_inc(x_117);
x_118 = lean_ctor_get(x_106, 9);
lean_inc(x_118);
x_119 = lean_ctor_get(x_106, 10);
lean_inc(x_119);
x_120 = lean_ctor_get(x_106, 11);
lean_inc(x_120);
x_121 = lean_ctor_get(x_106, 12);
lean_inc(x_121);
x_122 = lean_ctor_get(x_106, 13);
lean_inc(x_122);
x_123 = lean_ctor_get(x_106, 14);
lean_inc(x_123);
x_124 = lean_ctor_get(x_106, 15);
lean_inc(x_124);
x_125 = lean_ctor_get(x_106, 16);
lean_inc(x_125);
x_126 = lean_ctor_get(x_106, 17);
lean_inc(x_126);
x_127 = lean_ctor_get(x_106, 18);
lean_inc(x_127);
x_128 = lean_ctor_get(x_106, 19);
lean_inc(x_128);
x_129 = lean_ctor_get(x_106, 20);
lean_inc(x_129);
x_130 = lean_ctor_get(x_106, 21);
lean_inc(x_130);
x_131 = lean_ctor_get(x_106, 22);
lean_inc(x_131);
x_132 = lean_ctor_get(x_106, 23);
lean_inc(x_132);
x_133 = lean_ctor_get(x_106, 24);
lean_inc(x_133);
x_134 = lean_ctor_get(x_106, 25);
lean_inc(x_134);
x_135 = lean_ctor_get(x_106, 26);
lean_inc(x_135);
x_136 = lean_ctor_get(x_106, 27);
lean_inc(x_136);
x_137 = lean_ctor_get(x_106, 28);
lean_inc(x_137);
x_138 = lean_ctor_get(x_106, 29);
lean_inc(x_138);
x_139 = lean_ctor_get(x_106, 30);
lean_inc(x_139);
x_140 = lean_ctor_get(x_106, 31);
lean_inc(x_140);
x_141 = lean_ctor_get(x_106, 32);
lean_inc(x_141);
x_142 = lean_ctor_get_uint8(x_106, sizeof(void*)*39);
x_143 = lean_ctor_get(x_106, 33);
lean_inc(x_143);
x_144 = lean_ctor_get(x_106, 34);
lean_inc(x_144);
x_145 = lean_ctor_get(x_106, 35);
lean_inc(x_145);
x_146 = lean_ctor_get(x_106, 36);
lean_inc(x_146);
x_147 = lean_ctor_get(x_106, 37);
lean_inc(x_147);
x_148 = lean_ctor_get(x_106, 38);
lean_inc(x_148);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 lean_ctor_release(x_106, 4);
 lean_ctor_release(x_106, 5);
 lean_ctor_release(x_106, 6);
 lean_ctor_release(x_106, 7);
 lean_ctor_release(x_106, 8);
 lean_ctor_release(x_106, 9);
 lean_ctor_release(x_106, 10);
 lean_ctor_release(x_106, 11);
 lean_ctor_release(x_106, 12);
 lean_ctor_release(x_106, 13);
 lean_ctor_release(x_106, 14);
 lean_ctor_release(x_106, 15);
 lean_ctor_release(x_106, 16);
 lean_ctor_release(x_106, 17);
 lean_ctor_release(x_106, 18);
 lean_ctor_release(x_106, 19);
 lean_ctor_release(x_106, 20);
 lean_ctor_release(x_106, 21);
 lean_ctor_release(x_106, 22);
 lean_ctor_release(x_106, 23);
 lean_ctor_release(x_106, 24);
 lean_ctor_release(x_106, 25);
 lean_ctor_release(x_106, 26);
 lean_ctor_release(x_106, 27);
 lean_ctor_release(x_106, 28);
 lean_ctor_release(x_106, 29);
 lean_ctor_release(x_106, 30);
 lean_ctor_release(x_106, 31);
 lean_ctor_release(x_106, 32);
 lean_ctor_release(x_106, 33);
 lean_ctor_release(x_106, 34);
 lean_ctor_release(x_106, 35);
 lean_ctor_release(x_106, 36);
 lean_ctor_release(x_106, 37);
 lean_ctor_release(x_106, 38);
 x_149 = x_106;
} else {
 lean_dec_ref(x_106);
 x_149 = lean_box(0);
}
x_150 = l_Lean_PersistentArray_push___rarg(x_148, x_14);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 39, 1);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_109);
lean_ctor_set(x_151, 1, x_110);
lean_ctor_set(x_151, 2, x_111);
lean_ctor_set(x_151, 3, x_112);
lean_ctor_set(x_151, 4, x_113);
lean_ctor_set(x_151, 5, x_114);
lean_ctor_set(x_151, 6, x_115);
lean_ctor_set(x_151, 7, x_116);
lean_ctor_set(x_151, 8, x_117);
lean_ctor_set(x_151, 9, x_118);
lean_ctor_set(x_151, 10, x_119);
lean_ctor_set(x_151, 11, x_120);
lean_ctor_set(x_151, 12, x_121);
lean_ctor_set(x_151, 13, x_122);
lean_ctor_set(x_151, 14, x_123);
lean_ctor_set(x_151, 15, x_124);
lean_ctor_set(x_151, 16, x_125);
lean_ctor_set(x_151, 17, x_126);
lean_ctor_set(x_151, 18, x_127);
lean_ctor_set(x_151, 19, x_128);
lean_ctor_set(x_151, 20, x_129);
lean_ctor_set(x_151, 21, x_130);
lean_ctor_set(x_151, 22, x_131);
lean_ctor_set(x_151, 23, x_132);
lean_ctor_set(x_151, 24, x_133);
lean_ctor_set(x_151, 25, x_134);
lean_ctor_set(x_151, 26, x_135);
lean_ctor_set(x_151, 27, x_136);
lean_ctor_set(x_151, 28, x_137);
lean_ctor_set(x_151, 29, x_138);
lean_ctor_set(x_151, 30, x_139);
lean_ctor_set(x_151, 31, x_140);
lean_ctor_set(x_151, 32, x_141);
lean_ctor_set(x_151, 33, x_143);
lean_ctor_set(x_151, 34, x_144);
lean_ctor_set(x_151, 35, x_145);
lean_ctor_set(x_151, 36, x_146);
lean_ctor_set(x_151, 37, x_147);
lean_ctor_set(x_151, 38, x_150);
lean_ctor_set_uint8(x_151, sizeof(void*)*39, x_142);
x_152 = lean_array_fset(x_108, x_3, x_151);
x_153 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_96);
lean_ctor_set(x_153, 2, x_97);
lean_ctor_set(x_18, 3, x_153);
x_154 = lean_st_ref_set(x_4, x_17, x_20);
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
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_107);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_158 = lean_ctor_get(x_18, 0);
x_159 = lean_ctor_get(x_18, 1);
x_160 = lean_ctor_get(x_18, 2);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_18);
x_161 = lean_ctor_get(x_19, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_19, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_19, 2);
lean_inc(x_163);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_164 = x_19;
} else {
 lean_dec_ref(x_19);
 x_164 = lean_box(0);
}
x_165 = lean_array_get_size(x_161);
x_166 = lean_nat_dec_lt(x_3, x_165);
lean_dec(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_14);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(0, 3, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_161);
lean_ctor_set(x_167, 1, x_162);
lean_ctor_set(x_167, 2, x_163);
x_168 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_168, 0, x_158);
lean_ctor_set(x_168, 1, x_159);
lean_ctor_set(x_168, 2, x_160);
lean_ctor_set(x_168, 3, x_167);
lean_ctor_set(x_17, 14, x_168);
x_169 = lean_st_ref_set(x_4, x_17, x_20);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
x_172 = lean_box(0);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_170);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_174 = lean_array_fget(x_161, x_3);
x_175 = lean_box(0);
x_176 = lean_array_fset(x_161, x_3, x_175);
x_177 = lean_ctor_get(x_174, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_174, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_174, 2);
lean_inc(x_179);
x_180 = lean_ctor_get(x_174, 3);
lean_inc(x_180);
x_181 = lean_ctor_get(x_174, 4);
lean_inc(x_181);
x_182 = lean_ctor_get(x_174, 5);
lean_inc(x_182);
x_183 = lean_ctor_get(x_174, 6);
lean_inc(x_183);
x_184 = lean_ctor_get(x_174, 7);
lean_inc(x_184);
x_185 = lean_ctor_get(x_174, 8);
lean_inc(x_185);
x_186 = lean_ctor_get(x_174, 9);
lean_inc(x_186);
x_187 = lean_ctor_get(x_174, 10);
lean_inc(x_187);
x_188 = lean_ctor_get(x_174, 11);
lean_inc(x_188);
x_189 = lean_ctor_get(x_174, 12);
lean_inc(x_189);
x_190 = lean_ctor_get(x_174, 13);
lean_inc(x_190);
x_191 = lean_ctor_get(x_174, 14);
lean_inc(x_191);
x_192 = lean_ctor_get(x_174, 15);
lean_inc(x_192);
x_193 = lean_ctor_get(x_174, 16);
lean_inc(x_193);
x_194 = lean_ctor_get(x_174, 17);
lean_inc(x_194);
x_195 = lean_ctor_get(x_174, 18);
lean_inc(x_195);
x_196 = lean_ctor_get(x_174, 19);
lean_inc(x_196);
x_197 = lean_ctor_get(x_174, 20);
lean_inc(x_197);
x_198 = lean_ctor_get(x_174, 21);
lean_inc(x_198);
x_199 = lean_ctor_get(x_174, 22);
lean_inc(x_199);
x_200 = lean_ctor_get(x_174, 23);
lean_inc(x_200);
x_201 = lean_ctor_get(x_174, 24);
lean_inc(x_201);
x_202 = lean_ctor_get(x_174, 25);
lean_inc(x_202);
x_203 = lean_ctor_get(x_174, 26);
lean_inc(x_203);
x_204 = lean_ctor_get(x_174, 27);
lean_inc(x_204);
x_205 = lean_ctor_get(x_174, 28);
lean_inc(x_205);
x_206 = lean_ctor_get(x_174, 29);
lean_inc(x_206);
x_207 = lean_ctor_get(x_174, 30);
lean_inc(x_207);
x_208 = lean_ctor_get(x_174, 31);
lean_inc(x_208);
x_209 = lean_ctor_get(x_174, 32);
lean_inc(x_209);
x_210 = lean_ctor_get_uint8(x_174, sizeof(void*)*39);
x_211 = lean_ctor_get(x_174, 33);
lean_inc(x_211);
x_212 = lean_ctor_get(x_174, 34);
lean_inc(x_212);
x_213 = lean_ctor_get(x_174, 35);
lean_inc(x_213);
x_214 = lean_ctor_get(x_174, 36);
lean_inc(x_214);
x_215 = lean_ctor_get(x_174, 37);
lean_inc(x_215);
x_216 = lean_ctor_get(x_174, 38);
lean_inc(x_216);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 lean_ctor_release(x_174, 2);
 lean_ctor_release(x_174, 3);
 lean_ctor_release(x_174, 4);
 lean_ctor_release(x_174, 5);
 lean_ctor_release(x_174, 6);
 lean_ctor_release(x_174, 7);
 lean_ctor_release(x_174, 8);
 lean_ctor_release(x_174, 9);
 lean_ctor_release(x_174, 10);
 lean_ctor_release(x_174, 11);
 lean_ctor_release(x_174, 12);
 lean_ctor_release(x_174, 13);
 lean_ctor_release(x_174, 14);
 lean_ctor_release(x_174, 15);
 lean_ctor_release(x_174, 16);
 lean_ctor_release(x_174, 17);
 lean_ctor_release(x_174, 18);
 lean_ctor_release(x_174, 19);
 lean_ctor_release(x_174, 20);
 lean_ctor_release(x_174, 21);
 lean_ctor_release(x_174, 22);
 lean_ctor_release(x_174, 23);
 lean_ctor_release(x_174, 24);
 lean_ctor_release(x_174, 25);
 lean_ctor_release(x_174, 26);
 lean_ctor_release(x_174, 27);
 lean_ctor_release(x_174, 28);
 lean_ctor_release(x_174, 29);
 lean_ctor_release(x_174, 30);
 lean_ctor_release(x_174, 31);
 lean_ctor_release(x_174, 32);
 lean_ctor_release(x_174, 33);
 lean_ctor_release(x_174, 34);
 lean_ctor_release(x_174, 35);
 lean_ctor_release(x_174, 36);
 lean_ctor_release(x_174, 37);
 lean_ctor_release(x_174, 38);
 x_217 = x_174;
} else {
 lean_dec_ref(x_174);
 x_217 = lean_box(0);
}
x_218 = l_Lean_PersistentArray_push___rarg(x_216, x_14);
if (lean_is_scalar(x_217)) {
 x_219 = lean_alloc_ctor(0, 39, 1);
} else {
 x_219 = x_217;
}
lean_ctor_set(x_219, 0, x_177);
lean_ctor_set(x_219, 1, x_178);
lean_ctor_set(x_219, 2, x_179);
lean_ctor_set(x_219, 3, x_180);
lean_ctor_set(x_219, 4, x_181);
lean_ctor_set(x_219, 5, x_182);
lean_ctor_set(x_219, 6, x_183);
lean_ctor_set(x_219, 7, x_184);
lean_ctor_set(x_219, 8, x_185);
lean_ctor_set(x_219, 9, x_186);
lean_ctor_set(x_219, 10, x_187);
lean_ctor_set(x_219, 11, x_188);
lean_ctor_set(x_219, 12, x_189);
lean_ctor_set(x_219, 13, x_190);
lean_ctor_set(x_219, 14, x_191);
lean_ctor_set(x_219, 15, x_192);
lean_ctor_set(x_219, 16, x_193);
lean_ctor_set(x_219, 17, x_194);
lean_ctor_set(x_219, 18, x_195);
lean_ctor_set(x_219, 19, x_196);
lean_ctor_set(x_219, 20, x_197);
lean_ctor_set(x_219, 21, x_198);
lean_ctor_set(x_219, 22, x_199);
lean_ctor_set(x_219, 23, x_200);
lean_ctor_set(x_219, 24, x_201);
lean_ctor_set(x_219, 25, x_202);
lean_ctor_set(x_219, 26, x_203);
lean_ctor_set(x_219, 27, x_204);
lean_ctor_set(x_219, 28, x_205);
lean_ctor_set(x_219, 29, x_206);
lean_ctor_set(x_219, 30, x_207);
lean_ctor_set(x_219, 31, x_208);
lean_ctor_set(x_219, 32, x_209);
lean_ctor_set(x_219, 33, x_211);
lean_ctor_set(x_219, 34, x_212);
lean_ctor_set(x_219, 35, x_213);
lean_ctor_set(x_219, 36, x_214);
lean_ctor_set(x_219, 37, x_215);
lean_ctor_set(x_219, 38, x_218);
lean_ctor_set_uint8(x_219, sizeof(void*)*39, x_210);
x_220 = lean_array_fset(x_176, x_3, x_219);
if (lean_is_scalar(x_164)) {
 x_221 = lean_alloc_ctor(0, 3, 0);
} else {
 x_221 = x_164;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_162);
lean_ctor_set(x_221, 2, x_163);
x_222 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_222, 0, x_158);
lean_ctor_set(x_222, 1, x_159);
lean_ctor_set(x_222, 2, x_160);
lean_ctor_set(x_222, 3, x_221);
lean_ctor_set(x_17, 14, x_222);
x_223 = lean_st_ref_set(x_4, x_17, x_20);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_225 = x_223;
} else {
 lean_dec_ref(x_223);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_175);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_227 = lean_ctor_get(x_17, 0);
x_228 = lean_ctor_get(x_17, 1);
x_229 = lean_ctor_get(x_17, 2);
x_230 = lean_ctor_get(x_17, 3);
x_231 = lean_ctor_get(x_17, 4);
x_232 = lean_ctor_get(x_17, 5);
x_233 = lean_ctor_get(x_17, 6);
x_234 = lean_ctor_get(x_17, 7);
x_235 = lean_ctor_get_uint8(x_17, sizeof(void*)*16);
x_236 = lean_ctor_get(x_17, 8);
x_237 = lean_ctor_get(x_17, 9);
x_238 = lean_ctor_get(x_17, 10);
x_239 = lean_ctor_get(x_17, 11);
x_240 = lean_ctor_get(x_17, 12);
x_241 = lean_ctor_get(x_17, 13);
x_242 = lean_ctor_get(x_17, 15);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_17);
x_243 = lean_ctor_get(x_18, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_18, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_18, 2);
lean_inc(x_245);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 x_246 = x_18;
} else {
 lean_dec_ref(x_18);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_19, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_19, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_19, 2);
lean_inc(x_249);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_250 = x_19;
} else {
 lean_dec_ref(x_19);
 x_250 = lean_box(0);
}
x_251 = lean_array_get_size(x_247);
x_252 = lean_nat_dec_lt(x_3, x_251);
lean_dec(x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_14);
if (lean_is_scalar(x_250)) {
 x_253 = lean_alloc_ctor(0, 3, 0);
} else {
 x_253 = x_250;
}
lean_ctor_set(x_253, 0, x_247);
lean_ctor_set(x_253, 1, x_248);
lean_ctor_set(x_253, 2, x_249);
if (lean_is_scalar(x_246)) {
 x_254 = lean_alloc_ctor(0, 4, 0);
} else {
 x_254 = x_246;
}
lean_ctor_set(x_254, 0, x_243);
lean_ctor_set(x_254, 1, x_244);
lean_ctor_set(x_254, 2, x_245);
lean_ctor_set(x_254, 3, x_253);
x_255 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_255, 0, x_227);
lean_ctor_set(x_255, 1, x_228);
lean_ctor_set(x_255, 2, x_229);
lean_ctor_set(x_255, 3, x_230);
lean_ctor_set(x_255, 4, x_231);
lean_ctor_set(x_255, 5, x_232);
lean_ctor_set(x_255, 6, x_233);
lean_ctor_set(x_255, 7, x_234);
lean_ctor_set(x_255, 8, x_236);
lean_ctor_set(x_255, 9, x_237);
lean_ctor_set(x_255, 10, x_238);
lean_ctor_set(x_255, 11, x_239);
lean_ctor_set(x_255, 12, x_240);
lean_ctor_set(x_255, 13, x_241);
lean_ctor_set(x_255, 14, x_254);
lean_ctor_set(x_255, 15, x_242);
lean_ctor_set_uint8(x_255, sizeof(void*)*16, x_235);
x_256 = lean_st_ref_set(x_4, x_255, x_20);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_258 = x_256;
} else {
 lean_dec_ref(x_256);
 x_258 = lean_box(0);
}
x_259 = lean_box(0);
if (lean_is_scalar(x_258)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_258;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_257);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_261 = lean_array_fget(x_247, x_3);
x_262 = lean_box(0);
x_263 = lean_array_fset(x_247, x_3, x_262);
x_264 = lean_ctor_get(x_261, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_261, 1);
lean_inc(x_265);
x_266 = lean_ctor_get(x_261, 2);
lean_inc(x_266);
x_267 = lean_ctor_get(x_261, 3);
lean_inc(x_267);
x_268 = lean_ctor_get(x_261, 4);
lean_inc(x_268);
x_269 = lean_ctor_get(x_261, 5);
lean_inc(x_269);
x_270 = lean_ctor_get(x_261, 6);
lean_inc(x_270);
x_271 = lean_ctor_get(x_261, 7);
lean_inc(x_271);
x_272 = lean_ctor_get(x_261, 8);
lean_inc(x_272);
x_273 = lean_ctor_get(x_261, 9);
lean_inc(x_273);
x_274 = lean_ctor_get(x_261, 10);
lean_inc(x_274);
x_275 = lean_ctor_get(x_261, 11);
lean_inc(x_275);
x_276 = lean_ctor_get(x_261, 12);
lean_inc(x_276);
x_277 = lean_ctor_get(x_261, 13);
lean_inc(x_277);
x_278 = lean_ctor_get(x_261, 14);
lean_inc(x_278);
x_279 = lean_ctor_get(x_261, 15);
lean_inc(x_279);
x_280 = lean_ctor_get(x_261, 16);
lean_inc(x_280);
x_281 = lean_ctor_get(x_261, 17);
lean_inc(x_281);
x_282 = lean_ctor_get(x_261, 18);
lean_inc(x_282);
x_283 = lean_ctor_get(x_261, 19);
lean_inc(x_283);
x_284 = lean_ctor_get(x_261, 20);
lean_inc(x_284);
x_285 = lean_ctor_get(x_261, 21);
lean_inc(x_285);
x_286 = lean_ctor_get(x_261, 22);
lean_inc(x_286);
x_287 = lean_ctor_get(x_261, 23);
lean_inc(x_287);
x_288 = lean_ctor_get(x_261, 24);
lean_inc(x_288);
x_289 = lean_ctor_get(x_261, 25);
lean_inc(x_289);
x_290 = lean_ctor_get(x_261, 26);
lean_inc(x_290);
x_291 = lean_ctor_get(x_261, 27);
lean_inc(x_291);
x_292 = lean_ctor_get(x_261, 28);
lean_inc(x_292);
x_293 = lean_ctor_get(x_261, 29);
lean_inc(x_293);
x_294 = lean_ctor_get(x_261, 30);
lean_inc(x_294);
x_295 = lean_ctor_get(x_261, 31);
lean_inc(x_295);
x_296 = lean_ctor_get(x_261, 32);
lean_inc(x_296);
x_297 = lean_ctor_get_uint8(x_261, sizeof(void*)*39);
x_298 = lean_ctor_get(x_261, 33);
lean_inc(x_298);
x_299 = lean_ctor_get(x_261, 34);
lean_inc(x_299);
x_300 = lean_ctor_get(x_261, 35);
lean_inc(x_300);
x_301 = lean_ctor_get(x_261, 36);
lean_inc(x_301);
x_302 = lean_ctor_get(x_261, 37);
lean_inc(x_302);
x_303 = lean_ctor_get(x_261, 38);
lean_inc(x_303);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 lean_ctor_release(x_261, 4);
 lean_ctor_release(x_261, 5);
 lean_ctor_release(x_261, 6);
 lean_ctor_release(x_261, 7);
 lean_ctor_release(x_261, 8);
 lean_ctor_release(x_261, 9);
 lean_ctor_release(x_261, 10);
 lean_ctor_release(x_261, 11);
 lean_ctor_release(x_261, 12);
 lean_ctor_release(x_261, 13);
 lean_ctor_release(x_261, 14);
 lean_ctor_release(x_261, 15);
 lean_ctor_release(x_261, 16);
 lean_ctor_release(x_261, 17);
 lean_ctor_release(x_261, 18);
 lean_ctor_release(x_261, 19);
 lean_ctor_release(x_261, 20);
 lean_ctor_release(x_261, 21);
 lean_ctor_release(x_261, 22);
 lean_ctor_release(x_261, 23);
 lean_ctor_release(x_261, 24);
 lean_ctor_release(x_261, 25);
 lean_ctor_release(x_261, 26);
 lean_ctor_release(x_261, 27);
 lean_ctor_release(x_261, 28);
 lean_ctor_release(x_261, 29);
 lean_ctor_release(x_261, 30);
 lean_ctor_release(x_261, 31);
 lean_ctor_release(x_261, 32);
 lean_ctor_release(x_261, 33);
 lean_ctor_release(x_261, 34);
 lean_ctor_release(x_261, 35);
 lean_ctor_release(x_261, 36);
 lean_ctor_release(x_261, 37);
 lean_ctor_release(x_261, 38);
 x_304 = x_261;
} else {
 lean_dec_ref(x_261);
 x_304 = lean_box(0);
}
x_305 = l_Lean_PersistentArray_push___rarg(x_303, x_14);
if (lean_is_scalar(x_304)) {
 x_306 = lean_alloc_ctor(0, 39, 1);
} else {
 x_306 = x_304;
}
lean_ctor_set(x_306, 0, x_264);
lean_ctor_set(x_306, 1, x_265);
lean_ctor_set(x_306, 2, x_266);
lean_ctor_set(x_306, 3, x_267);
lean_ctor_set(x_306, 4, x_268);
lean_ctor_set(x_306, 5, x_269);
lean_ctor_set(x_306, 6, x_270);
lean_ctor_set(x_306, 7, x_271);
lean_ctor_set(x_306, 8, x_272);
lean_ctor_set(x_306, 9, x_273);
lean_ctor_set(x_306, 10, x_274);
lean_ctor_set(x_306, 11, x_275);
lean_ctor_set(x_306, 12, x_276);
lean_ctor_set(x_306, 13, x_277);
lean_ctor_set(x_306, 14, x_278);
lean_ctor_set(x_306, 15, x_279);
lean_ctor_set(x_306, 16, x_280);
lean_ctor_set(x_306, 17, x_281);
lean_ctor_set(x_306, 18, x_282);
lean_ctor_set(x_306, 19, x_283);
lean_ctor_set(x_306, 20, x_284);
lean_ctor_set(x_306, 21, x_285);
lean_ctor_set(x_306, 22, x_286);
lean_ctor_set(x_306, 23, x_287);
lean_ctor_set(x_306, 24, x_288);
lean_ctor_set(x_306, 25, x_289);
lean_ctor_set(x_306, 26, x_290);
lean_ctor_set(x_306, 27, x_291);
lean_ctor_set(x_306, 28, x_292);
lean_ctor_set(x_306, 29, x_293);
lean_ctor_set(x_306, 30, x_294);
lean_ctor_set(x_306, 31, x_295);
lean_ctor_set(x_306, 32, x_296);
lean_ctor_set(x_306, 33, x_298);
lean_ctor_set(x_306, 34, x_299);
lean_ctor_set(x_306, 35, x_300);
lean_ctor_set(x_306, 36, x_301);
lean_ctor_set(x_306, 37, x_302);
lean_ctor_set(x_306, 38, x_305);
lean_ctor_set_uint8(x_306, sizeof(void*)*39, x_297);
x_307 = lean_array_fset(x_263, x_3, x_306);
if (lean_is_scalar(x_250)) {
 x_308 = lean_alloc_ctor(0, 3, 0);
} else {
 x_308 = x_250;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_248);
lean_ctor_set(x_308, 2, x_249);
if (lean_is_scalar(x_246)) {
 x_309 = lean_alloc_ctor(0, 4, 0);
} else {
 x_309 = x_246;
}
lean_ctor_set(x_309, 0, x_243);
lean_ctor_set(x_309, 1, x_244);
lean_ctor_set(x_309, 2, x_245);
lean_ctor_set(x_309, 3, x_308);
x_310 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_310, 0, x_227);
lean_ctor_set(x_310, 1, x_228);
lean_ctor_set(x_310, 2, x_229);
lean_ctor_set(x_310, 3, x_230);
lean_ctor_set(x_310, 4, x_231);
lean_ctor_set(x_310, 5, x_232);
lean_ctor_set(x_310, 6, x_233);
lean_ctor_set(x_310, 7, x_234);
lean_ctor_set(x_310, 8, x_236);
lean_ctor_set(x_310, 9, x_237);
lean_ctor_set(x_310, 10, x_238);
lean_ctor_set(x_310, 11, x_239);
lean_ctor_set(x_310, 12, x_240);
lean_ctor_set(x_310, 13, x_241);
lean_ctor_set(x_310, 14, x_309);
lean_ctor_set(x_310, 15, x_242);
lean_ctor_set_uint8(x_310, sizeof(void*)*16, x_235);
x_311 = lean_st_ref_set(x_4, x_310, x_20);
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_313 = x_311;
} else {
 lean_dec_ref(x_311);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_262);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
}
else
{
uint8_t x_315; 
x_315 = !lean_is_exclusive(x_13);
if (x_315 == 0)
{
return x_13;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_13, 0);
x_317 = lean_ctor_get(x_13, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_13);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ignored", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3;
x_3 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3;
x_13 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lambda__1(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_MessageData_ofExpr(x_23);
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_25);
lean_ctor_set(x_13, 0, x_26);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_12, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lambda__1(x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_29);
return x_31;
}
else
{
uint8_t x_32; 
lean_free_object(x_13);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_dec(x_13);
x_37 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_MessageData_ofExpr(x_38);
x_41 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_12, x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lambda__1(x_1, x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
lean_dec(x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_37, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_50 = x_37;
} else {
 lean_dec_ref(x_37);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
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
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__6;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 6);
lean_inc(x_19);
x_20 = lean_ctor_get(x_9, 7);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 8);
lean_inc(x_21);
x_22 = lean_ctor_get(x_9, 9);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 10);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*13);
x_25 = lean_ctor_get(x_9, 11);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_9, sizeof(void*)*13 + 1);
x_27 = lean_ctor_get(x_9, 12);
lean_inc(x_27);
x_28 = lean_nat_dec_eq(x_16, x_17);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_9, 12);
lean_dec(x_30);
x_31 = lean_ctor_get(x_9, 11);
lean_dec(x_31);
x_32 = lean_ctor_get(x_9, 10);
lean_dec(x_32);
x_33 = lean_ctor_get(x_9, 9);
lean_dec(x_33);
x_34 = lean_ctor_get(x_9, 8);
lean_dec(x_34);
x_35 = lean_ctor_get(x_9, 7);
lean_dec(x_35);
x_36 = lean_ctor_get(x_9, 6);
lean_dec(x_36);
x_37 = lean_ctor_get(x_9, 5);
lean_dec(x_37);
x_38 = lean_ctor_get(x_9, 4);
lean_dec(x_38);
x_39 = lean_ctor_get(x_9, 3);
lean_dec(x_39);
x_40 = lean_ctor_get(x_9, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_9, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_9, 0);
lean_dec(x_42);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_16, x_43);
lean_dec(x_16);
lean_ctor_set(x_9, 3, x_44);
x_45 = l_Lean_Grind_Linarith_Poly_findVarToSubst(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_9);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_dec(x_45);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = l_Lean_Grind_Linarith_Poly_coeff(x_59, x_57);
lean_dec(x_59);
lean_inc(x_1);
x_61 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_60, x_57, x_58, x_56, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_55);
lean_dec(x_57);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_63);
lean_dec(x_9);
lean_dec(x_1);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = lean_box(0);
lean_ctor_set(x_64, 0, x_67);
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_64);
if (x_71 == 0)
{
return x_64;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_64, 0);
x_73 = lean_ctor_get(x_64, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_64);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_1);
x_75 = lean_ctor_get(x_61, 1);
lean_inc(x_75);
lean_dec(x_61);
x_76 = lean_ctor_get(x_62, 0);
lean_inc(x_76);
lean_dec(x_62);
x_1 = x_76;
x_11 = x_75;
goto _start;
}
}
else
{
uint8_t x_78; 
lean_dec(x_9);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_61);
if (x_78 == 0)
{
return x_61;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_61, 0);
x_80 = lean_ctor_get(x_61, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_61);
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
lean_dec(x_9);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_45);
if (x_82 == 0)
{
return x_45;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_45, 0);
x_84 = lean_ctor_get(x_45, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_45);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_9);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_add(x_16, x_86);
lean_dec(x_16);
x_88 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_88, 0, x_13);
lean_ctor_set(x_88, 1, x_14);
lean_ctor_set(x_88, 2, x_15);
lean_ctor_set(x_88, 3, x_87);
lean_ctor_set(x_88, 4, x_17);
lean_ctor_set(x_88, 5, x_18);
lean_ctor_set(x_88, 6, x_19);
lean_ctor_set(x_88, 7, x_20);
lean_ctor_set(x_88, 8, x_21);
lean_ctor_set(x_88, 9, x_22);
lean_ctor_set(x_88, 10, x_23);
lean_ctor_set(x_88, 11, x_25);
lean_ctor_set(x_88, 12, x_27);
lean_ctor_set_uint8(x_88, sizeof(void*)*13, x_24);
lean_ctor_set_uint8(x_88, sizeof(void*)*13 + 1, x_26);
x_89 = l_Lean_Grind_Linarith_Poly_findVarToSubst(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_88, x_10, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_88);
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
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_1);
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
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
lean_dec(x_90);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_89, 1);
lean_inc(x_97);
lean_dec(x_89);
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = l_Lean_Grind_Linarith_Poly_coeff(x_101, x_99);
lean_dec(x_101);
lean_inc(x_1);
x_103 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_102, x_99, x_100, x_98, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_88, x_10, x_97);
lean_dec(x_99);
lean_dec(x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_88, x_10, x_105);
lean_dec(x_88);
lean_dec(x_1);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_106, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_113 = x_106;
} else {
 lean_dec_ref(x_106);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_1);
x_115 = lean_ctor_get(x_103, 1);
lean_inc(x_115);
lean_dec(x_103);
x_116 = lean_ctor_get(x_104, 0);
lean_inc(x_116);
lean_dec(x_104);
x_1 = x_116;
x_9 = x_88;
x_11 = x_115;
goto _start;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_88);
lean_dec(x_1);
x_118 = lean_ctor_get(x_103, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_103, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_120 = x_103;
} else {
 lean_dec_ref(x_103);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_88);
lean_dec(x_1);
x_122 = lean_ctor_get(x_89, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_89, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_124 = x_89;
} else {
 lean_dec_ref(x_89);
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
}
else
{
lean_object* x_126; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_126 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___spec__1(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_126;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_usize_shift_right(x_4, x_5);
x_9 = 1;
x_10 = lean_usize_shift_left(x_9, x_5);
x_11 = lean_usize_sub(x_10, x_9);
x_12 = lean_usize_land(x_4, x_11);
x_13 = 5;
x_14 = lean_usize_sub(x_5, x_13);
x_15 = lean_usize_to_nat(x_8);
x_16 = lean_array_get_size(x_7);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_7, x_15);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_7, x_15, x_19);
x_21 = l_Lean_PersistentArray_modifyAux___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__2(x_1, x_2, x_18, x_12, x_14);
x_22 = lean_array_fset(x_20, x_15, x_21);
lean_dec(x_15);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_usize_shift_right(x_4, x_5);
x_25 = 1;
x_26 = lean_usize_shift_left(x_25, x_5);
x_27 = lean_usize_sub(x_26, x_25);
x_28 = lean_usize_land(x_4, x_27);
x_29 = 5;
x_30 = lean_usize_sub(x_5, x_29);
x_31 = lean_usize_to_nat(x_24);
x_32 = lean_array_get_size(x_23);
x_33 = lean_nat_dec_lt(x_31, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_23);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_array_fget(x_23, x_31);
x_36 = lean_box(0);
x_37 = lean_array_fset(x_23, x_31, x_36);
x_38 = l_Lean_PersistentArray_modifyAux___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__2(x_1, x_2, x_35, x_28, x_30);
x_39 = lean_array_fset(x_37, x_31, x_38);
lean_dec(x_31);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_3);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_3, 0);
x_43 = lean_usize_to_nat(x_4);
x_44 = lean_array_get_size(x_42);
x_45 = lean_nat_dec_lt(x_43, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_dec(x_43);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_array_fget(x_42, x_43);
x_47 = lean_box(0);
x_48 = lean_array_fset(x_42, x_43, x_47);
x_49 = l_Lean_PersistentArray_push___rarg(x_46, x_1);
x_50 = lean_array_fset(x_48, x_43, x_49);
lean_dec(x_43);
lean_ctor_set(x_3, 0, x_50);
return x_3;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
lean_dec(x_3);
x_52 = lean_usize_to_nat(x_4);
x_53 = lean_array_get_size(x_51);
x_54 = lean_nat_dec_lt(x_52, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_52);
lean_dec(x_1);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_51);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_array_fget(x_51, x_52);
x_57 = lean_box(0);
x_58 = lean_array_fset(x_51, x_52, x_57);
x_59 = l_Lean_PersistentArray_push___rarg(x_56, x_1);
x_60 = lean_array_fset(x_58, x_52, x_59);
lean_dec(x_52);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = l_Lean_PersistentArray_modifyAux___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__2(x_1, x_2, x_6, x_11, x_8);
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
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_7, x_13);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_7, x_13, x_17);
x_19 = l_Lean_PersistentArray_push___rarg(x_16, x_1);
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
x_28 = l_Lean_PersistentArray_modifyAux___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__2(x_1, x_2, x_21, x_27, x_24);
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
lean_dec(x_1);
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
x_37 = l_Lean_PersistentArray_push___rarg(x_34, x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Grind_Linarith_Poly_updateOccs(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_40 = lean_st_ref_take(x_6, x_16);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 14);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_41, 14);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_42, 3);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_43);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_43, 0);
x_51 = lean_array_get_size(x_50);
x_52 = lean_nat_dec_lt(x_5, x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_st_ref_set(x_6, x_41, x_44);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_17 = x_54;
goto block_39;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_array_fget(x_50, x_5);
x_56 = lean_box(0);
x_57 = lean_array_fset(x_50, x_5, x_56);
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_55, 31);
x_60 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1;
lean_inc(x_2);
x_61 = l_Lean_PersistentArray_modify___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__1(x_2, x_60, x_59, x_3);
lean_ctor_set(x_55, 31, x_61);
x_62 = lean_array_fset(x_57, x_5, x_55);
lean_ctor_set(x_43, 0, x_62);
x_63 = lean_st_ref_set(x_6, x_41, x_44);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_17 = x_64;
goto block_39;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_65 = lean_ctor_get(x_55, 0);
x_66 = lean_ctor_get(x_55, 1);
x_67 = lean_ctor_get(x_55, 2);
x_68 = lean_ctor_get(x_55, 3);
x_69 = lean_ctor_get(x_55, 4);
x_70 = lean_ctor_get(x_55, 5);
x_71 = lean_ctor_get(x_55, 6);
x_72 = lean_ctor_get(x_55, 7);
x_73 = lean_ctor_get(x_55, 8);
x_74 = lean_ctor_get(x_55, 9);
x_75 = lean_ctor_get(x_55, 10);
x_76 = lean_ctor_get(x_55, 11);
x_77 = lean_ctor_get(x_55, 12);
x_78 = lean_ctor_get(x_55, 13);
x_79 = lean_ctor_get(x_55, 14);
x_80 = lean_ctor_get(x_55, 15);
x_81 = lean_ctor_get(x_55, 16);
x_82 = lean_ctor_get(x_55, 17);
x_83 = lean_ctor_get(x_55, 18);
x_84 = lean_ctor_get(x_55, 19);
x_85 = lean_ctor_get(x_55, 20);
x_86 = lean_ctor_get(x_55, 21);
x_87 = lean_ctor_get(x_55, 22);
x_88 = lean_ctor_get(x_55, 23);
x_89 = lean_ctor_get(x_55, 24);
x_90 = lean_ctor_get(x_55, 25);
x_91 = lean_ctor_get(x_55, 26);
x_92 = lean_ctor_get(x_55, 27);
x_93 = lean_ctor_get(x_55, 28);
x_94 = lean_ctor_get(x_55, 29);
x_95 = lean_ctor_get(x_55, 30);
x_96 = lean_ctor_get(x_55, 31);
x_97 = lean_ctor_get(x_55, 32);
x_98 = lean_ctor_get_uint8(x_55, sizeof(void*)*39);
x_99 = lean_ctor_get(x_55, 33);
x_100 = lean_ctor_get(x_55, 34);
x_101 = lean_ctor_get(x_55, 35);
x_102 = lean_ctor_get(x_55, 36);
x_103 = lean_ctor_get(x_55, 37);
x_104 = lean_ctor_get(x_55, 38);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
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
lean_inc(x_80);
lean_inc(x_79);
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
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_55);
x_105 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1;
lean_inc(x_2);
x_106 = l_Lean_PersistentArray_modify___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__1(x_2, x_105, x_96, x_3);
x_107 = lean_alloc_ctor(0, 39, 1);
lean_ctor_set(x_107, 0, x_65);
lean_ctor_set(x_107, 1, x_66);
lean_ctor_set(x_107, 2, x_67);
lean_ctor_set(x_107, 3, x_68);
lean_ctor_set(x_107, 4, x_69);
lean_ctor_set(x_107, 5, x_70);
lean_ctor_set(x_107, 6, x_71);
lean_ctor_set(x_107, 7, x_72);
lean_ctor_set(x_107, 8, x_73);
lean_ctor_set(x_107, 9, x_74);
lean_ctor_set(x_107, 10, x_75);
lean_ctor_set(x_107, 11, x_76);
lean_ctor_set(x_107, 12, x_77);
lean_ctor_set(x_107, 13, x_78);
lean_ctor_set(x_107, 14, x_79);
lean_ctor_set(x_107, 15, x_80);
lean_ctor_set(x_107, 16, x_81);
lean_ctor_set(x_107, 17, x_82);
lean_ctor_set(x_107, 18, x_83);
lean_ctor_set(x_107, 19, x_84);
lean_ctor_set(x_107, 20, x_85);
lean_ctor_set(x_107, 21, x_86);
lean_ctor_set(x_107, 22, x_87);
lean_ctor_set(x_107, 23, x_88);
lean_ctor_set(x_107, 24, x_89);
lean_ctor_set(x_107, 25, x_90);
lean_ctor_set(x_107, 26, x_91);
lean_ctor_set(x_107, 27, x_92);
lean_ctor_set(x_107, 28, x_93);
lean_ctor_set(x_107, 29, x_94);
lean_ctor_set(x_107, 30, x_95);
lean_ctor_set(x_107, 31, x_106);
lean_ctor_set(x_107, 32, x_97);
lean_ctor_set(x_107, 33, x_99);
lean_ctor_set(x_107, 34, x_100);
lean_ctor_set(x_107, 35, x_101);
lean_ctor_set(x_107, 36, x_102);
lean_ctor_set(x_107, 37, x_103);
lean_ctor_set(x_107, 38, x_104);
lean_ctor_set_uint8(x_107, sizeof(void*)*39, x_98);
x_108 = lean_array_fset(x_57, x_5, x_107);
lean_ctor_set(x_43, 0, x_108);
x_109 = lean_st_ref_set(x_6, x_41, x_44);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_17 = x_110;
goto block_39;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_43, 0);
x_112 = lean_ctor_get(x_43, 1);
x_113 = lean_ctor_get(x_43, 2);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_43);
x_114 = lean_array_get_size(x_111);
x_115 = lean_nat_dec_lt(x_5, x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_112);
lean_ctor_set(x_116, 2, x_113);
lean_ctor_set(x_42, 3, x_116);
x_117 = lean_st_ref_set(x_6, x_41, x_44);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_17 = x_118;
goto block_39;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_119 = lean_array_fget(x_111, x_5);
x_120 = lean_box(0);
x_121 = lean_array_fset(x_111, x_5, x_120);
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_119, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_119, 3);
lean_inc(x_125);
x_126 = lean_ctor_get(x_119, 4);
lean_inc(x_126);
x_127 = lean_ctor_get(x_119, 5);
lean_inc(x_127);
x_128 = lean_ctor_get(x_119, 6);
lean_inc(x_128);
x_129 = lean_ctor_get(x_119, 7);
lean_inc(x_129);
x_130 = lean_ctor_get(x_119, 8);
lean_inc(x_130);
x_131 = lean_ctor_get(x_119, 9);
lean_inc(x_131);
x_132 = lean_ctor_get(x_119, 10);
lean_inc(x_132);
x_133 = lean_ctor_get(x_119, 11);
lean_inc(x_133);
x_134 = lean_ctor_get(x_119, 12);
lean_inc(x_134);
x_135 = lean_ctor_get(x_119, 13);
lean_inc(x_135);
x_136 = lean_ctor_get(x_119, 14);
lean_inc(x_136);
x_137 = lean_ctor_get(x_119, 15);
lean_inc(x_137);
x_138 = lean_ctor_get(x_119, 16);
lean_inc(x_138);
x_139 = lean_ctor_get(x_119, 17);
lean_inc(x_139);
x_140 = lean_ctor_get(x_119, 18);
lean_inc(x_140);
x_141 = lean_ctor_get(x_119, 19);
lean_inc(x_141);
x_142 = lean_ctor_get(x_119, 20);
lean_inc(x_142);
x_143 = lean_ctor_get(x_119, 21);
lean_inc(x_143);
x_144 = lean_ctor_get(x_119, 22);
lean_inc(x_144);
x_145 = lean_ctor_get(x_119, 23);
lean_inc(x_145);
x_146 = lean_ctor_get(x_119, 24);
lean_inc(x_146);
x_147 = lean_ctor_get(x_119, 25);
lean_inc(x_147);
x_148 = lean_ctor_get(x_119, 26);
lean_inc(x_148);
x_149 = lean_ctor_get(x_119, 27);
lean_inc(x_149);
x_150 = lean_ctor_get(x_119, 28);
lean_inc(x_150);
x_151 = lean_ctor_get(x_119, 29);
lean_inc(x_151);
x_152 = lean_ctor_get(x_119, 30);
lean_inc(x_152);
x_153 = lean_ctor_get(x_119, 31);
lean_inc(x_153);
x_154 = lean_ctor_get(x_119, 32);
lean_inc(x_154);
x_155 = lean_ctor_get_uint8(x_119, sizeof(void*)*39);
x_156 = lean_ctor_get(x_119, 33);
lean_inc(x_156);
x_157 = lean_ctor_get(x_119, 34);
lean_inc(x_157);
x_158 = lean_ctor_get(x_119, 35);
lean_inc(x_158);
x_159 = lean_ctor_get(x_119, 36);
lean_inc(x_159);
x_160 = lean_ctor_get(x_119, 37);
lean_inc(x_160);
x_161 = lean_ctor_get(x_119, 38);
lean_inc(x_161);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 lean_ctor_release(x_119, 5);
 lean_ctor_release(x_119, 6);
 lean_ctor_release(x_119, 7);
 lean_ctor_release(x_119, 8);
 lean_ctor_release(x_119, 9);
 lean_ctor_release(x_119, 10);
 lean_ctor_release(x_119, 11);
 lean_ctor_release(x_119, 12);
 lean_ctor_release(x_119, 13);
 lean_ctor_release(x_119, 14);
 lean_ctor_release(x_119, 15);
 lean_ctor_release(x_119, 16);
 lean_ctor_release(x_119, 17);
 lean_ctor_release(x_119, 18);
 lean_ctor_release(x_119, 19);
 lean_ctor_release(x_119, 20);
 lean_ctor_release(x_119, 21);
 lean_ctor_release(x_119, 22);
 lean_ctor_release(x_119, 23);
 lean_ctor_release(x_119, 24);
 lean_ctor_release(x_119, 25);
 lean_ctor_release(x_119, 26);
 lean_ctor_release(x_119, 27);
 lean_ctor_release(x_119, 28);
 lean_ctor_release(x_119, 29);
 lean_ctor_release(x_119, 30);
 lean_ctor_release(x_119, 31);
 lean_ctor_release(x_119, 32);
 lean_ctor_release(x_119, 33);
 lean_ctor_release(x_119, 34);
 lean_ctor_release(x_119, 35);
 lean_ctor_release(x_119, 36);
 lean_ctor_release(x_119, 37);
 lean_ctor_release(x_119, 38);
 x_162 = x_119;
} else {
 lean_dec_ref(x_119);
 x_162 = lean_box(0);
}
x_163 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1;
lean_inc(x_2);
x_164 = l_Lean_PersistentArray_modify___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__1(x_2, x_163, x_153, x_3);
if (lean_is_scalar(x_162)) {
 x_165 = lean_alloc_ctor(0, 39, 1);
} else {
 x_165 = x_162;
}
lean_ctor_set(x_165, 0, x_122);
lean_ctor_set(x_165, 1, x_123);
lean_ctor_set(x_165, 2, x_124);
lean_ctor_set(x_165, 3, x_125);
lean_ctor_set(x_165, 4, x_126);
lean_ctor_set(x_165, 5, x_127);
lean_ctor_set(x_165, 6, x_128);
lean_ctor_set(x_165, 7, x_129);
lean_ctor_set(x_165, 8, x_130);
lean_ctor_set(x_165, 9, x_131);
lean_ctor_set(x_165, 10, x_132);
lean_ctor_set(x_165, 11, x_133);
lean_ctor_set(x_165, 12, x_134);
lean_ctor_set(x_165, 13, x_135);
lean_ctor_set(x_165, 14, x_136);
lean_ctor_set(x_165, 15, x_137);
lean_ctor_set(x_165, 16, x_138);
lean_ctor_set(x_165, 17, x_139);
lean_ctor_set(x_165, 18, x_140);
lean_ctor_set(x_165, 19, x_141);
lean_ctor_set(x_165, 20, x_142);
lean_ctor_set(x_165, 21, x_143);
lean_ctor_set(x_165, 22, x_144);
lean_ctor_set(x_165, 23, x_145);
lean_ctor_set(x_165, 24, x_146);
lean_ctor_set(x_165, 25, x_147);
lean_ctor_set(x_165, 26, x_148);
lean_ctor_set(x_165, 27, x_149);
lean_ctor_set(x_165, 28, x_150);
lean_ctor_set(x_165, 29, x_151);
lean_ctor_set(x_165, 30, x_152);
lean_ctor_set(x_165, 31, x_164);
lean_ctor_set(x_165, 32, x_154);
lean_ctor_set(x_165, 33, x_156);
lean_ctor_set(x_165, 34, x_157);
lean_ctor_set(x_165, 35, x_158);
lean_ctor_set(x_165, 36, x_159);
lean_ctor_set(x_165, 37, x_160);
lean_ctor_set(x_165, 38, x_161);
lean_ctor_set_uint8(x_165, sizeof(void*)*39, x_155);
x_166 = lean_array_fset(x_121, x_5, x_165);
x_167 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_112);
lean_ctor_set(x_167, 2, x_113);
lean_ctor_set(x_42, 3, x_167);
x_168 = lean_st_ref_set(x_6, x_41, x_44);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_17 = x_169;
goto block_39;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_170 = lean_ctor_get(x_42, 0);
x_171 = lean_ctor_get(x_42, 1);
x_172 = lean_ctor_get(x_42, 2);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_42);
x_173 = lean_ctor_get(x_43, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_43, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_43, 2);
lean_inc(x_175);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 x_176 = x_43;
} else {
 lean_dec_ref(x_43);
 x_176 = lean_box(0);
}
x_177 = lean_array_get_size(x_173);
x_178 = lean_nat_dec_lt(x_5, x_177);
lean_dec(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
if (lean_is_scalar(x_176)) {
 x_179 = lean_alloc_ctor(0, 3, 0);
} else {
 x_179 = x_176;
}
lean_ctor_set(x_179, 0, x_173);
lean_ctor_set(x_179, 1, x_174);
lean_ctor_set(x_179, 2, x_175);
x_180 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_180, 0, x_170);
lean_ctor_set(x_180, 1, x_171);
lean_ctor_set(x_180, 2, x_172);
lean_ctor_set(x_180, 3, x_179);
lean_ctor_set(x_41, 14, x_180);
x_181 = lean_st_ref_set(x_6, x_41, x_44);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_17 = x_182;
goto block_39;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_183 = lean_array_fget(x_173, x_5);
x_184 = lean_box(0);
x_185 = lean_array_fset(x_173, x_5, x_184);
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_183, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_183, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_183, 4);
lean_inc(x_190);
x_191 = lean_ctor_get(x_183, 5);
lean_inc(x_191);
x_192 = lean_ctor_get(x_183, 6);
lean_inc(x_192);
x_193 = lean_ctor_get(x_183, 7);
lean_inc(x_193);
x_194 = lean_ctor_get(x_183, 8);
lean_inc(x_194);
x_195 = lean_ctor_get(x_183, 9);
lean_inc(x_195);
x_196 = lean_ctor_get(x_183, 10);
lean_inc(x_196);
x_197 = lean_ctor_get(x_183, 11);
lean_inc(x_197);
x_198 = lean_ctor_get(x_183, 12);
lean_inc(x_198);
x_199 = lean_ctor_get(x_183, 13);
lean_inc(x_199);
x_200 = lean_ctor_get(x_183, 14);
lean_inc(x_200);
x_201 = lean_ctor_get(x_183, 15);
lean_inc(x_201);
x_202 = lean_ctor_get(x_183, 16);
lean_inc(x_202);
x_203 = lean_ctor_get(x_183, 17);
lean_inc(x_203);
x_204 = lean_ctor_get(x_183, 18);
lean_inc(x_204);
x_205 = lean_ctor_get(x_183, 19);
lean_inc(x_205);
x_206 = lean_ctor_get(x_183, 20);
lean_inc(x_206);
x_207 = lean_ctor_get(x_183, 21);
lean_inc(x_207);
x_208 = lean_ctor_get(x_183, 22);
lean_inc(x_208);
x_209 = lean_ctor_get(x_183, 23);
lean_inc(x_209);
x_210 = lean_ctor_get(x_183, 24);
lean_inc(x_210);
x_211 = lean_ctor_get(x_183, 25);
lean_inc(x_211);
x_212 = lean_ctor_get(x_183, 26);
lean_inc(x_212);
x_213 = lean_ctor_get(x_183, 27);
lean_inc(x_213);
x_214 = lean_ctor_get(x_183, 28);
lean_inc(x_214);
x_215 = lean_ctor_get(x_183, 29);
lean_inc(x_215);
x_216 = lean_ctor_get(x_183, 30);
lean_inc(x_216);
x_217 = lean_ctor_get(x_183, 31);
lean_inc(x_217);
x_218 = lean_ctor_get(x_183, 32);
lean_inc(x_218);
x_219 = lean_ctor_get_uint8(x_183, sizeof(void*)*39);
x_220 = lean_ctor_get(x_183, 33);
lean_inc(x_220);
x_221 = lean_ctor_get(x_183, 34);
lean_inc(x_221);
x_222 = lean_ctor_get(x_183, 35);
lean_inc(x_222);
x_223 = lean_ctor_get(x_183, 36);
lean_inc(x_223);
x_224 = lean_ctor_get(x_183, 37);
lean_inc(x_224);
x_225 = lean_ctor_get(x_183, 38);
lean_inc(x_225);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 lean_ctor_release(x_183, 3);
 lean_ctor_release(x_183, 4);
 lean_ctor_release(x_183, 5);
 lean_ctor_release(x_183, 6);
 lean_ctor_release(x_183, 7);
 lean_ctor_release(x_183, 8);
 lean_ctor_release(x_183, 9);
 lean_ctor_release(x_183, 10);
 lean_ctor_release(x_183, 11);
 lean_ctor_release(x_183, 12);
 lean_ctor_release(x_183, 13);
 lean_ctor_release(x_183, 14);
 lean_ctor_release(x_183, 15);
 lean_ctor_release(x_183, 16);
 lean_ctor_release(x_183, 17);
 lean_ctor_release(x_183, 18);
 lean_ctor_release(x_183, 19);
 lean_ctor_release(x_183, 20);
 lean_ctor_release(x_183, 21);
 lean_ctor_release(x_183, 22);
 lean_ctor_release(x_183, 23);
 lean_ctor_release(x_183, 24);
 lean_ctor_release(x_183, 25);
 lean_ctor_release(x_183, 26);
 lean_ctor_release(x_183, 27);
 lean_ctor_release(x_183, 28);
 lean_ctor_release(x_183, 29);
 lean_ctor_release(x_183, 30);
 lean_ctor_release(x_183, 31);
 lean_ctor_release(x_183, 32);
 lean_ctor_release(x_183, 33);
 lean_ctor_release(x_183, 34);
 lean_ctor_release(x_183, 35);
 lean_ctor_release(x_183, 36);
 lean_ctor_release(x_183, 37);
 lean_ctor_release(x_183, 38);
 x_226 = x_183;
} else {
 lean_dec_ref(x_183);
 x_226 = lean_box(0);
}
x_227 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1;
lean_inc(x_2);
x_228 = l_Lean_PersistentArray_modify___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__1(x_2, x_227, x_217, x_3);
if (lean_is_scalar(x_226)) {
 x_229 = lean_alloc_ctor(0, 39, 1);
} else {
 x_229 = x_226;
}
lean_ctor_set(x_229, 0, x_186);
lean_ctor_set(x_229, 1, x_187);
lean_ctor_set(x_229, 2, x_188);
lean_ctor_set(x_229, 3, x_189);
lean_ctor_set(x_229, 4, x_190);
lean_ctor_set(x_229, 5, x_191);
lean_ctor_set(x_229, 6, x_192);
lean_ctor_set(x_229, 7, x_193);
lean_ctor_set(x_229, 8, x_194);
lean_ctor_set(x_229, 9, x_195);
lean_ctor_set(x_229, 10, x_196);
lean_ctor_set(x_229, 11, x_197);
lean_ctor_set(x_229, 12, x_198);
lean_ctor_set(x_229, 13, x_199);
lean_ctor_set(x_229, 14, x_200);
lean_ctor_set(x_229, 15, x_201);
lean_ctor_set(x_229, 16, x_202);
lean_ctor_set(x_229, 17, x_203);
lean_ctor_set(x_229, 18, x_204);
lean_ctor_set(x_229, 19, x_205);
lean_ctor_set(x_229, 20, x_206);
lean_ctor_set(x_229, 21, x_207);
lean_ctor_set(x_229, 22, x_208);
lean_ctor_set(x_229, 23, x_209);
lean_ctor_set(x_229, 24, x_210);
lean_ctor_set(x_229, 25, x_211);
lean_ctor_set(x_229, 26, x_212);
lean_ctor_set(x_229, 27, x_213);
lean_ctor_set(x_229, 28, x_214);
lean_ctor_set(x_229, 29, x_215);
lean_ctor_set(x_229, 30, x_216);
lean_ctor_set(x_229, 31, x_228);
lean_ctor_set(x_229, 32, x_218);
lean_ctor_set(x_229, 33, x_220);
lean_ctor_set(x_229, 34, x_221);
lean_ctor_set(x_229, 35, x_222);
lean_ctor_set(x_229, 36, x_223);
lean_ctor_set(x_229, 37, x_224);
lean_ctor_set(x_229, 38, x_225);
lean_ctor_set_uint8(x_229, sizeof(void*)*39, x_219);
x_230 = lean_array_fset(x_185, x_5, x_229);
if (lean_is_scalar(x_176)) {
 x_231 = lean_alloc_ctor(0, 3, 0);
} else {
 x_231 = x_176;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_174);
lean_ctor_set(x_231, 2, x_175);
x_232 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_232, 0, x_170);
lean_ctor_set(x_232, 1, x_171);
lean_ctor_set(x_232, 2, x_172);
lean_ctor_set(x_232, 3, x_231);
lean_ctor_set(x_41, 14, x_232);
x_233 = lean_st_ref_set(x_6, x_41, x_44);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_17 = x_234;
goto block_39;
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_235 = lean_ctor_get(x_41, 0);
x_236 = lean_ctor_get(x_41, 1);
x_237 = lean_ctor_get(x_41, 2);
x_238 = lean_ctor_get(x_41, 3);
x_239 = lean_ctor_get(x_41, 4);
x_240 = lean_ctor_get(x_41, 5);
x_241 = lean_ctor_get(x_41, 6);
x_242 = lean_ctor_get(x_41, 7);
x_243 = lean_ctor_get_uint8(x_41, sizeof(void*)*16);
x_244 = lean_ctor_get(x_41, 8);
x_245 = lean_ctor_get(x_41, 9);
x_246 = lean_ctor_get(x_41, 10);
x_247 = lean_ctor_get(x_41, 11);
x_248 = lean_ctor_get(x_41, 12);
x_249 = lean_ctor_get(x_41, 13);
x_250 = lean_ctor_get(x_41, 15);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_41);
x_251 = lean_ctor_get(x_42, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_42, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_42, 2);
lean_inc(x_253);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_254 = x_42;
} else {
 lean_dec_ref(x_42);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_43, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_43, 1);
lean_inc(x_256);
x_257 = lean_ctor_get(x_43, 2);
lean_inc(x_257);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 x_258 = x_43;
} else {
 lean_dec_ref(x_43);
 x_258 = lean_box(0);
}
x_259 = lean_array_get_size(x_255);
x_260 = lean_nat_dec_lt(x_5, x_259);
lean_dec(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
if (lean_is_scalar(x_258)) {
 x_261 = lean_alloc_ctor(0, 3, 0);
} else {
 x_261 = x_258;
}
lean_ctor_set(x_261, 0, x_255);
lean_ctor_set(x_261, 1, x_256);
lean_ctor_set(x_261, 2, x_257);
if (lean_is_scalar(x_254)) {
 x_262 = lean_alloc_ctor(0, 4, 0);
} else {
 x_262 = x_254;
}
lean_ctor_set(x_262, 0, x_251);
lean_ctor_set(x_262, 1, x_252);
lean_ctor_set(x_262, 2, x_253);
lean_ctor_set(x_262, 3, x_261);
x_263 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_263, 0, x_235);
lean_ctor_set(x_263, 1, x_236);
lean_ctor_set(x_263, 2, x_237);
lean_ctor_set(x_263, 3, x_238);
lean_ctor_set(x_263, 4, x_239);
lean_ctor_set(x_263, 5, x_240);
lean_ctor_set(x_263, 6, x_241);
lean_ctor_set(x_263, 7, x_242);
lean_ctor_set(x_263, 8, x_244);
lean_ctor_set(x_263, 9, x_245);
lean_ctor_set(x_263, 10, x_246);
lean_ctor_set(x_263, 11, x_247);
lean_ctor_set(x_263, 12, x_248);
lean_ctor_set(x_263, 13, x_249);
lean_ctor_set(x_263, 14, x_262);
lean_ctor_set(x_263, 15, x_250);
lean_ctor_set_uint8(x_263, sizeof(void*)*16, x_243);
x_264 = lean_st_ref_set(x_6, x_263, x_44);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
x_17 = x_265;
goto block_39;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_266 = lean_array_fget(x_255, x_5);
x_267 = lean_box(0);
x_268 = lean_array_fset(x_255, x_5, x_267);
x_269 = lean_ctor_get(x_266, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_266, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_266, 2);
lean_inc(x_271);
x_272 = lean_ctor_get(x_266, 3);
lean_inc(x_272);
x_273 = lean_ctor_get(x_266, 4);
lean_inc(x_273);
x_274 = lean_ctor_get(x_266, 5);
lean_inc(x_274);
x_275 = lean_ctor_get(x_266, 6);
lean_inc(x_275);
x_276 = lean_ctor_get(x_266, 7);
lean_inc(x_276);
x_277 = lean_ctor_get(x_266, 8);
lean_inc(x_277);
x_278 = lean_ctor_get(x_266, 9);
lean_inc(x_278);
x_279 = lean_ctor_get(x_266, 10);
lean_inc(x_279);
x_280 = lean_ctor_get(x_266, 11);
lean_inc(x_280);
x_281 = lean_ctor_get(x_266, 12);
lean_inc(x_281);
x_282 = lean_ctor_get(x_266, 13);
lean_inc(x_282);
x_283 = lean_ctor_get(x_266, 14);
lean_inc(x_283);
x_284 = lean_ctor_get(x_266, 15);
lean_inc(x_284);
x_285 = lean_ctor_get(x_266, 16);
lean_inc(x_285);
x_286 = lean_ctor_get(x_266, 17);
lean_inc(x_286);
x_287 = lean_ctor_get(x_266, 18);
lean_inc(x_287);
x_288 = lean_ctor_get(x_266, 19);
lean_inc(x_288);
x_289 = lean_ctor_get(x_266, 20);
lean_inc(x_289);
x_290 = lean_ctor_get(x_266, 21);
lean_inc(x_290);
x_291 = lean_ctor_get(x_266, 22);
lean_inc(x_291);
x_292 = lean_ctor_get(x_266, 23);
lean_inc(x_292);
x_293 = lean_ctor_get(x_266, 24);
lean_inc(x_293);
x_294 = lean_ctor_get(x_266, 25);
lean_inc(x_294);
x_295 = lean_ctor_get(x_266, 26);
lean_inc(x_295);
x_296 = lean_ctor_get(x_266, 27);
lean_inc(x_296);
x_297 = lean_ctor_get(x_266, 28);
lean_inc(x_297);
x_298 = lean_ctor_get(x_266, 29);
lean_inc(x_298);
x_299 = lean_ctor_get(x_266, 30);
lean_inc(x_299);
x_300 = lean_ctor_get(x_266, 31);
lean_inc(x_300);
x_301 = lean_ctor_get(x_266, 32);
lean_inc(x_301);
x_302 = lean_ctor_get_uint8(x_266, sizeof(void*)*39);
x_303 = lean_ctor_get(x_266, 33);
lean_inc(x_303);
x_304 = lean_ctor_get(x_266, 34);
lean_inc(x_304);
x_305 = lean_ctor_get(x_266, 35);
lean_inc(x_305);
x_306 = lean_ctor_get(x_266, 36);
lean_inc(x_306);
x_307 = lean_ctor_get(x_266, 37);
lean_inc(x_307);
x_308 = lean_ctor_get(x_266, 38);
lean_inc(x_308);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 lean_ctor_release(x_266, 2);
 lean_ctor_release(x_266, 3);
 lean_ctor_release(x_266, 4);
 lean_ctor_release(x_266, 5);
 lean_ctor_release(x_266, 6);
 lean_ctor_release(x_266, 7);
 lean_ctor_release(x_266, 8);
 lean_ctor_release(x_266, 9);
 lean_ctor_release(x_266, 10);
 lean_ctor_release(x_266, 11);
 lean_ctor_release(x_266, 12);
 lean_ctor_release(x_266, 13);
 lean_ctor_release(x_266, 14);
 lean_ctor_release(x_266, 15);
 lean_ctor_release(x_266, 16);
 lean_ctor_release(x_266, 17);
 lean_ctor_release(x_266, 18);
 lean_ctor_release(x_266, 19);
 lean_ctor_release(x_266, 20);
 lean_ctor_release(x_266, 21);
 lean_ctor_release(x_266, 22);
 lean_ctor_release(x_266, 23);
 lean_ctor_release(x_266, 24);
 lean_ctor_release(x_266, 25);
 lean_ctor_release(x_266, 26);
 lean_ctor_release(x_266, 27);
 lean_ctor_release(x_266, 28);
 lean_ctor_release(x_266, 29);
 lean_ctor_release(x_266, 30);
 lean_ctor_release(x_266, 31);
 lean_ctor_release(x_266, 32);
 lean_ctor_release(x_266, 33);
 lean_ctor_release(x_266, 34);
 lean_ctor_release(x_266, 35);
 lean_ctor_release(x_266, 36);
 lean_ctor_release(x_266, 37);
 lean_ctor_release(x_266, 38);
 x_309 = x_266;
} else {
 lean_dec_ref(x_266);
 x_309 = lean_box(0);
}
x_310 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1;
lean_inc(x_2);
x_311 = l_Lean_PersistentArray_modify___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__1(x_2, x_310, x_300, x_3);
if (lean_is_scalar(x_309)) {
 x_312 = lean_alloc_ctor(0, 39, 1);
} else {
 x_312 = x_309;
}
lean_ctor_set(x_312, 0, x_269);
lean_ctor_set(x_312, 1, x_270);
lean_ctor_set(x_312, 2, x_271);
lean_ctor_set(x_312, 3, x_272);
lean_ctor_set(x_312, 4, x_273);
lean_ctor_set(x_312, 5, x_274);
lean_ctor_set(x_312, 6, x_275);
lean_ctor_set(x_312, 7, x_276);
lean_ctor_set(x_312, 8, x_277);
lean_ctor_set(x_312, 9, x_278);
lean_ctor_set(x_312, 10, x_279);
lean_ctor_set(x_312, 11, x_280);
lean_ctor_set(x_312, 12, x_281);
lean_ctor_set(x_312, 13, x_282);
lean_ctor_set(x_312, 14, x_283);
lean_ctor_set(x_312, 15, x_284);
lean_ctor_set(x_312, 16, x_285);
lean_ctor_set(x_312, 17, x_286);
lean_ctor_set(x_312, 18, x_287);
lean_ctor_set(x_312, 19, x_288);
lean_ctor_set(x_312, 20, x_289);
lean_ctor_set(x_312, 21, x_290);
lean_ctor_set(x_312, 22, x_291);
lean_ctor_set(x_312, 23, x_292);
lean_ctor_set(x_312, 24, x_293);
lean_ctor_set(x_312, 25, x_294);
lean_ctor_set(x_312, 26, x_295);
lean_ctor_set(x_312, 27, x_296);
lean_ctor_set(x_312, 28, x_297);
lean_ctor_set(x_312, 29, x_298);
lean_ctor_set(x_312, 30, x_299);
lean_ctor_set(x_312, 31, x_311);
lean_ctor_set(x_312, 32, x_301);
lean_ctor_set(x_312, 33, x_303);
lean_ctor_set(x_312, 34, x_304);
lean_ctor_set(x_312, 35, x_305);
lean_ctor_set(x_312, 36, x_306);
lean_ctor_set(x_312, 37, x_307);
lean_ctor_set(x_312, 38, x_308);
lean_ctor_set_uint8(x_312, sizeof(void*)*39, x_302);
x_313 = lean_array_fset(x_268, x_5, x_312);
if (lean_is_scalar(x_258)) {
 x_314 = lean_alloc_ctor(0, 3, 0);
} else {
 x_314 = x_258;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_256);
lean_ctor_set(x_314, 2, x_257);
if (lean_is_scalar(x_254)) {
 x_315 = lean_alloc_ctor(0, 4, 0);
} else {
 x_315 = x_254;
}
lean_ctor_set(x_315, 0, x_251);
lean_ctor_set(x_315, 1, x_252);
lean_ctor_set(x_315, 2, x_253);
lean_ctor_set(x_315, 3, x_314);
x_316 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_316, 0, x_235);
lean_ctor_set(x_316, 1, x_236);
lean_ctor_set(x_316, 2, x_237);
lean_ctor_set(x_316, 3, x_238);
lean_ctor_set(x_316, 4, x_239);
lean_ctor_set(x_316, 5, x_240);
lean_ctor_set(x_316, 6, x_241);
lean_ctor_set(x_316, 7, x_242);
lean_ctor_set(x_316, 8, x_244);
lean_ctor_set(x_316, 9, x_245);
lean_ctor_set(x_316, 10, x_246);
lean_ctor_set(x_316, 11, x_247);
lean_ctor_set(x_316, 12, x_248);
lean_ctor_set(x_316, 13, x_249);
lean_ctor_set(x_316, 14, x_315);
lean_ctor_set(x_316, 15, x_250);
lean_ctor_set_uint8(x_316, sizeof(void*)*16, x_243);
x_317 = lean_st_ref_set(x_6, x_316, x_44);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
lean_dec(x_317);
x_17 = x_318;
goto block_39;
}
}
block_39:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
lean_dec(x_2);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = 0;
x_23 = lean_unbox(x_20);
lean_dec(x_20);
x_24 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_box(0);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_26; 
lean_free_object(x_18);
x_26 = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = 0;
x_30 = lean_unbox(x_27);
lean_dec(x_27);
x_31 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_30, x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
return x_34;
}
}
}
else
{
uint8_t x_35; 
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
}
else
{
uint8_t x_319; 
lean_dec(x_2);
x_319 = !lean_is_exclusive(x_15);
if (x_319 == 0)
{
return x_15;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_15, 0);
x_321 = lean_ctor_get(x_15, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_15);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3;
x_3 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3;
x_3 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_10);
x_13 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__2;
x_25 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__1(x_21, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 1);
x_33 = lean_ctor_get(x_25, 0);
lean_dec(x_33);
x_34 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_MessageData_ofExpr(x_35);
x_38 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_37);
lean_ctor_set(x_25, 0, x_38);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_24, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_36);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__1(x_21, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_42);
lean_dec(x_41);
return x_43;
}
else
{
uint8_t x_44; 
lean_free_object(x_25);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_34);
if (x_44 == 0)
{
return x_34;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_34, 0);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_34);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_dec(x_25);
x_49 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_MessageData_ofExpr(x_50);
x_53 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_24, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_51);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__1(x_21, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_58);
lean_dec(x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_60 = lean_ctor_get(x_49, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_62 = x_49;
} else {
 lean_dec_ref(x_49);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
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
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
lean_dec(x_13);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
x_66 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__4;
x_67 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_64);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_box(0);
x_72 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__2(x_22, x_21, x_65, x_71, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_70);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_65);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_67);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_67, 1);
x_75 = lean_ctor_get(x_67, 0);
lean_dec(x_75);
x_76 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_MessageData_ofExpr(x_77);
x_80 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_67, 7);
lean_ctor_set(x_67, 1, x_79);
lean_ctor_set(x_67, 0, x_80);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_67);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_66, x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_78);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__2(x_22, x_21, x_65, x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_84);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_83);
lean_dec(x_65);
return x_85;
}
else
{
uint8_t x_86; 
lean_free_object(x_67);
lean_dec(x_65);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_76);
if (x_86 == 0)
{
return x_76;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_76, 0);
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_76);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_67, 1);
lean_inc(x_90);
lean_dec(x_67);
x_91 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_MessageData_ofExpr(x_92);
x_95 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_66, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_93);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__2(x_22, x_21, x_65, x_99, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_100);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_99);
lean_dec(x_65);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_65);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_102 = lean_ctor_get(x_91, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_91, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_104 = x_91;
} else {
 lean_dec_ref(x_91);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_106 = !lean_is_exclusive(x_13);
if (x_106 == 0)
{
return x_13;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_13, 0);
x_108 = lean_ctor_get(x_13, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_13);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3;
x_3 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1;
x_13 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_MessageData_ofExpr(x_23);
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_25);
lean_ctor_set(x_13, 0, x_26);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_12, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3(x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_29);
return x_31;
}
else
{
uint8_t x_32; 
lean_free_object(x_13);
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
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_dec(x_13);
x_37 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_MessageData_ofExpr(x_38);
x_41 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_12, x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3(x_1, x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
lean_dec(x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
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
x_48 = lean_ctor_get(x_37, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_50 = x_37;
} else {
 lean_dec_ref(x_37);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__2(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_8, x_7);
if (x_10 == 0)
{
lean_dec(x_5);
return x_9;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_uget(x_6, x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
lean_inc(x_13);
x_15 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__3(x_1, x_2, x_11, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; 
lean_dec(x_13);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_5);
x_18 = 1;
x_19 = lean_usize_add(x_8, x_18);
x_8 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
lean_inc(x_21);
x_22 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__3(x_1, x_2, x_11, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_8, x_27);
x_8 = x_28;
x_9 = x_26;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_4);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_uget(x_5, x_7);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = l_Lean_Grind_Linarith_Poly_coeff(x_15, x_1);
lean_dec(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_18 = lean_int_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_10);
x_20 = lean_array_push(x_14, x_19);
lean_ctor_set(x_11, 1, x_20);
lean_inc(x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_11);
x_22 = 1;
x_23 = lean_usize_add(x_7, x_22);
x_7 = x_23;
x_8 = x_21;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_16);
x_25 = l_Lean_PersistentArray_push___rarg(x_13, x_10);
lean_ctor_set(x_11, 0, x_25);
lean_inc(x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_11);
x_27 = 1;
x_28 = lean_usize_add(x_7, x_27);
x_7 = x_28;
x_8 = x_26;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
x_33 = l_Lean_Grind_Linarith_Poly_coeff(x_32, x_1);
lean_dec(x_32);
x_34 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_35 = lean_int_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_10);
x_37 = lean_array_push(x_31, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_4);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_38);
x_40 = 1;
x_41 = lean_usize_add(x_7, x_40);
x_7 = x_41;
x_8 = x_39;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
lean_dec(x_33);
x_43 = l_Lean_PersistentArray_push___rarg(x_30, x_10);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_31);
lean_inc(x_4);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_44);
x_46 = 1;
x_47 = lean_usize_add(x_7, x_46);
x_7 = x_47;
x_8 = x_45;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_10 = lean_array_size(x_6);
x_11 = 0;
x_12 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__4(x_1, x_2, x_6, x_7, x_8, x_6, x_10, x_11, x_9);
lean_dec(x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
lean_object* x_15; 
lean_dec(x_12);
lean_free_object(x_3);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
x_20 = lean_array_size(x_16);
x_21 = 0;
x_22 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__4(x_1, x_2, x_16, x_17, x_18, x_16, x_20, x_21, x_19);
lean_dec(x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
x_32 = lean_array_size(x_28);
x_33 = 0;
x_34 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__5(x_1, x_28, x_29, x_30, x_28, x_32, x_33, x_31);
lean_dec(x_28);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_ctor_set(x_3, 0, x_36);
return x_3;
}
else
{
lean_object* x_37; 
lean_dec(x_34);
lean_free_object(x_3);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_3, 0);
lean_inc(x_38);
lean_dec(x_3);
x_39 = lean_box(0);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
x_42 = lean_array_size(x_38);
x_43 = 0;
x_44 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__5(x_1, x_38, x_39, x_40, x_38, x_42, x_43, x_41);
lean_dec(x_38);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; 
lean_dec(x_44);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_4);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_uget(x_5, x_7);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = l_Lean_Grind_Linarith_Poly_coeff(x_15, x_1);
lean_dec(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_18 = lean_int_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_10);
x_20 = lean_array_push(x_14, x_19);
lean_ctor_set(x_11, 1, x_20);
lean_inc(x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_11);
x_22 = 1;
x_23 = lean_usize_add(x_7, x_22);
x_7 = x_23;
x_8 = x_21;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_16);
x_25 = l_Lean_PersistentArray_push___rarg(x_13, x_10);
lean_ctor_set(x_11, 0, x_25);
lean_inc(x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_11);
x_27 = 1;
x_28 = lean_usize_add(x_7, x_27);
x_7 = x_28;
x_8 = x_26;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
x_33 = l_Lean_Grind_Linarith_Poly_coeff(x_32, x_1);
lean_dec(x_32);
x_34 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10;
x_35 = lean_int_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_10);
x_37 = lean_array_push(x_31, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_4);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_38);
x_40 = 1;
x_41 = lean_usize_add(x_7, x_40);
x_7 = x_41;
x_8 = x_39;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
lean_dec(x_33);
x_43 = l_Lean_PersistentArray_push___rarg(x_30, x_10);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_31);
lean_inc(x_4);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_44);
x_46 = 1;
x_47 = lean_usize_add(x_7, x_46);
x_7 = x_47;
x_8 = x_45;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__3(x_1, x_3, x_4, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
x_12 = lean_array_size(x_9);
x_13 = 0;
x_14 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__6(x_1, x_8, x_9, x_10, x_9, x_12, x_13, x_11);
lean_dec(x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__5;
x_4 = l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__2(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__5(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__6(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__1(x_1, x_2);
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_9, x_8);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_10);
x_23 = lean_array_uget(x_7, x_9);
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
lean_inc(x_34);
lean_inc(x_3);
x_35 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(x_1, x_2, x_3, x_33, x_34, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(x_34, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_37);
lean_dec(x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_6);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_6);
x_24 = x_40;
x_25 = x_39;
goto block_32;
}
else
{
uint8_t x_41; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_34);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_dec(x_35);
x_46 = !lean_is_exclusive(x_36);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_48 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_47, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_45);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_50 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
lean_inc(x_6);
lean_ctor_set(x_36, 0, x_6);
x_24 = x_36;
x_25 = x_53;
goto block_32;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_free_object(x_36);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___spec__1___closed__1;
x_24 = x_55;
x_25 = x_54;
goto block_32;
}
}
else
{
uint8_t x_56; 
lean_free_object(x_36);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_50);
if (x_56 == 0)
{
return x_50;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_50, 0);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_50);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_free_object(x_36);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_48);
if (x_60 == 0)
{
return x_48;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
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
x_64 = lean_ctor_get(x_36, 0);
lean_inc(x_64);
lean_dec(x_36);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_65 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_64, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_45);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_67 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_66);
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
lean_dec(x_67);
lean_inc(x_6);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_6);
x_24 = x_71;
x_25 = x_70;
goto block_32;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_dec(x_67);
x_73 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___spec__1___closed__1;
x_24 = x_73;
x_25 = x_72;
goto block_32;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
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
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
x_78 = lean_ctor_get(x_65, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_65, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_80 = x_65;
} else {
 lean_dec_ref(x_65);
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
else
{
uint8_t x_82; 
lean_dec(x_34);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_35);
if (x_82 == 0)
{
return x_35;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_35, 0);
x_84 = lean_ctor_get(x_35, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_35);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
block_32:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
else
{
lean_object* x_28; size_t x_29; size_t x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = 1;
x_30 = lean_usize_add(x_9, x_29);
x_9 = x_30;
x_10 = x_28;
x_20 = x_25;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_323 = lean_ctor_get(x_17, 31);
lean_inc(x_323);
lean_dec(x_17);
x_324 = lean_ctor_get(x_323, 2);
lean_inc(x_324);
x_325 = lean_nat_dec_lt(x_4, x_324);
lean_dec(x_324);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; 
lean_dec(x_323);
x_326 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1;
x_327 = l_outOfBounds___rarg(x_326);
x_19 = x_327;
goto block_322;
}
else
{
lean_object* x_328; lean_object* x_329; 
x_328 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1;
x_329 = l_Lean_PersistentArray_get_x21___rarg(x_328, x_323, x_4);
x_19 = x_329;
goto block_322;
}
block_322:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_20 = l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___spec__1(x_1, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_48 = lean_st_ref_take(x_7, x_18);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 14);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_49, 14);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_50, 3);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_51);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_51, 0);
x_59 = lean_array_get_size(x_58);
x_60 = lean_nat_dec_lt(x_6, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_21);
x_61 = lean_st_ref_set(x_7, x_49, x_52);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_23 = x_62;
goto block_47;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_array_fget(x_58, x_6);
x_64 = lean_box(0);
x_65 = lean_array_fset(x_58, x_6, x_64);
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_63, 31);
x_68 = l_Lean_PersistentArray_set___rarg(x_67, x_4, x_21);
lean_ctor_set(x_63, 31, x_68);
x_69 = lean_array_fset(x_65, x_6, x_63);
lean_ctor_set(x_51, 0, x_69);
x_70 = lean_st_ref_set(x_7, x_49, x_52);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_23 = x_71;
goto block_47;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_72 = lean_ctor_get(x_63, 0);
x_73 = lean_ctor_get(x_63, 1);
x_74 = lean_ctor_get(x_63, 2);
x_75 = lean_ctor_get(x_63, 3);
x_76 = lean_ctor_get(x_63, 4);
x_77 = lean_ctor_get(x_63, 5);
x_78 = lean_ctor_get(x_63, 6);
x_79 = lean_ctor_get(x_63, 7);
x_80 = lean_ctor_get(x_63, 8);
x_81 = lean_ctor_get(x_63, 9);
x_82 = lean_ctor_get(x_63, 10);
x_83 = lean_ctor_get(x_63, 11);
x_84 = lean_ctor_get(x_63, 12);
x_85 = lean_ctor_get(x_63, 13);
x_86 = lean_ctor_get(x_63, 14);
x_87 = lean_ctor_get(x_63, 15);
x_88 = lean_ctor_get(x_63, 16);
x_89 = lean_ctor_get(x_63, 17);
x_90 = lean_ctor_get(x_63, 18);
x_91 = lean_ctor_get(x_63, 19);
x_92 = lean_ctor_get(x_63, 20);
x_93 = lean_ctor_get(x_63, 21);
x_94 = lean_ctor_get(x_63, 22);
x_95 = lean_ctor_get(x_63, 23);
x_96 = lean_ctor_get(x_63, 24);
x_97 = lean_ctor_get(x_63, 25);
x_98 = lean_ctor_get(x_63, 26);
x_99 = lean_ctor_get(x_63, 27);
x_100 = lean_ctor_get(x_63, 28);
x_101 = lean_ctor_get(x_63, 29);
x_102 = lean_ctor_get(x_63, 30);
x_103 = lean_ctor_get(x_63, 31);
x_104 = lean_ctor_get(x_63, 32);
x_105 = lean_ctor_get_uint8(x_63, sizeof(void*)*39);
x_106 = lean_ctor_get(x_63, 33);
x_107 = lean_ctor_get(x_63, 34);
x_108 = lean_ctor_get(x_63, 35);
x_109 = lean_ctor_get(x_63, 36);
x_110 = lean_ctor_get(x_63, 37);
x_111 = lean_ctor_get(x_63, 38);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
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
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_63);
x_112 = l_Lean_PersistentArray_set___rarg(x_103, x_4, x_21);
x_113 = lean_alloc_ctor(0, 39, 1);
lean_ctor_set(x_113, 0, x_72);
lean_ctor_set(x_113, 1, x_73);
lean_ctor_set(x_113, 2, x_74);
lean_ctor_set(x_113, 3, x_75);
lean_ctor_set(x_113, 4, x_76);
lean_ctor_set(x_113, 5, x_77);
lean_ctor_set(x_113, 6, x_78);
lean_ctor_set(x_113, 7, x_79);
lean_ctor_set(x_113, 8, x_80);
lean_ctor_set(x_113, 9, x_81);
lean_ctor_set(x_113, 10, x_82);
lean_ctor_set(x_113, 11, x_83);
lean_ctor_set(x_113, 12, x_84);
lean_ctor_set(x_113, 13, x_85);
lean_ctor_set(x_113, 14, x_86);
lean_ctor_set(x_113, 15, x_87);
lean_ctor_set(x_113, 16, x_88);
lean_ctor_set(x_113, 17, x_89);
lean_ctor_set(x_113, 18, x_90);
lean_ctor_set(x_113, 19, x_91);
lean_ctor_set(x_113, 20, x_92);
lean_ctor_set(x_113, 21, x_93);
lean_ctor_set(x_113, 22, x_94);
lean_ctor_set(x_113, 23, x_95);
lean_ctor_set(x_113, 24, x_96);
lean_ctor_set(x_113, 25, x_97);
lean_ctor_set(x_113, 26, x_98);
lean_ctor_set(x_113, 27, x_99);
lean_ctor_set(x_113, 28, x_100);
lean_ctor_set(x_113, 29, x_101);
lean_ctor_set(x_113, 30, x_102);
lean_ctor_set(x_113, 31, x_112);
lean_ctor_set(x_113, 32, x_104);
lean_ctor_set(x_113, 33, x_106);
lean_ctor_set(x_113, 34, x_107);
lean_ctor_set(x_113, 35, x_108);
lean_ctor_set(x_113, 36, x_109);
lean_ctor_set(x_113, 37, x_110);
lean_ctor_set(x_113, 38, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*39, x_105);
x_114 = lean_array_fset(x_65, x_6, x_113);
lean_ctor_set(x_51, 0, x_114);
x_115 = lean_st_ref_set(x_7, x_49, x_52);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_23 = x_116;
goto block_47;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_117 = lean_ctor_get(x_51, 0);
x_118 = lean_ctor_get(x_51, 1);
x_119 = lean_ctor_get(x_51, 2);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_51);
x_120 = lean_array_get_size(x_117);
x_121 = lean_nat_dec_lt(x_6, x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_21);
x_122 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set(x_122, 1, x_118);
lean_ctor_set(x_122, 2, x_119);
lean_ctor_set(x_50, 3, x_122);
x_123 = lean_st_ref_set(x_7, x_49, x_52);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_23 = x_124;
goto block_47;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_125 = lean_array_fget(x_117, x_6);
x_126 = lean_box(0);
x_127 = lean_array_fset(x_117, x_6, x_126);
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_125, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_125, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_125, 4);
lean_inc(x_132);
x_133 = lean_ctor_get(x_125, 5);
lean_inc(x_133);
x_134 = lean_ctor_get(x_125, 6);
lean_inc(x_134);
x_135 = lean_ctor_get(x_125, 7);
lean_inc(x_135);
x_136 = lean_ctor_get(x_125, 8);
lean_inc(x_136);
x_137 = lean_ctor_get(x_125, 9);
lean_inc(x_137);
x_138 = lean_ctor_get(x_125, 10);
lean_inc(x_138);
x_139 = lean_ctor_get(x_125, 11);
lean_inc(x_139);
x_140 = lean_ctor_get(x_125, 12);
lean_inc(x_140);
x_141 = lean_ctor_get(x_125, 13);
lean_inc(x_141);
x_142 = lean_ctor_get(x_125, 14);
lean_inc(x_142);
x_143 = lean_ctor_get(x_125, 15);
lean_inc(x_143);
x_144 = lean_ctor_get(x_125, 16);
lean_inc(x_144);
x_145 = lean_ctor_get(x_125, 17);
lean_inc(x_145);
x_146 = lean_ctor_get(x_125, 18);
lean_inc(x_146);
x_147 = lean_ctor_get(x_125, 19);
lean_inc(x_147);
x_148 = lean_ctor_get(x_125, 20);
lean_inc(x_148);
x_149 = lean_ctor_get(x_125, 21);
lean_inc(x_149);
x_150 = lean_ctor_get(x_125, 22);
lean_inc(x_150);
x_151 = lean_ctor_get(x_125, 23);
lean_inc(x_151);
x_152 = lean_ctor_get(x_125, 24);
lean_inc(x_152);
x_153 = lean_ctor_get(x_125, 25);
lean_inc(x_153);
x_154 = lean_ctor_get(x_125, 26);
lean_inc(x_154);
x_155 = lean_ctor_get(x_125, 27);
lean_inc(x_155);
x_156 = lean_ctor_get(x_125, 28);
lean_inc(x_156);
x_157 = lean_ctor_get(x_125, 29);
lean_inc(x_157);
x_158 = lean_ctor_get(x_125, 30);
lean_inc(x_158);
x_159 = lean_ctor_get(x_125, 31);
lean_inc(x_159);
x_160 = lean_ctor_get(x_125, 32);
lean_inc(x_160);
x_161 = lean_ctor_get_uint8(x_125, sizeof(void*)*39);
x_162 = lean_ctor_get(x_125, 33);
lean_inc(x_162);
x_163 = lean_ctor_get(x_125, 34);
lean_inc(x_163);
x_164 = lean_ctor_get(x_125, 35);
lean_inc(x_164);
x_165 = lean_ctor_get(x_125, 36);
lean_inc(x_165);
x_166 = lean_ctor_get(x_125, 37);
lean_inc(x_166);
x_167 = lean_ctor_get(x_125, 38);
lean_inc(x_167);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 lean_ctor_release(x_125, 4);
 lean_ctor_release(x_125, 5);
 lean_ctor_release(x_125, 6);
 lean_ctor_release(x_125, 7);
 lean_ctor_release(x_125, 8);
 lean_ctor_release(x_125, 9);
 lean_ctor_release(x_125, 10);
 lean_ctor_release(x_125, 11);
 lean_ctor_release(x_125, 12);
 lean_ctor_release(x_125, 13);
 lean_ctor_release(x_125, 14);
 lean_ctor_release(x_125, 15);
 lean_ctor_release(x_125, 16);
 lean_ctor_release(x_125, 17);
 lean_ctor_release(x_125, 18);
 lean_ctor_release(x_125, 19);
 lean_ctor_release(x_125, 20);
 lean_ctor_release(x_125, 21);
 lean_ctor_release(x_125, 22);
 lean_ctor_release(x_125, 23);
 lean_ctor_release(x_125, 24);
 lean_ctor_release(x_125, 25);
 lean_ctor_release(x_125, 26);
 lean_ctor_release(x_125, 27);
 lean_ctor_release(x_125, 28);
 lean_ctor_release(x_125, 29);
 lean_ctor_release(x_125, 30);
 lean_ctor_release(x_125, 31);
 lean_ctor_release(x_125, 32);
 lean_ctor_release(x_125, 33);
 lean_ctor_release(x_125, 34);
 lean_ctor_release(x_125, 35);
 lean_ctor_release(x_125, 36);
 lean_ctor_release(x_125, 37);
 lean_ctor_release(x_125, 38);
 x_168 = x_125;
} else {
 lean_dec_ref(x_125);
 x_168 = lean_box(0);
}
x_169 = l_Lean_PersistentArray_set___rarg(x_159, x_4, x_21);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 39, 1);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_128);
lean_ctor_set(x_170, 1, x_129);
lean_ctor_set(x_170, 2, x_130);
lean_ctor_set(x_170, 3, x_131);
lean_ctor_set(x_170, 4, x_132);
lean_ctor_set(x_170, 5, x_133);
lean_ctor_set(x_170, 6, x_134);
lean_ctor_set(x_170, 7, x_135);
lean_ctor_set(x_170, 8, x_136);
lean_ctor_set(x_170, 9, x_137);
lean_ctor_set(x_170, 10, x_138);
lean_ctor_set(x_170, 11, x_139);
lean_ctor_set(x_170, 12, x_140);
lean_ctor_set(x_170, 13, x_141);
lean_ctor_set(x_170, 14, x_142);
lean_ctor_set(x_170, 15, x_143);
lean_ctor_set(x_170, 16, x_144);
lean_ctor_set(x_170, 17, x_145);
lean_ctor_set(x_170, 18, x_146);
lean_ctor_set(x_170, 19, x_147);
lean_ctor_set(x_170, 20, x_148);
lean_ctor_set(x_170, 21, x_149);
lean_ctor_set(x_170, 22, x_150);
lean_ctor_set(x_170, 23, x_151);
lean_ctor_set(x_170, 24, x_152);
lean_ctor_set(x_170, 25, x_153);
lean_ctor_set(x_170, 26, x_154);
lean_ctor_set(x_170, 27, x_155);
lean_ctor_set(x_170, 28, x_156);
lean_ctor_set(x_170, 29, x_157);
lean_ctor_set(x_170, 30, x_158);
lean_ctor_set(x_170, 31, x_169);
lean_ctor_set(x_170, 32, x_160);
lean_ctor_set(x_170, 33, x_162);
lean_ctor_set(x_170, 34, x_163);
lean_ctor_set(x_170, 35, x_164);
lean_ctor_set(x_170, 36, x_165);
lean_ctor_set(x_170, 37, x_166);
lean_ctor_set(x_170, 38, x_167);
lean_ctor_set_uint8(x_170, sizeof(void*)*39, x_161);
x_171 = lean_array_fset(x_127, x_6, x_170);
x_172 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_118);
lean_ctor_set(x_172, 2, x_119);
lean_ctor_set(x_50, 3, x_172);
x_173 = lean_st_ref_set(x_7, x_49, x_52);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_23 = x_174;
goto block_47;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_175 = lean_ctor_get(x_50, 0);
x_176 = lean_ctor_get(x_50, 1);
x_177 = lean_ctor_get(x_50, 2);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_50);
x_178 = lean_ctor_get(x_51, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_51, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_51, 2);
lean_inc(x_180);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 x_181 = x_51;
} else {
 lean_dec_ref(x_51);
 x_181 = lean_box(0);
}
x_182 = lean_array_get_size(x_178);
x_183 = lean_nat_dec_lt(x_6, x_182);
lean_dec(x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_21);
if (lean_is_scalar(x_181)) {
 x_184 = lean_alloc_ctor(0, 3, 0);
} else {
 x_184 = x_181;
}
lean_ctor_set(x_184, 0, x_178);
lean_ctor_set(x_184, 1, x_179);
lean_ctor_set(x_184, 2, x_180);
x_185 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_185, 0, x_175);
lean_ctor_set(x_185, 1, x_176);
lean_ctor_set(x_185, 2, x_177);
lean_ctor_set(x_185, 3, x_184);
lean_ctor_set(x_49, 14, x_185);
x_186 = lean_st_ref_set(x_7, x_49, x_52);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_23 = x_187;
goto block_47;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_188 = lean_array_fget(x_178, x_6);
x_189 = lean_box(0);
x_190 = lean_array_fset(x_178, x_6, x_189);
x_191 = lean_ctor_get(x_188, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 4);
lean_inc(x_195);
x_196 = lean_ctor_get(x_188, 5);
lean_inc(x_196);
x_197 = lean_ctor_get(x_188, 6);
lean_inc(x_197);
x_198 = lean_ctor_get(x_188, 7);
lean_inc(x_198);
x_199 = lean_ctor_get(x_188, 8);
lean_inc(x_199);
x_200 = lean_ctor_get(x_188, 9);
lean_inc(x_200);
x_201 = lean_ctor_get(x_188, 10);
lean_inc(x_201);
x_202 = lean_ctor_get(x_188, 11);
lean_inc(x_202);
x_203 = lean_ctor_get(x_188, 12);
lean_inc(x_203);
x_204 = lean_ctor_get(x_188, 13);
lean_inc(x_204);
x_205 = lean_ctor_get(x_188, 14);
lean_inc(x_205);
x_206 = lean_ctor_get(x_188, 15);
lean_inc(x_206);
x_207 = lean_ctor_get(x_188, 16);
lean_inc(x_207);
x_208 = lean_ctor_get(x_188, 17);
lean_inc(x_208);
x_209 = lean_ctor_get(x_188, 18);
lean_inc(x_209);
x_210 = lean_ctor_get(x_188, 19);
lean_inc(x_210);
x_211 = lean_ctor_get(x_188, 20);
lean_inc(x_211);
x_212 = lean_ctor_get(x_188, 21);
lean_inc(x_212);
x_213 = lean_ctor_get(x_188, 22);
lean_inc(x_213);
x_214 = lean_ctor_get(x_188, 23);
lean_inc(x_214);
x_215 = lean_ctor_get(x_188, 24);
lean_inc(x_215);
x_216 = lean_ctor_get(x_188, 25);
lean_inc(x_216);
x_217 = lean_ctor_get(x_188, 26);
lean_inc(x_217);
x_218 = lean_ctor_get(x_188, 27);
lean_inc(x_218);
x_219 = lean_ctor_get(x_188, 28);
lean_inc(x_219);
x_220 = lean_ctor_get(x_188, 29);
lean_inc(x_220);
x_221 = lean_ctor_get(x_188, 30);
lean_inc(x_221);
x_222 = lean_ctor_get(x_188, 31);
lean_inc(x_222);
x_223 = lean_ctor_get(x_188, 32);
lean_inc(x_223);
x_224 = lean_ctor_get_uint8(x_188, sizeof(void*)*39);
x_225 = lean_ctor_get(x_188, 33);
lean_inc(x_225);
x_226 = lean_ctor_get(x_188, 34);
lean_inc(x_226);
x_227 = lean_ctor_get(x_188, 35);
lean_inc(x_227);
x_228 = lean_ctor_get(x_188, 36);
lean_inc(x_228);
x_229 = lean_ctor_get(x_188, 37);
lean_inc(x_229);
x_230 = lean_ctor_get(x_188, 38);
lean_inc(x_230);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 lean_ctor_release(x_188, 6);
 lean_ctor_release(x_188, 7);
 lean_ctor_release(x_188, 8);
 lean_ctor_release(x_188, 9);
 lean_ctor_release(x_188, 10);
 lean_ctor_release(x_188, 11);
 lean_ctor_release(x_188, 12);
 lean_ctor_release(x_188, 13);
 lean_ctor_release(x_188, 14);
 lean_ctor_release(x_188, 15);
 lean_ctor_release(x_188, 16);
 lean_ctor_release(x_188, 17);
 lean_ctor_release(x_188, 18);
 lean_ctor_release(x_188, 19);
 lean_ctor_release(x_188, 20);
 lean_ctor_release(x_188, 21);
 lean_ctor_release(x_188, 22);
 lean_ctor_release(x_188, 23);
 lean_ctor_release(x_188, 24);
 lean_ctor_release(x_188, 25);
 lean_ctor_release(x_188, 26);
 lean_ctor_release(x_188, 27);
 lean_ctor_release(x_188, 28);
 lean_ctor_release(x_188, 29);
 lean_ctor_release(x_188, 30);
 lean_ctor_release(x_188, 31);
 lean_ctor_release(x_188, 32);
 lean_ctor_release(x_188, 33);
 lean_ctor_release(x_188, 34);
 lean_ctor_release(x_188, 35);
 lean_ctor_release(x_188, 36);
 lean_ctor_release(x_188, 37);
 lean_ctor_release(x_188, 38);
 x_231 = x_188;
} else {
 lean_dec_ref(x_188);
 x_231 = lean_box(0);
}
x_232 = l_Lean_PersistentArray_set___rarg(x_222, x_4, x_21);
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(0, 39, 1);
} else {
 x_233 = x_231;
}
lean_ctor_set(x_233, 0, x_191);
lean_ctor_set(x_233, 1, x_192);
lean_ctor_set(x_233, 2, x_193);
lean_ctor_set(x_233, 3, x_194);
lean_ctor_set(x_233, 4, x_195);
lean_ctor_set(x_233, 5, x_196);
lean_ctor_set(x_233, 6, x_197);
lean_ctor_set(x_233, 7, x_198);
lean_ctor_set(x_233, 8, x_199);
lean_ctor_set(x_233, 9, x_200);
lean_ctor_set(x_233, 10, x_201);
lean_ctor_set(x_233, 11, x_202);
lean_ctor_set(x_233, 12, x_203);
lean_ctor_set(x_233, 13, x_204);
lean_ctor_set(x_233, 14, x_205);
lean_ctor_set(x_233, 15, x_206);
lean_ctor_set(x_233, 16, x_207);
lean_ctor_set(x_233, 17, x_208);
lean_ctor_set(x_233, 18, x_209);
lean_ctor_set(x_233, 19, x_210);
lean_ctor_set(x_233, 20, x_211);
lean_ctor_set(x_233, 21, x_212);
lean_ctor_set(x_233, 22, x_213);
lean_ctor_set(x_233, 23, x_214);
lean_ctor_set(x_233, 24, x_215);
lean_ctor_set(x_233, 25, x_216);
lean_ctor_set(x_233, 26, x_217);
lean_ctor_set(x_233, 27, x_218);
lean_ctor_set(x_233, 28, x_219);
lean_ctor_set(x_233, 29, x_220);
lean_ctor_set(x_233, 30, x_221);
lean_ctor_set(x_233, 31, x_232);
lean_ctor_set(x_233, 32, x_223);
lean_ctor_set(x_233, 33, x_225);
lean_ctor_set(x_233, 34, x_226);
lean_ctor_set(x_233, 35, x_227);
lean_ctor_set(x_233, 36, x_228);
lean_ctor_set(x_233, 37, x_229);
lean_ctor_set(x_233, 38, x_230);
lean_ctor_set_uint8(x_233, sizeof(void*)*39, x_224);
x_234 = lean_array_fset(x_190, x_6, x_233);
if (lean_is_scalar(x_181)) {
 x_235 = lean_alloc_ctor(0, 3, 0);
} else {
 x_235 = x_181;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_179);
lean_ctor_set(x_235, 2, x_180);
x_236 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_236, 0, x_175);
lean_ctor_set(x_236, 1, x_176);
lean_ctor_set(x_236, 2, x_177);
lean_ctor_set(x_236, 3, x_235);
lean_ctor_set(x_49, 14, x_236);
x_237 = lean_st_ref_set(x_7, x_49, x_52);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
x_23 = x_238;
goto block_47;
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_239 = lean_ctor_get(x_49, 0);
x_240 = lean_ctor_get(x_49, 1);
x_241 = lean_ctor_get(x_49, 2);
x_242 = lean_ctor_get(x_49, 3);
x_243 = lean_ctor_get(x_49, 4);
x_244 = lean_ctor_get(x_49, 5);
x_245 = lean_ctor_get(x_49, 6);
x_246 = lean_ctor_get(x_49, 7);
x_247 = lean_ctor_get_uint8(x_49, sizeof(void*)*16);
x_248 = lean_ctor_get(x_49, 8);
x_249 = lean_ctor_get(x_49, 9);
x_250 = lean_ctor_get(x_49, 10);
x_251 = lean_ctor_get(x_49, 11);
x_252 = lean_ctor_get(x_49, 12);
x_253 = lean_ctor_get(x_49, 13);
x_254 = lean_ctor_get(x_49, 15);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_49);
x_255 = lean_ctor_get(x_50, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_50, 1);
lean_inc(x_256);
x_257 = lean_ctor_get(x_50, 2);
lean_inc(x_257);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 lean_ctor_release(x_50, 3);
 x_258 = x_50;
} else {
 lean_dec_ref(x_50);
 x_258 = lean_box(0);
}
x_259 = lean_ctor_get(x_51, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_51, 1);
lean_inc(x_260);
x_261 = lean_ctor_get(x_51, 2);
lean_inc(x_261);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 x_262 = x_51;
} else {
 lean_dec_ref(x_51);
 x_262 = lean_box(0);
}
x_263 = lean_array_get_size(x_259);
x_264 = lean_nat_dec_lt(x_6, x_263);
lean_dec(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_21);
if (lean_is_scalar(x_262)) {
 x_265 = lean_alloc_ctor(0, 3, 0);
} else {
 x_265 = x_262;
}
lean_ctor_set(x_265, 0, x_259);
lean_ctor_set(x_265, 1, x_260);
lean_ctor_set(x_265, 2, x_261);
if (lean_is_scalar(x_258)) {
 x_266 = lean_alloc_ctor(0, 4, 0);
} else {
 x_266 = x_258;
}
lean_ctor_set(x_266, 0, x_255);
lean_ctor_set(x_266, 1, x_256);
lean_ctor_set(x_266, 2, x_257);
lean_ctor_set(x_266, 3, x_265);
x_267 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_267, 0, x_239);
lean_ctor_set(x_267, 1, x_240);
lean_ctor_set(x_267, 2, x_241);
lean_ctor_set(x_267, 3, x_242);
lean_ctor_set(x_267, 4, x_243);
lean_ctor_set(x_267, 5, x_244);
lean_ctor_set(x_267, 6, x_245);
lean_ctor_set(x_267, 7, x_246);
lean_ctor_set(x_267, 8, x_248);
lean_ctor_set(x_267, 9, x_249);
lean_ctor_set(x_267, 10, x_250);
lean_ctor_set(x_267, 11, x_251);
lean_ctor_set(x_267, 12, x_252);
lean_ctor_set(x_267, 13, x_253);
lean_ctor_set(x_267, 14, x_266);
lean_ctor_set(x_267, 15, x_254);
lean_ctor_set_uint8(x_267, sizeof(void*)*16, x_247);
x_268 = lean_st_ref_set(x_7, x_267, x_52);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
x_23 = x_269;
goto block_47;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_270 = lean_array_fget(x_259, x_6);
x_271 = lean_box(0);
x_272 = lean_array_fset(x_259, x_6, x_271);
x_273 = lean_ctor_get(x_270, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_270, 1);
lean_inc(x_274);
x_275 = lean_ctor_get(x_270, 2);
lean_inc(x_275);
x_276 = lean_ctor_get(x_270, 3);
lean_inc(x_276);
x_277 = lean_ctor_get(x_270, 4);
lean_inc(x_277);
x_278 = lean_ctor_get(x_270, 5);
lean_inc(x_278);
x_279 = lean_ctor_get(x_270, 6);
lean_inc(x_279);
x_280 = lean_ctor_get(x_270, 7);
lean_inc(x_280);
x_281 = lean_ctor_get(x_270, 8);
lean_inc(x_281);
x_282 = lean_ctor_get(x_270, 9);
lean_inc(x_282);
x_283 = lean_ctor_get(x_270, 10);
lean_inc(x_283);
x_284 = lean_ctor_get(x_270, 11);
lean_inc(x_284);
x_285 = lean_ctor_get(x_270, 12);
lean_inc(x_285);
x_286 = lean_ctor_get(x_270, 13);
lean_inc(x_286);
x_287 = lean_ctor_get(x_270, 14);
lean_inc(x_287);
x_288 = lean_ctor_get(x_270, 15);
lean_inc(x_288);
x_289 = lean_ctor_get(x_270, 16);
lean_inc(x_289);
x_290 = lean_ctor_get(x_270, 17);
lean_inc(x_290);
x_291 = lean_ctor_get(x_270, 18);
lean_inc(x_291);
x_292 = lean_ctor_get(x_270, 19);
lean_inc(x_292);
x_293 = lean_ctor_get(x_270, 20);
lean_inc(x_293);
x_294 = lean_ctor_get(x_270, 21);
lean_inc(x_294);
x_295 = lean_ctor_get(x_270, 22);
lean_inc(x_295);
x_296 = lean_ctor_get(x_270, 23);
lean_inc(x_296);
x_297 = lean_ctor_get(x_270, 24);
lean_inc(x_297);
x_298 = lean_ctor_get(x_270, 25);
lean_inc(x_298);
x_299 = lean_ctor_get(x_270, 26);
lean_inc(x_299);
x_300 = lean_ctor_get(x_270, 27);
lean_inc(x_300);
x_301 = lean_ctor_get(x_270, 28);
lean_inc(x_301);
x_302 = lean_ctor_get(x_270, 29);
lean_inc(x_302);
x_303 = lean_ctor_get(x_270, 30);
lean_inc(x_303);
x_304 = lean_ctor_get(x_270, 31);
lean_inc(x_304);
x_305 = lean_ctor_get(x_270, 32);
lean_inc(x_305);
x_306 = lean_ctor_get_uint8(x_270, sizeof(void*)*39);
x_307 = lean_ctor_get(x_270, 33);
lean_inc(x_307);
x_308 = lean_ctor_get(x_270, 34);
lean_inc(x_308);
x_309 = lean_ctor_get(x_270, 35);
lean_inc(x_309);
x_310 = lean_ctor_get(x_270, 36);
lean_inc(x_310);
x_311 = lean_ctor_get(x_270, 37);
lean_inc(x_311);
x_312 = lean_ctor_get(x_270, 38);
lean_inc(x_312);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 lean_ctor_release(x_270, 2);
 lean_ctor_release(x_270, 3);
 lean_ctor_release(x_270, 4);
 lean_ctor_release(x_270, 5);
 lean_ctor_release(x_270, 6);
 lean_ctor_release(x_270, 7);
 lean_ctor_release(x_270, 8);
 lean_ctor_release(x_270, 9);
 lean_ctor_release(x_270, 10);
 lean_ctor_release(x_270, 11);
 lean_ctor_release(x_270, 12);
 lean_ctor_release(x_270, 13);
 lean_ctor_release(x_270, 14);
 lean_ctor_release(x_270, 15);
 lean_ctor_release(x_270, 16);
 lean_ctor_release(x_270, 17);
 lean_ctor_release(x_270, 18);
 lean_ctor_release(x_270, 19);
 lean_ctor_release(x_270, 20);
 lean_ctor_release(x_270, 21);
 lean_ctor_release(x_270, 22);
 lean_ctor_release(x_270, 23);
 lean_ctor_release(x_270, 24);
 lean_ctor_release(x_270, 25);
 lean_ctor_release(x_270, 26);
 lean_ctor_release(x_270, 27);
 lean_ctor_release(x_270, 28);
 lean_ctor_release(x_270, 29);
 lean_ctor_release(x_270, 30);
 lean_ctor_release(x_270, 31);
 lean_ctor_release(x_270, 32);
 lean_ctor_release(x_270, 33);
 lean_ctor_release(x_270, 34);
 lean_ctor_release(x_270, 35);
 lean_ctor_release(x_270, 36);
 lean_ctor_release(x_270, 37);
 lean_ctor_release(x_270, 38);
 x_313 = x_270;
} else {
 lean_dec_ref(x_270);
 x_313 = lean_box(0);
}
x_314 = l_Lean_PersistentArray_set___rarg(x_304, x_4, x_21);
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(0, 39, 1);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_273);
lean_ctor_set(x_315, 1, x_274);
lean_ctor_set(x_315, 2, x_275);
lean_ctor_set(x_315, 3, x_276);
lean_ctor_set(x_315, 4, x_277);
lean_ctor_set(x_315, 5, x_278);
lean_ctor_set(x_315, 6, x_279);
lean_ctor_set(x_315, 7, x_280);
lean_ctor_set(x_315, 8, x_281);
lean_ctor_set(x_315, 9, x_282);
lean_ctor_set(x_315, 10, x_283);
lean_ctor_set(x_315, 11, x_284);
lean_ctor_set(x_315, 12, x_285);
lean_ctor_set(x_315, 13, x_286);
lean_ctor_set(x_315, 14, x_287);
lean_ctor_set(x_315, 15, x_288);
lean_ctor_set(x_315, 16, x_289);
lean_ctor_set(x_315, 17, x_290);
lean_ctor_set(x_315, 18, x_291);
lean_ctor_set(x_315, 19, x_292);
lean_ctor_set(x_315, 20, x_293);
lean_ctor_set(x_315, 21, x_294);
lean_ctor_set(x_315, 22, x_295);
lean_ctor_set(x_315, 23, x_296);
lean_ctor_set(x_315, 24, x_297);
lean_ctor_set(x_315, 25, x_298);
lean_ctor_set(x_315, 26, x_299);
lean_ctor_set(x_315, 27, x_300);
lean_ctor_set(x_315, 28, x_301);
lean_ctor_set(x_315, 29, x_302);
lean_ctor_set(x_315, 30, x_303);
lean_ctor_set(x_315, 31, x_314);
lean_ctor_set(x_315, 32, x_305);
lean_ctor_set(x_315, 33, x_307);
lean_ctor_set(x_315, 34, x_308);
lean_ctor_set(x_315, 35, x_309);
lean_ctor_set(x_315, 36, x_310);
lean_ctor_set(x_315, 37, x_311);
lean_ctor_set(x_315, 38, x_312);
lean_ctor_set_uint8(x_315, sizeof(void*)*39, x_306);
x_316 = lean_array_fset(x_272, x_6, x_315);
if (lean_is_scalar(x_262)) {
 x_317 = lean_alloc_ctor(0, 3, 0);
} else {
 x_317 = x_262;
}
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_260);
lean_ctor_set(x_317, 2, x_261);
if (lean_is_scalar(x_258)) {
 x_318 = lean_alloc_ctor(0, 4, 0);
} else {
 x_318 = x_258;
}
lean_ctor_set(x_318, 0, x_255);
lean_ctor_set(x_318, 1, x_256);
lean_ctor_set(x_318, 2, x_257);
lean_ctor_set(x_318, 3, x_317);
x_319 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_319, 0, x_239);
lean_ctor_set(x_319, 1, x_240);
lean_ctor_set(x_319, 2, x_241);
lean_ctor_set(x_319, 3, x_242);
lean_ctor_set(x_319, 4, x_243);
lean_ctor_set(x_319, 5, x_244);
lean_ctor_set(x_319, 6, x_245);
lean_ctor_set(x_319, 7, x_246);
lean_ctor_set(x_319, 8, x_248);
lean_ctor_set(x_319, 9, x_249);
lean_ctor_set(x_319, 10, x_250);
lean_ctor_set(x_319, 11, x_251);
lean_ctor_set(x_319, 12, x_252);
lean_ctor_set(x_319, 13, x_253);
lean_ctor_set(x_319, 14, x_318);
lean_ctor_set(x_319, 15, x_254);
lean_ctor_set_uint8(x_319, sizeof(void*)*16, x_247);
x_320 = lean_st_ref_set(x_7, x_319, x_52);
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec(x_320);
x_23 = x_321;
goto block_47;
}
}
block_47:
{
lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_box(0);
x_25 = lean_array_size(x_22);
x_26 = 0;
x_27 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__1;
x_28 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___spec__1(x_2, x_1, x_3, x_22, x_24, x_27, x_22, x_25, x_26, x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
lean_dec(x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
lean_dec(x_30);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
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
}
}
else
{
uint8_t x_330; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_330 = !lean_is_exclusive(x_16);
if (x_330 == 0)
{
return x_16;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_16, 0);
x_332 = lean_ctor_get(x_16, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_16);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
return x_333;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lambda__1(x_2, x_1, x_3, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
return x_20;
}
else
{
uint8_t x_21; 
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
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_15, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_box(0);
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
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___spec__1___boxed(lean_object** _args) {
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
x_21 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_22 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_23 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_21, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
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
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_nat_to_int(x_1);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
lean_dec(x_2);
lean_dec(x_19);
return x_20;
}
else
{
uint8_t x_21; 
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
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
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
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
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
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
x_20 = lean_ctor_get(x_4, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Lean_RBNode_forIn_visit___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___spec__1(x_1, x_2, x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(x_1, x_2, x_3, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_4 = x_20;
x_5 = x_30;
x_15 = x_29;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 37);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_lt(x_2, x_18);
lean_dec(x_18);
x_20 = lean_st_ref_take(x_5, x_16);
if (x_19 == 0)
{
lean_object* x_319; lean_object* x_320; 
lean_dec(x_17);
x_319 = l_Lean_IR_instInhabitedIndexSet;
x_320 = l_outOfBounds___rarg(x_319);
x_21 = x_320;
goto block_318;
}
else
{
lean_object* x_321; lean_object* x_322; 
x_321 = l_Lean_IR_instInhabitedIndexSet;
x_322 = l_Lean_PersistentArray_get_x21___rarg(x_321, x_17, x_2);
x_21 = x_322;
goto block_318;
}
block_318:
{
lean_object* x_22; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 14);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_dec(x_20);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_40, 14);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_41, 3);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_42);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_42, 0);
x_50 = lean_array_get_size(x_49);
x_51 = lean_nat_dec_lt(x_4, x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_st_ref_set(x_5, x_40, x_43);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_22 = x_53;
goto block_39;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_array_fget(x_49, x_4);
x_55 = lean_box(0);
x_56 = lean_array_fset(x_49, x_4, x_55);
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_54, 37);
x_59 = lean_box(0);
x_60 = l_Lean_PersistentArray_set___rarg(x_58, x_2, x_59);
lean_ctor_set(x_54, 37, x_60);
x_61 = lean_array_fset(x_56, x_4, x_54);
lean_ctor_set(x_42, 0, x_61);
x_62 = lean_st_ref_set(x_5, x_40, x_43);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_22 = x_63;
goto block_39;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_64 = lean_ctor_get(x_54, 0);
x_65 = lean_ctor_get(x_54, 1);
x_66 = lean_ctor_get(x_54, 2);
x_67 = lean_ctor_get(x_54, 3);
x_68 = lean_ctor_get(x_54, 4);
x_69 = lean_ctor_get(x_54, 5);
x_70 = lean_ctor_get(x_54, 6);
x_71 = lean_ctor_get(x_54, 7);
x_72 = lean_ctor_get(x_54, 8);
x_73 = lean_ctor_get(x_54, 9);
x_74 = lean_ctor_get(x_54, 10);
x_75 = lean_ctor_get(x_54, 11);
x_76 = lean_ctor_get(x_54, 12);
x_77 = lean_ctor_get(x_54, 13);
x_78 = lean_ctor_get(x_54, 14);
x_79 = lean_ctor_get(x_54, 15);
x_80 = lean_ctor_get(x_54, 16);
x_81 = lean_ctor_get(x_54, 17);
x_82 = lean_ctor_get(x_54, 18);
x_83 = lean_ctor_get(x_54, 19);
x_84 = lean_ctor_get(x_54, 20);
x_85 = lean_ctor_get(x_54, 21);
x_86 = lean_ctor_get(x_54, 22);
x_87 = lean_ctor_get(x_54, 23);
x_88 = lean_ctor_get(x_54, 24);
x_89 = lean_ctor_get(x_54, 25);
x_90 = lean_ctor_get(x_54, 26);
x_91 = lean_ctor_get(x_54, 27);
x_92 = lean_ctor_get(x_54, 28);
x_93 = lean_ctor_get(x_54, 29);
x_94 = lean_ctor_get(x_54, 30);
x_95 = lean_ctor_get(x_54, 31);
x_96 = lean_ctor_get(x_54, 32);
x_97 = lean_ctor_get_uint8(x_54, sizeof(void*)*39);
x_98 = lean_ctor_get(x_54, 33);
x_99 = lean_ctor_get(x_54, 34);
x_100 = lean_ctor_get(x_54, 35);
x_101 = lean_ctor_get(x_54, 36);
x_102 = lean_ctor_get(x_54, 37);
x_103 = lean_ctor_get(x_54, 38);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
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
lean_inc(x_80);
lean_inc(x_79);
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
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_54);
x_104 = lean_box(0);
x_105 = l_Lean_PersistentArray_set___rarg(x_102, x_2, x_104);
x_106 = lean_alloc_ctor(0, 39, 1);
lean_ctor_set(x_106, 0, x_64);
lean_ctor_set(x_106, 1, x_65);
lean_ctor_set(x_106, 2, x_66);
lean_ctor_set(x_106, 3, x_67);
lean_ctor_set(x_106, 4, x_68);
lean_ctor_set(x_106, 5, x_69);
lean_ctor_set(x_106, 6, x_70);
lean_ctor_set(x_106, 7, x_71);
lean_ctor_set(x_106, 8, x_72);
lean_ctor_set(x_106, 9, x_73);
lean_ctor_set(x_106, 10, x_74);
lean_ctor_set(x_106, 11, x_75);
lean_ctor_set(x_106, 12, x_76);
lean_ctor_set(x_106, 13, x_77);
lean_ctor_set(x_106, 14, x_78);
lean_ctor_set(x_106, 15, x_79);
lean_ctor_set(x_106, 16, x_80);
lean_ctor_set(x_106, 17, x_81);
lean_ctor_set(x_106, 18, x_82);
lean_ctor_set(x_106, 19, x_83);
lean_ctor_set(x_106, 20, x_84);
lean_ctor_set(x_106, 21, x_85);
lean_ctor_set(x_106, 22, x_86);
lean_ctor_set(x_106, 23, x_87);
lean_ctor_set(x_106, 24, x_88);
lean_ctor_set(x_106, 25, x_89);
lean_ctor_set(x_106, 26, x_90);
lean_ctor_set(x_106, 27, x_91);
lean_ctor_set(x_106, 28, x_92);
lean_ctor_set(x_106, 29, x_93);
lean_ctor_set(x_106, 30, x_94);
lean_ctor_set(x_106, 31, x_95);
lean_ctor_set(x_106, 32, x_96);
lean_ctor_set(x_106, 33, x_98);
lean_ctor_set(x_106, 34, x_99);
lean_ctor_set(x_106, 35, x_100);
lean_ctor_set(x_106, 36, x_101);
lean_ctor_set(x_106, 37, x_105);
lean_ctor_set(x_106, 38, x_103);
lean_ctor_set_uint8(x_106, sizeof(void*)*39, x_97);
x_107 = lean_array_fset(x_56, x_4, x_106);
lean_ctor_set(x_42, 0, x_107);
x_108 = lean_st_ref_set(x_5, x_40, x_43);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_22 = x_109;
goto block_39;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_110 = lean_ctor_get(x_42, 0);
x_111 = lean_ctor_get(x_42, 1);
x_112 = lean_ctor_get(x_42, 2);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_42);
x_113 = lean_array_get_size(x_110);
x_114 = lean_nat_dec_lt(x_4, x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_115, 2, x_112);
lean_ctor_set(x_41, 3, x_115);
x_116 = lean_st_ref_set(x_5, x_40, x_43);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_22 = x_117;
goto block_39;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_118 = lean_array_fget(x_110, x_4);
x_119 = lean_box(0);
x_120 = lean_array_fset(x_110, x_4, x_119);
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_118, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_118, 3);
lean_inc(x_124);
x_125 = lean_ctor_get(x_118, 4);
lean_inc(x_125);
x_126 = lean_ctor_get(x_118, 5);
lean_inc(x_126);
x_127 = lean_ctor_get(x_118, 6);
lean_inc(x_127);
x_128 = lean_ctor_get(x_118, 7);
lean_inc(x_128);
x_129 = lean_ctor_get(x_118, 8);
lean_inc(x_129);
x_130 = lean_ctor_get(x_118, 9);
lean_inc(x_130);
x_131 = lean_ctor_get(x_118, 10);
lean_inc(x_131);
x_132 = lean_ctor_get(x_118, 11);
lean_inc(x_132);
x_133 = lean_ctor_get(x_118, 12);
lean_inc(x_133);
x_134 = lean_ctor_get(x_118, 13);
lean_inc(x_134);
x_135 = lean_ctor_get(x_118, 14);
lean_inc(x_135);
x_136 = lean_ctor_get(x_118, 15);
lean_inc(x_136);
x_137 = lean_ctor_get(x_118, 16);
lean_inc(x_137);
x_138 = lean_ctor_get(x_118, 17);
lean_inc(x_138);
x_139 = lean_ctor_get(x_118, 18);
lean_inc(x_139);
x_140 = lean_ctor_get(x_118, 19);
lean_inc(x_140);
x_141 = lean_ctor_get(x_118, 20);
lean_inc(x_141);
x_142 = lean_ctor_get(x_118, 21);
lean_inc(x_142);
x_143 = lean_ctor_get(x_118, 22);
lean_inc(x_143);
x_144 = lean_ctor_get(x_118, 23);
lean_inc(x_144);
x_145 = lean_ctor_get(x_118, 24);
lean_inc(x_145);
x_146 = lean_ctor_get(x_118, 25);
lean_inc(x_146);
x_147 = lean_ctor_get(x_118, 26);
lean_inc(x_147);
x_148 = lean_ctor_get(x_118, 27);
lean_inc(x_148);
x_149 = lean_ctor_get(x_118, 28);
lean_inc(x_149);
x_150 = lean_ctor_get(x_118, 29);
lean_inc(x_150);
x_151 = lean_ctor_get(x_118, 30);
lean_inc(x_151);
x_152 = lean_ctor_get(x_118, 31);
lean_inc(x_152);
x_153 = lean_ctor_get(x_118, 32);
lean_inc(x_153);
x_154 = lean_ctor_get_uint8(x_118, sizeof(void*)*39);
x_155 = lean_ctor_get(x_118, 33);
lean_inc(x_155);
x_156 = lean_ctor_get(x_118, 34);
lean_inc(x_156);
x_157 = lean_ctor_get(x_118, 35);
lean_inc(x_157);
x_158 = lean_ctor_get(x_118, 36);
lean_inc(x_158);
x_159 = lean_ctor_get(x_118, 37);
lean_inc(x_159);
x_160 = lean_ctor_get(x_118, 38);
lean_inc(x_160);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 lean_ctor_release(x_118, 5);
 lean_ctor_release(x_118, 6);
 lean_ctor_release(x_118, 7);
 lean_ctor_release(x_118, 8);
 lean_ctor_release(x_118, 9);
 lean_ctor_release(x_118, 10);
 lean_ctor_release(x_118, 11);
 lean_ctor_release(x_118, 12);
 lean_ctor_release(x_118, 13);
 lean_ctor_release(x_118, 14);
 lean_ctor_release(x_118, 15);
 lean_ctor_release(x_118, 16);
 lean_ctor_release(x_118, 17);
 lean_ctor_release(x_118, 18);
 lean_ctor_release(x_118, 19);
 lean_ctor_release(x_118, 20);
 lean_ctor_release(x_118, 21);
 lean_ctor_release(x_118, 22);
 lean_ctor_release(x_118, 23);
 lean_ctor_release(x_118, 24);
 lean_ctor_release(x_118, 25);
 lean_ctor_release(x_118, 26);
 lean_ctor_release(x_118, 27);
 lean_ctor_release(x_118, 28);
 lean_ctor_release(x_118, 29);
 lean_ctor_release(x_118, 30);
 lean_ctor_release(x_118, 31);
 lean_ctor_release(x_118, 32);
 lean_ctor_release(x_118, 33);
 lean_ctor_release(x_118, 34);
 lean_ctor_release(x_118, 35);
 lean_ctor_release(x_118, 36);
 lean_ctor_release(x_118, 37);
 lean_ctor_release(x_118, 38);
 x_161 = x_118;
} else {
 lean_dec_ref(x_118);
 x_161 = lean_box(0);
}
x_162 = lean_box(0);
x_163 = l_Lean_PersistentArray_set___rarg(x_159, x_2, x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 39, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_121);
lean_ctor_set(x_164, 1, x_122);
lean_ctor_set(x_164, 2, x_123);
lean_ctor_set(x_164, 3, x_124);
lean_ctor_set(x_164, 4, x_125);
lean_ctor_set(x_164, 5, x_126);
lean_ctor_set(x_164, 6, x_127);
lean_ctor_set(x_164, 7, x_128);
lean_ctor_set(x_164, 8, x_129);
lean_ctor_set(x_164, 9, x_130);
lean_ctor_set(x_164, 10, x_131);
lean_ctor_set(x_164, 11, x_132);
lean_ctor_set(x_164, 12, x_133);
lean_ctor_set(x_164, 13, x_134);
lean_ctor_set(x_164, 14, x_135);
lean_ctor_set(x_164, 15, x_136);
lean_ctor_set(x_164, 16, x_137);
lean_ctor_set(x_164, 17, x_138);
lean_ctor_set(x_164, 18, x_139);
lean_ctor_set(x_164, 19, x_140);
lean_ctor_set(x_164, 20, x_141);
lean_ctor_set(x_164, 21, x_142);
lean_ctor_set(x_164, 22, x_143);
lean_ctor_set(x_164, 23, x_144);
lean_ctor_set(x_164, 24, x_145);
lean_ctor_set(x_164, 25, x_146);
lean_ctor_set(x_164, 26, x_147);
lean_ctor_set(x_164, 27, x_148);
lean_ctor_set(x_164, 28, x_149);
lean_ctor_set(x_164, 29, x_150);
lean_ctor_set(x_164, 30, x_151);
lean_ctor_set(x_164, 31, x_152);
lean_ctor_set(x_164, 32, x_153);
lean_ctor_set(x_164, 33, x_155);
lean_ctor_set(x_164, 34, x_156);
lean_ctor_set(x_164, 35, x_157);
lean_ctor_set(x_164, 36, x_158);
lean_ctor_set(x_164, 37, x_163);
lean_ctor_set(x_164, 38, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*39, x_154);
x_165 = lean_array_fset(x_120, x_4, x_164);
x_166 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_111);
lean_ctor_set(x_166, 2, x_112);
lean_ctor_set(x_41, 3, x_166);
x_167 = lean_st_ref_set(x_5, x_40, x_43);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_22 = x_168;
goto block_39;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_169 = lean_ctor_get(x_41, 0);
x_170 = lean_ctor_get(x_41, 1);
x_171 = lean_ctor_get(x_41, 2);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_41);
x_172 = lean_ctor_get(x_42, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_42, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_42, 2);
lean_inc(x_174);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 x_175 = x_42;
} else {
 lean_dec_ref(x_42);
 x_175 = lean_box(0);
}
x_176 = lean_array_get_size(x_172);
x_177 = lean_nat_dec_lt(x_4, x_176);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
if (lean_is_scalar(x_175)) {
 x_178 = lean_alloc_ctor(0, 3, 0);
} else {
 x_178 = x_175;
}
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set(x_178, 1, x_173);
lean_ctor_set(x_178, 2, x_174);
x_179 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_179, 0, x_169);
lean_ctor_set(x_179, 1, x_170);
lean_ctor_set(x_179, 2, x_171);
lean_ctor_set(x_179, 3, x_178);
lean_ctor_set(x_40, 14, x_179);
x_180 = lean_st_ref_set(x_5, x_40, x_43);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_22 = x_181;
goto block_39;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_182 = lean_array_fget(x_172, x_4);
x_183 = lean_box(0);
x_184 = lean_array_fset(x_172, x_4, x_183);
x_185 = lean_ctor_get(x_182, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_182, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_182, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_182, 3);
lean_inc(x_188);
x_189 = lean_ctor_get(x_182, 4);
lean_inc(x_189);
x_190 = lean_ctor_get(x_182, 5);
lean_inc(x_190);
x_191 = lean_ctor_get(x_182, 6);
lean_inc(x_191);
x_192 = lean_ctor_get(x_182, 7);
lean_inc(x_192);
x_193 = lean_ctor_get(x_182, 8);
lean_inc(x_193);
x_194 = lean_ctor_get(x_182, 9);
lean_inc(x_194);
x_195 = lean_ctor_get(x_182, 10);
lean_inc(x_195);
x_196 = lean_ctor_get(x_182, 11);
lean_inc(x_196);
x_197 = lean_ctor_get(x_182, 12);
lean_inc(x_197);
x_198 = lean_ctor_get(x_182, 13);
lean_inc(x_198);
x_199 = lean_ctor_get(x_182, 14);
lean_inc(x_199);
x_200 = lean_ctor_get(x_182, 15);
lean_inc(x_200);
x_201 = lean_ctor_get(x_182, 16);
lean_inc(x_201);
x_202 = lean_ctor_get(x_182, 17);
lean_inc(x_202);
x_203 = lean_ctor_get(x_182, 18);
lean_inc(x_203);
x_204 = lean_ctor_get(x_182, 19);
lean_inc(x_204);
x_205 = lean_ctor_get(x_182, 20);
lean_inc(x_205);
x_206 = lean_ctor_get(x_182, 21);
lean_inc(x_206);
x_207 = lean_ctor_get(x_182, 22);
lean_inc(x_207);
x_208 = lean_ctor_get(x_182, 23);
lean_inc(x_208);
x_209 = lean_ctor_get(x_182, 24);
lean_inc(x_209);
x_210 = lean_ctor_get(x_182, 25);
lean_inc(x_210);
x_211 = lean_ctor_get(x_182, 26);
lean_inc(x_211);
x_212 = lean_ctor_get(x_182, 27);
lean_inc(x_212);
x_213 = lean_ctor_get(x_182, 28);
lean_inc(x_213);
x_214 = lean_ctor_get(x_182, 29);
lean_inc(x_214);
x_215 = lean_ctor_get(x_182, 30);
lean_inc(x_215);
x_216 = lean_ctor_get(x_182, 31);
lean_inc(x_216);
x_217 = lean_ctor_get(x_182, 32);
lean_inc(x_217);
x_218 = lean_ctor_get_uint8(x_182, sizeof(void*)*39);
x_219 = lean_ctor_get(x_182, 33);
lean_inc(x_219);
x_220 = lean_ctor_get(x_182, 34);
lean_inc(x_220);
x_221 = lean_ctor_get(x_182, 35);
lean_inc(x_221);
x_222 = lean_ctor_get(x_182, 36);
lean_inc(x_222);
x_223 = lean_ctor_get(x_182, 37);
lean_inc(x_223);
x_224 = lean_ctor_get(x_182, 38);
lean_inc(x_224);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 lean_ctor_release(x_182, 3);
 lean_ctor_release(x_182, 4);
 lean_ctor_release(x_182, 5);
 lean_ctor_release(x_182, 6);
 lean_ctor_release(x_182, 7);
 lean_ctor_release(x_182, 8);
 lean_ctor_release(x_182, 9);
 lean_ctor_release(x_182, 10);
 lean_ctor_release(x_182, 11);
 lean_ctor_release(x_182, 12);
 lean_ctor_release(x_182, 13);
 lean_ctor_release(x_182, 14);
 lean_ctor_release(x_182, 15);
 lean_ctor_release(x_182, 16);
 lean_ctor_release(x_182, 17);
 lean_ctor_release(x_182, 18);
 lean_ctor_release(x_182, 19);
 lean_ctor_release(x_182, 20);
 lean_ctor_release(x_182, 21);
 lean_ctor_release(x_182, 22);
 lean_ctor_release(x_182, 23);
 lean_ctor_release(x_182, 24);
 lean_ctor_release(x_182, 25);
 lean_ctor_release(x_182, 26);
 lean_ctor_release(x_182, 27);
 lean_ctor_release(x_182, 28);
 lean_ctor_release(x_182, 29);
 lean_ctor_release(x_182, 30);
 lean_ctor_release(x_182, 31);
 lean_ctor_release(x_182, 32);
 lean_ctor_release(x_182, 33);
 lean_ctor_release(x_182, 34);
 lean_ctor_release(x_182, 35);
 lean_ctor_release(x_182, 36);
 lean_ctor_release(x_182, 37);
 lean_ctor_release(x_182, 38);
 x_225 = x_182;
} else {
 lean_dec_ref(x_182);
 x_225 = lean_box(0);
}
x_226 = lean_box(0);
x_227 = l_Lean_PersistentArray_set___rarg(x_223, x_2, x_226);
if (lean_is_scalar(x_225)) {
 x_228 = lean_alloc_ctor(0, 39, 1);
} else {
 x_228 = x_225;
}
lean_ctor_set(x_228, 0, x_185);
lean_ctor_set(x_228, 1, x_186);
lean_ctor_set(x_228, 2, x_187);
lean_ctor_set(x_228, 3, x_188);
lean_ctor_set(x_228, 4, x_189);
lean_ctor_set(x_228, 5, x_190);
lean_ctor_set(x_228, 6, x_191);
lean_ctor_set(x_228, 7, x_192);
lean_ctor_set(x_228, 8, x_193);
lean_ctor_set(x_228, 9, x_194);
lean_ctor_set(x_228, 10, x_195);
lean_ctor_set(x_228, 11, x_196);
lean_ctor_set(x_228, 12, x_197);
lean_ctor_set(x_228, 13, x_198);
lean_ctor_set(x_228, 14, x_199);
lean_ctor_set(x_228, 15, x_200);
lean_ctor_set(x_228, 16, x_201);
lean_ctor_set(x_228, 17, x_202);
lean_ctor_set(x_228, 18, x_203);
lean_ctor_set(x_228, 19, x_204);
lean_ctor_set(x_228, 20, x_205);
lean_ctor_set(x_228, 21, x_206);
lean_ctor_set(x_228, 22, x_207);
lean_ctor_set(x_228, 23, x_208);
lean_ctor_set(x_228, 24, x_209);
lean_ctor_set(x_228, 25, x_210);
lean_ctor_set(x_228, 26, x_211);
lean_ctor_set(x_228, 27, x_212);
lean_ctor_set(x_228, 28, x_213);
lean_ctor_set(x_228, 29, x_214);
lean_ctor_set(x_228, 30, x_215);
lean_ctor_set(x_228, 31, x_216);
lean_ctor_set(x_228, 32, x_217);
lean_ctor_set(x_228, 33, x_219);
lean_ctor_set(x_228, 34, x_220);
lean_ctor_set(x_228, 35, x_221);
lean_ctor_set(x_228, 36, x_222);
lean_ctor_set(x_228, 37, x_227);
lean_ctor_set(x_228, 38, x_224);
lean_ctor_set_uint8(x_228, sizeof(void*)*39, x_218);
x_229 = lean_array_fset(x_184, x_4, x_228);
if (lean_is_scalar(x_175)) {
 x_230 = lean_alloc_ctor(0, 3, 0);
} else {
 x_230 = x_175;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_173);
lean_ctor_set(x_230, 2, x_174);
x_231 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_231, 0, x_169);
lean_ctor_set(x_231, 1, x_170);
lean_ctor_set(x_231, 2, x_171);
lean_ctor_set(x_231, 3, x_230);
lean_ctor_set(x_40, 14, x_231);
x_232 = lean_st_ref_set(x_5, x_40, x_43);
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
x_22 = x_233;
goto block_39;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_234 = lean_ctor_get(x_40, 0);
x_235 = lean_ctor_get(x_40, 1);
x_236 = lean_ctor_get(x_40, 2);
x_237 = lean_ctor_get(x_40, 3);
x_238 = lean_ctor_get(x_40, 4);
x_239 = lean_ctor_get(x_40, 5);
x_240 = lean_ctor_get(x_40, 6);
x_241 = lean_ctor_get(x_40, 7);
x_242 = lean_ctor_get_uint8(x_40, sizeof(void*)*16);
x_243 = lean_ctor_get(x_40, 8);
x_244 = lean_ctor_get(x_40, 9);
x_245 = lean_ctor_get(x_40, 10);
x_246 = lean_ctor_get(x_40, 11);
x_247 = lean_ctor_get(x_40, 12);
x_248 = lean_ctor_get(x_40, 13);
x_249 = lean_ctor_get(x_40, 15);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_40);
x_250 = lean_ctor_get(x_41, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_41, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_41, 2);
lean_inc(x_252);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_253 = x_41;
} else {
 lean_dec_ref(x_41);
 x_253 = lean_box(0);
}
x_254 = lean_ctor_get(x_42, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_42, 1);
lean_inc(x_255);
x_256 = lean_ctor_get(x_42, 2);
lean_inc(x_256);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 x_257 = x_42;
} else {
 lean_dec_ref(x_42);
 x_257 = lean_box(0);
}
x_258 = lean_array_get_size(x_254);
x_259 = lean_nat_dec_lt(x_4, x_258);
lean_dec(x_258);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
if (lean_is_scalar(x_257)) {
 x_260 = lean_alloc_ctor(0, 3, 0);
} else {
 x_260 = x_257;
}
lean_ctor_set(x_260, 0, x_254);
lean_ctor_set(x_260, 1, x_255);
lean_ctor_set(x_260, 2, x_256);
if (lean_is_scalar(x_253)) {
 x_261 = lean_alloc_ctor(0, 4, 0);
} else {
 x_261 = x_253;
}
lean_ctor_set(x_261, 0, x_250);
lean_ctor_set(x_261, 1, x_251);
lean_ctor_set(x_261, 2, x_252);
lean_ctor_set(x_261, 3, x_260);
x_262 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_262, 0, x_234);
lean_ctor_set(x_262, 1, x_235);
lean_ctor_set(x_262, 2, x_236);
lean_ctor_set(x_262, 3, x_237);
lean_ctor_set(x_262, 4, x_238);
lean_ctor_set(x_262, 5, x_239);
lean_ctor_set(x_262, 6, x_240);
lean_ctor_set(x_262, 7, x_241);
lean_ctor_set(x_262, 8, x_243);
lean_ctor_set(x_262, 9, x_244);
lean_ctor_set(x_262, 10, x_245);
lean_ctor_set(x_262, 11, x_246);
lean_ctor_set(x_262, 12, x_247);
lean_ctor_set(x_262, 13, x_248);
lean_ctor_set(x_262, 14, x_261);
lean_ctor_set(x_262, 15, x_249);
lean_ctor_set_uint8(x_262, sizeof(void*)*16, x_242);
x_263 = lean_st_ref_set(x_5, x_262, x_43);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_22 = x_264;
goto block_39;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_265 = lean_array_fget(x_254, x_4);
x_266 = lean_box(0);
x_267 = lean_array_fset(x_254, x_4, x_266);
x_268 = lean_ctor_get(x_265, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_265, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_265, 2);
lean_inc(x_270);
x_271 = lean_ctor_get(x_265, 3);
lean_inc(x_271);
x_272 = lean_ctor_get(x_265, 4);
lean_inc(x_272);
x_273 = lean_ctor_get(x_265, 5);
lean_inc(x_273);
x_274 = lean_ctor_get(x_265, 6);
lean_inc(x_274);
x_275 = lean_ctor_get(x_265, 7);
lean_inc(x_275);
x_276 = lean_ctor_get(x_265, 8);
lean_inc(x_276);
x_277 = lean_ctor_get(x_265, 9);
lean_inc(x_277);
x_278 = lean_ctor_get(x_265, 10);
lean_inc(x_278);
x_279 = lean_ctor_get(x_265, 11);
lean_inc(x_279);
x_280 = lean_ctor_get(x_265, 12);
lean_inc(x_280);
x_281 = lean_ctor_get(x_265, 13);
lean_inc(x_281);
x_282 = lean_ctor_get(x_265, 14);
lean_inc(x_282);
x_283 = lean_ctor_get(x_265, 15);
lean_inc(x_283);
x_284 = lean_ctor_get(x_265, 16);
lean_inc(x_284);
x_285 = lean_ctor_get(x_265, 17);
lean_inc(x_285);
x_286 = lean_ctor_get(x_265, 18);
lean_inc(x_286);
x_287 = lean_ctor_get(x_265, 19);
lean_inc(x_287);
x_288 = lean_ctor_get(x_265, 20);
lean_inc(x_288);
x_289 = lean_ctor_get(x_265, 21);
lean_inc(x_289);
x_290 = lean_ctor_get(x_265, 22);
lean_inc(x_290);
x_291 = lean_ctor_get(x_265, 23);
lean_inc(x_291);
x_292 = lean_ctor_get(x_265, 24);
lean_inc(x_292);
x_293 = lean_ctor_get(x_265, 25);
lean_inc(x_293);
x_294 = lean_ctor_get(x_265, 26);
lean_inc(x_294);
x_295 = lean_ctor_get(x_265, 27);
lean_inc(x_295);
x_296 = lean_ctor_get(x_265, 28);
lean_inc(x_296);
x_297 = lean_ctor_get(x_265, 29);
lean_inc(x_297);
x_298 = lean_ctor_get(x_265, 30);
lean_inc(x_298);
x_299 = lean_ctor_get(x_265, 31);
lean_inc(x_299);
x_300 = lean_ctor_get(x_265, 32);
lean_inc(x_300);
x_301 = lean_ctor_get_uint8(x_265, sizeof(void*)*39);
x_302 = lean_ctor_get(x_265, 33);
lean_inc(x_302);
x_303 = lean_ctor_get(x_265, 34);
lean_inc(x_303);
x_304 = lean_ctor_get(x_265, 35);
lean_inc(x_304);
x_305 = lean_ctor_get(x_265, 36);
lean_inc(x_305);
x_306 = lean_ctor_get(x_265, 37);
lean_inc(x_306);
x_307 = lean_ctor_get(x_265, 38);
lean_inc(x_307);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 lean_ctor_release(x_265, 2);
 lean_ctor_release(x_265, 3);
 lean_ctor_release(x_265, 4);
 lean_ctor_release(x_265, 5);
 lean_ctor_release(x_265, 6);
 lean_ctor_release(x_265, 7);
 lean_ctor_release(x_265, 8);
 lean_ctor_release(x_265, 9);
 lean_ctor_release(x_265, 10);
 lean_ctor_release(x_265, 11);
 lean_ctor_release(x_265, 12);
 lean_ctor_release(x_265, 13);
 lean_ctor_release(x_265, 14);
 lean_ctor_release(x_265, 15);
 lean_ctor_release(x_265, 16);
 lean_ctor_release(x_265, 17);
 lean_ctor_release(x_265, 18);
 lean_ctor_release(x_265, 19);
 lean_ctor_release(x_265, 20);
 lean_ctor_release(x_265, 21);
 lean_ctor_release(x_265, 22);
 lean_ctor_release(x_265, 23);
 lean_ctor_release(x_265, 24);
 lean_ctor_release(x_265, 25);
 lean_ctor_release(x_265, 26);
 lean_ctor_release(x_265, 27);
 lean_ctor_release(x_265, 28);
 lean_ctor_release(x_265, 29);
 lean_ctor_release(x_265, 30);
 lean_ctor_release(x_265, 31);
 lean_ctor_release(x_265, 32);
 lean_ctor_release(x_265, 33);
 lean_ctor_release(x_265, 34);
 lean_ctor_release(x_265, 35);
 lean_ctor_release(x_265, 36);
 lean_ctor_release(x_265, 37);
 lean_ctor_release(x_265, 38);
 x_308 = x_265;
} else {
 lean_dec_ref(x_265);
 x_308 = lean_box(0);
}
x_309 = lean_box(0);
x_310 = l_Lean_PersistentArray_set___rarg(x_306, x_2, x_309);
if (lean_is_scalar(x_308)) {
 x_311 = lean_alloc_ctor(0, 39, 1);
} else {
 x_311 = x_308;
}
lean_ctor_set(x_311, 0, x_268);
lean_ctor_set(x_311, 1, x_269);
lean_ctor_set(x_311, 2, x_270);
lean_ctor_set(x_311, 3, x_271);
lean_ctor_set(x_311, 4, x_272);
lean_ctor_set(x_311, 5, x_273);
lean_ctor_set(x_311, 6, x_274);
lean_ctor_set(x_311, 7, x_275);
lean_ctor_set(x_311, 8, x_276);
lean_ctor_set(x_311, 9, x_277);
lean_ctor_set(x_311, 10, x_278);
lean_ctor_set(x_311, 11, x_279);
lean_ctor_set(x_311, 12, x_280);
lean_ctor_set(x_311, 13, x_281);
lean_ctor_set(x_311, 14, x_282);
lean_ctor_set(x_311, 15, x_283);
lean_ctor_set(x_311, 16, x_284);
lean_ctor_set(x_311, 17, x_285);
lean_ctor_set(x_311, 18, x_286);
lean_ctor_set(x_311, 19, x_287);
lean_ctor_set(x_311, 20, x_288);
lean_ctor_set(x_311, 21, x_289);
lean_ctor_set(x_311, 22, x_290);
lean_ctor_set(x_311, 23, x_291);
lean_ctor_set(x_311, 24, x_292);
lean_ctor_set(x_311, 25, x_293);
lean_ctor_set(x_311, 26, x_294);
lean_ctor_set(x_311, 27, x_295);
lean_ctor_set(x_311, 28, x_296);
lean_ctor_set(x_311, 29, x_297);
lean_ctor_set(x_311, 30, x_298);
lean_ctor_set(x_311, 31, x_299);
lean_ctor_set(x_311, 32, x_300);
lean_ctor_set(x_311, 33, x_302);
lean_ctor_set(x_311, 34, x_303);
lean_ctor_set(x_311, 35, x_304);
lean_ctor_set(x_311, 36, x_305);
lean_ctor_set(x_311, 37, x_310);
lean_ctor_set(x_311, 38, x_307);
lean_ctor_set_uint8(x_311, sizeof(void*)*39, x_301);
x_312 = lean_array_fset(x_267, x_4, x_311);
if (lean_is_scalar(x_257)) {
 x_313 = lean_alloc_ctor(0, 3, 0);
} else {
 x_313 = x_257;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_255);
lean_ctor_set(x_313, 2, x_256);
if (lean_is_scalar(x_253)) {
 x_314 = lean_alloc_ctor(0, 4, 0);
} else {
 x_314 = x_253;
}
lean_ctor_set(x_314, 0, x_250);
lean_ctor_set(x_314, 1, x_251);
lean_ctor_set(x_314, 2, x_252);
lean_ctor_set(x_314, 3, x_313);
x_315 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_315, 0, x_234);
lean_ctor_set(x_315, 1, x_235);
lean_ctor_set(x_315, 2, x_236);
lean_ctor_set(x_315, 3, x_237);
lean_ctor_set(x_315, 4, x_238);
lean_ctor_set(x_315, 5, x_239);
lean_ctor_set(x_315, 6, x_240);
lean_ctor_set(x_315, 7, x_241);
lean_ctor_set(x_315, 8, x_243);
lean_ctor_set(x_315, 9, x_244);
lean_ctor_set(x_315, 10, x_245);
lean_ctor_set(x_315, 11, x_246);
lean_ctor_set(x_315, 12, x_247);
lean_ctor_set(x_315, 13, x_248);
lean_ctor_set(x_315, 14, x_314);
lean_ctor_set(x_315, 15, x_249);
lean_ctor_set_uint8(x_315, sizeof(void*)*16, x_242);
x_316 = lean_st_ref_set(x_5, x_315, x_43);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
x_22 = x_317;
goto block_39;
}
}
block_39:
{
lean_object* x_23; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(x_1, x_2, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = l_Lean_RBNode_forIn_visit___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___spec__1(x_1, x_2, x_3, x_21, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
lean_dec(x_21);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
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
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
else
{
uint8_t x_323; 
lean_dec(x_12);
lean_dec(x_11);
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
x_323 = !lean_is_exclusive(x_14);
if (x_323 == 0)
{
return x_14;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_14, 0);
x_325 = lean_ctor_get(x_14, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_14);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_RBNode_forIn_visit___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_st_ref_take(x_6, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 14);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_16, 14);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_17, 3);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_array_get_size(x_27);
x_29 = lean_nat_dec_lt(x_5, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_15);
x_30 = lean_st_ref_set(x_6, x_16, x_20);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_array_fget(x_27, x_5);
x_34 = lean_box(0);
x_35 = lean_array_fset(x_27, x_5, x_34);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_33, 35);
x_38 = lean_ctor_get(x_33, 36);
lean_inc(x_3);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_3);
x_40 = l_Lean_PersistentArray_set___rarg(x_37, x_2, x_39);
lean_inc(x_2);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_38);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_33, 36, x_15);
lean_ctor_set(x_33, 35, x_40);
x_41 = lean_array_fset(x_35, x_5, x_33);
lean_ctor_set(x_18, 0, x_41);
x_42 = lean_st_ref_set(x_6, x_16, x_20);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_45 = lean_ctor_get(x_33, 0);
x_46 = lean_ctor_get(x_33, 1);
x_47 = lean_ctor_get(x_33, 2);
x_48 = lean_ctor_get(x_33, 3);
x_49 = lean_ctor_get(x_33, 4);
x_50 = lean_ctor_get(x_33, 5);
x_51 = lean_ctor_get(x_33, 6);
x_52 = lean_ctor_get(x_33, 7);
x_53 = lean_ctor_get(x_33, 8);
x_54 = lean_ctor_get(x_33, 9);
x_55 = lean_ctor_get(x_33, 10);
x_56 = lean_ctor_get(x_33, 11);
x_57 = lean_ctor_get(x_33, 12);
x_58 = lean_ctor_get(x_33, 13);
x_59 = lean_ctor_get(x_33, 14);
x_60 = lean_ctor_get(x_33, 15);
x_61 = lean_ctor_get(x_33, 16);
x_62 = lean_ctor_get(x_33, 17);
x_63 = lean_ctor_get(x_33, 18);
x_64 = lean_ctor_get(x_33, 19);
x_65 = lean_ctor_get(x_33, 20);
x_66 = lean_ctor_get(x_33, 21);
x_67 = lean_ctor_get(x_33, 22);
x_68 = lean_ctor_get(x_33, 23);
x_69 = lean_ctor_get(x_33, 24);
x_70 = lean_ctor_get(x_33, 25);
x_71 = lean_ctor_get(x_33, 26);
x_72 = lean_ctor_get(x_33, 27);
x_73 = lean_ctor_get(x_33, 28);
x_74 = lean_ctor_get(x_33, 29);
x_75 = lean_ctor_get(x_33, 30);
x_76 = lean_ctor_get(x_33, 31);
x_77 = lean_ctor_get(x_33, 32);
x_78 = lean_ctor_get_uint8(x_33, sizeof(void*)*39);
x_79 = lean_ctor_get(x_33, 33);
x_80 = lean_ctor_get(x_33, 34);
x_81 = lean_ctor_get(x_33, 35);
x_82 = lean_ctor_get(x_33, 36);
x_83 = lean_ctor_get(x_33, 37);
x_84 = lean_ctor_get(x_33, 38);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
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
lean_dec(x_33);
lean_inc(x_3);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_3);
x_86 = l_Lean_PersistentArray_set___rarg(x_81, x_2, x_85);
lean_inc(x_2);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_82);
lean_ctor_set(x_15, 0, x_2);
x_87 = lean_alloc_ctor(0, 39, 1);
lean_ctor_set(x_87, 0, x_45);
lean_ctor_set(x_87, 1, x_46);
lean_ctor_set(x_87, 2, x_47);
lean_ctor_set(x_87, 3, x_48);
lean_ctor_set(x_87, 4, x_49);
lean_ctor_set(x_87, 5, x_50);
lean_ctor_set(x_87, 6, x_51);
lean_ctor_set(x_87, 7, x_52);
lean_ctor_set(x_87, 8, x_53);
lean_ctor_set(x_87, 9, x_54);
lean_ctor_set(x_87, 10, x_55);
lean_ctor_set(x_87, 11, x_56);
lean_ctor_set(x_87, 12, x_57);
lean_ctor_set(x_87, 13, x_58);
lean_ctor_set(x_87, 14, x_59);
lean_ctor_set(x_87, 15, x_60);
lean_ctor_set(x_87, 16, x_61);
lean_ctor_set(x_87, 17, x_62);
lean_ctor_set(x_87, 18, x_63);
lean_ctor_set(x_87, 19, x_64);
lean_ctor_set(x_87, 20, x_65);
lean_ctor_set(x_87, 21, x_66);
lean_ctor_set(x_87, 22, x_67);
lean_ctor_set(x_87, 23, x_68);
lean_ctor_set(x_87, 24, x_69);
lean_ctor_set(x_87, 25, x_70);
lean_ctor_set(x_87, 26, x_71);
lean_ctor_set(x_87, 27, x_72);
lean_ctor_set(x_87, 28, x_73);
lean_ctor_set(x_87, 29, x_74);
lean_ctor_set(x_87, 30, x_75);
lean_ctor_set(x_87, 31, x_76);
lean_ctor_set(x_87, 32, x_77);
lean_ctor_set(x_87, 33, x_79);
lean_ctor_set(x_87, 34, x_80);
lean_ctor_set(x_87, 35, x_86);
lean_ctor_set(x_87, 36, x_15);
lean_ctor_set(x_87, 37, x_83);
lean_ctor_set(x_87, 38, x_84);
lean_ctor_set_uint8(x_87, sizeof(void*)*39, x_78);
x_88 = lean_array_fset(x_35, x_5, x_87);
lean_ctor_set(x_18, 0, x_88);
x_89 = lean_st_ref_set(x_6, x_16, x_20);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_18, 0);
x_93 = lean_ctor_get(x_18, 1);
x_94 = lean_ctor_get(x_18, 2);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_18);
x_95 = lean_array_get_size(x_92);
x_96 = lean_nat_dec_lt(x_5, x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_free_object(x_15);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_93);
lean_ctor_set(x_97, 2, x_94);
lean_ctor_set(x_17, 3, x_97);
x_98 = lean_st_ref_set(x_6, x_16, x_20);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_99);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_101 = lean_array_fget(x_92, x_5);
x_102 = lean_box(0);
x_103 = lean_array_fset(x_92, x_5, x_102);
x_104 = lean_ctor_get(x_101, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_101, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_101, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_101, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_101, 5);
lean_inc(x_109);
x_110 = lean_ctor_get(x_101, 6);
lean_inc(x_110);
x_111 = lean_ctor_get(x_101, 7);
lean_inc(x_111);
x_112 = lean_ctor_get(x_101, 8);
lean_inc(x_112);
x_113 = lean_ctor_get(x_101, 9);
lean_inc(x_113);
x_114 = lean_ctor_get(x_101, 10);
lean_inc(x_114);
x_115 = lean_ctor_get(x_101, 11);
lean_inc(x_115);
x_116 = lean_ctor_get(x_101, 12);
lean_inc(x_116);
x_117 = lean_ctor_get(x_101, 13);
lean_inc(x_117);
x_118 = lean_ctor_get(x_101, 14);
lean_inc(x_118);
x_119 = lean_ctor_get(x_101, 15);
lean_inc(x_119);
x_120 = lean_ctor_get(x_101, 16);
lean_inc(x_120);
x_121 = lean_ctor_get(x_101, 17);
lean_inc(x_121);
x_122 = lean_ctor_get(x_101, 18);
lean_inc(x_122);
x_123 = lean_ctor_get(x_101, 19);
lean_inc(x_123);
x_124 = lean_ctor_get(x_101, 20);
lean_inc(x_124);
x_125 = lean_ctor_get(x_101, 21);
lean_inc(x_125);
x_126 = lean_ctor_get(x_101, 22);
lean_inc(x_126);
x_127 = lean_ctor_get(x_101, 23);
lean_inc(x_127);
x_128 = lean_ctor_get(x_101, 24);
lean_inc(x_128);
x_129 = lean_ctor_get(x_101, 25);
lean_inc(x_129);
x_130 = lean_ctor_get(x_101, 26);
lean_inc(x_130);
x_131 = lean_ctor_get(x_101, 27);
lean_inc(x_131);
x_132 = lean_ctor_get(x_101, 28);
lean_inc(x_132);
x_133 = lean_ctor_get(x_101, 29);
lean_inc(x_133);
x_134 = lean_ctor_get(x_101, 30);
lean_inc(x_134);
x_135 = lean_ctor_get(x_101, 31);
lean_inc(x_135);
x_136 = lean_ctor_get(x_101, 32);
lean_inc(x_136);
x_137 = lean_ctor_get_uint8(x_101, sizeof(void*)*39);
x_138 = lean_ctor_get(x_101, 33);
lean_inc(x_138);
x_139 = lean_ctor_get(x_101, 34);
lean_inc(x_139);
x_140 = lean_ctor_get(x_101, 35);
lean_inc(x_140);
x_141 = lean_ctor_get(x_101, 36);
lean_inc(x_141);
x_142 = lean_ctor_get(x_101, 37);
lean_inc(x_142);
x_143 = lean_ctor_get(x_101, 38);
lean_inc(x_143);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 lean_ctor_release(x_101, 3);
 lean_ctor_release(x_101, 4);
 lean_ctor_release(x_101, 5);
 lean_ctor_release(x_101, 6);
 lean_ctor_release(x_101, 7);
 lean_ctor_release(x_101, 8);
 lean_ctor_release(x_101, 9);
 lean_ctor_release(x_101, 10);
 lean_ctor_release(x_101, 11);
 lean_ctor_release(x_101, 12);
 lean_ctor_release(x_101, 13);
 lean_ctor_release(x_101, 14);
 lean_ctor_release(x_101, 15);
 lean_ctor_release(x_101, 16);
 lean_ctor_release(x_101, 17);
 lean_ctor_release(x_101, 18);
 lean_ctor_release(x_101, 19);
 lean_ctor_release(x_101, 20);
 lean_ctor_release(x_101, 21);
 lean_ctor_release(x_101, 22);
 lean_ctor_release(x_101, 23);
 lean_ctor_release(x_101, 24);
 lean_ctor_release(x_101, 25);
 lean_ctor_release(x_101, 26);
 lean_ctor_release(x_101, 27);
 lean_ctor_release(x_101, 28);
 lean_ctor_release(x_101, 29);
 lean_ctor_release(x_101, 30);
 lean_ctor_release(x_101, 31);
 lean_ctor_release(x_101, 32);
 lean_ctor_release(x_101, 33);
 lean_ctor_release(x_101, 34);
 lean_ctor_release(x_101, 35);
 lean_ctor_release(x_101, 36);
 lean_ctor_release(x_101, 37);
 lean_ctor_release(x_101, 38);
 x_144 = x_101;
} else {
 lean_dec_ref(x_101);
 x_144 = lean_box(0);
}
lean_inc(x_3);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_3);
x_146 = l_Lean_PersistentArray_set___rarg(x_140, x_2, x_145);
lean_inc(x_2);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_141);
lean_ctor_set(x_15, 0, x_2);
if (lean_is_scalar(x_144)) {
 x_147 = lean_alloc_ctor(0, 39, 1);
} else {
 x_147 = x_144;
}
lean_ctor_set(x_147, 0, x_104);
lean_ctor_set(x_147, 1, x_105);
lean_ctor_set(x_147, 2, x_106);
lean_ctor_set(x_147, 3, x_107);
lean_ctor_set(x_147, 4, x_108);
lean_ctor_set(x_147, 5, x_109);
lean_ctor_set(x_147, 6, x_110);
lean_ctor_set(x_147, 7, x_111);
lean_ctor_set(x_147, 8, x_112);
lean_ctor_set(x_147, 9, x_113);
lean_ctor_set(x_147, 10, x_114);
lean_ctor_set(x_147, 11, x_115);
lean_ctor_set(x_147, 12, x_116);
lean_ctor_set(x_147, 13, x_117);
lean_ctor_set(x_147, 14, x_118);
lean_ctor_set(x_147, 15, x_119);
lean_ctor_set(x_147, 16, x_120);
lean_ctor_set(x_147, 17, x_121);
lean_ctor_set(x_147, 18, x_122);
lean_ctor_set(x_147, 19, x_123);
lean_ctor_set(x_147, 20, x_124);
lean_ctor_set(x_147, 21, x_125);
lean_ctor_set(x_147, 22, x_126);
lean_ctor_set(x_147, 23, x_127);
lean_ctor_set(x_147, 24, x_128);
lean_ctor_set(x_147, 25, x_129);
lean_ctor_set(x_147, 26, x_130);
lean_ctor_set(x_147, 27, x_131);
lean_ctor_set(x_147, 28, x_132);
lean_ctor_set(x_147, 29, x_133);
lean_ctor_set(x_147, 30, x_134);
lean_ctor_set(x_147, 31, x_135);
lean_ctor_set(x_147, 32, x_136);
lean_ctor_set(x_147, 33, x_138);
lean_ctor_set(x_147, 34, x_139);
lean_ctor_set(x_147, 35, x_146);
lean_ctor_set(x_147, 36, x_15);
lean_ctor_set(x_147, 37, x_142);
lean_ctor_set(x_147, 38, x_143);
lean_ctor_set_uint8(x_147, sizeof(void*)*39, x_137);
x_148 = lean_array_fset(x_103, x_5, x_147);
x_149 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_93);
lean_ctor_set(x_149, 2, x_94);
lean_ctor_set(x_17, 3, x_149);
x_150 = lean_st_ref_set(x_6, x_16, x_20);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_151);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_153 = lean_ctor_get(x_17, 0);
x_154 = lean_ctor_get(x_17, 1);
x_155 = lean_ctor_get(x_17, 2);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_17);
x_156 = lean_ctor_get(x_18, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_18, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_18, 2);
lean_inc(x_158);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_159 = x_18;
} else {
 lean_dec_ref(x_18);
 x_159 = lean_box(0);
}
x_160 = lean_array_get_size(x_156);
x_161 = lean_nat_dec_lt(x_5, x_160);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_free_object(x_15);
if (lean_is_scalar(x_159)) {
 x_162 = lean_alloc_ctor(0, 3, 0);
} else {
 x_162 = x_159;
}
lean_ctor_set(x_162, 0, x_156);
lean_ctor_set(x_162, 1, x_157);
lean_ctor_set(x_162, 2, x_158);
x_163 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_163, 0, x_153);
lean_ctor_set(x_163, 1, x_154);
lean_ctor_set(x_163, 2, x_155);
lean_ctor_set(x_163, 3, x_162);
lean_ctor_set(x_16, 14, x_163);
x_164 = lean_st_ref_set(x_6, x_16, x_20);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_165);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_167 = lean_array_fget(x_156, x_5);
x_168 = lean_box(0);
x_169 = lean_array_fset(x_156, x_5, x_168);
x_170 = lean_ctor_get(x_167, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_167, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_167, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_167, 3);
lean_inc(x_173);
x_174 = lean_ctor_get(x_167, 4);
lean_inc(x_174);
x_175 = lean_ctor_get(x_167, 5);
lean_inc(x_175);
x_176 = lean_ctor_get(x_167, 6);
lean_inc(x_176);
x_177 = lean_ctor_get(x_167, 7);
lean_inc(x_177);
x_178 = lean_ctor_get(x_167, 8);
lean_inc(x_178);
x_179 = lean_ctor_get(x_167, 9);
lean_inc(x_179);
x_180 = lean_ctor_get(x_167, 10);
lean_inc(x_180);
x_181 = lean_ctor_get(x_167, 11);
lean_inc(x_181);
x_182 = lean_ctor_get(x_167, 12);
lean_inc(x_182);
x_183 = lean_ctor_get(x_167, 13);
lean_inc(x_183);
x_184 = lean_ctor_get(x_167, 14);
lean_inc(x_184);
x_185 = lean_ctor_get(x_167, 15);
lean_inc(x_185);
x_186 = lean_ctor_get(x_167, 16);
lean_inc(x_186);
x_187 = lean_ctor_get(x_167, 17);
lean_inc(x_187);
x_188 = lean_ctor_get(x_167, 18);
lean_inc(x_188);
x_189 = lean_ctor_get(x_167, 19);
lean_inc(x_189);
x_190 = lean_ctor_get(x_167, 20);
lean_inc(x_190);
x_191 = lean_ctor_get(x_167, 21);
lean_inc(x_191);
x_192 = lean_ctor_get(x_167, 22);
lean_inc(x_192);
x_193 = lean_ctor_get(x_167, 23);
lean_inc(x_193);
x_194 = lean_ctor_get(x_167, 24);
lean_inc(x_194);
x_195 = lean_ctor_get(x_167, 25);
lean_inc(x_195);
x_196 = lean_ctor_get(x_167, 26);
lean_inc(x_196);
x_197 = lean_ctor_get(x_167, 27);
lean_inc(x_197);
x_198 = lean_ctor_get(x_167, 28);
lean_inc(x_198);
x_199 = lean_ctor_get(x_167, 29);
lean_inc(x_199);
x_200 = lean_ctor_get(x_167, 30);
lean_inc(x_200);
x_201 = lean_ctor_get(x_167, 31);
lean_inc(x_201);
x_202 = lean_ctor_get(x_167, 32);
lean_inc(x_202);
x_203 = lean_ctor_get_uint8(x_167, sizeof(void*)*39);
x_204 = lean_ctor_get(x_167, 33);
lean_inc(x_204);
x_205 = lean_ctor_get(x_167, 34);
lean_inc(x_205);
x_206 = lean_ctor_get(x_167, 35);
lean_inc(x_206);
x_207 = lean_ctor_get(x_167, 36);
lean_inc(x_207);
x_208 = lean_ctor_get(x_167, 37);
lean_inc(x_208);
x_209 = lean_ctor_get(x_167, 38);
lean_inc(x_209);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 lean_ctor_release(x_167, 2);
 lean_ctor_release(x_167, 3);
 lean_ctor_release(x_167, 4);
 lean_ctor_release(x_167, 5);
 lean_ctor_release(x_167, 6);
 lean_ctor_release(x_167, 7);
 lean_ctor_release(x_167, 8);
 lean_ctor_release(x_167, 9);
 lean_ctor_release(x_167, 10);
 lean_ctor_release(x_167, 11);
 lean_ctor_release(x_167, 12);
 lean_ctor_release(x_167, 13);
 lean_ctor_release(x_167, 14);
 lean_ctor_release(x_167, 15);
 lean_ctor_release(x_167, 16);
 lean_ctor_release(x_167, 17);
 lean_ctor_release(x_167, 18);
 lean_ctor_release(x_167, 19);
 lean_ctor_release(x_167, 20);
 lean_ctor_release(x_167, 21);
 lean_ctor_release(x_167, 22);
 lean_ctor_release(x_167, 23);
 lean_ctor_release(x_167, 24);
 lean_ctor_release(x_167, 25);
 lean_ctor_release(x_167, 26);
 lean_ctor_release(x_167, 27);
 lean_ctor_release(x_167, 28);
 lean_ctor_release(x_167, 29);
 lean_ctor_release(x_167, 30);
 lean_ctor_release(x_167, 31);
 lean_ctor_release(x_167, 32);
 lean_ctor_release(x_167, 33);
 lean_ctor_release(x_167, 34);
 lean_ctor_release(x_167, 35);
 lean_ctor_release(x_167, 36);
 lean_ctor_release(x_167, 37);
 lean_ctor_release(x_167, 38);
 x_210 = x_167;
} else {
 lean_dec_ref(x_167);
 x_210 = lean_box(0);
}
lean_inc(x_3);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_3);
x_212 = l_Lean_PersistentArray_set___rarg(x_206, x_2, x_211);
lean_inc(x_2);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_207);
lean_ctor_set(x_15, 0, x_2);
if (lean_is_scalar(x_210)) {
 x_213 = lean_alloc_ctor(0, 39, 1);
} else {
 x_213 = x_210;
}
lean_ctor_set(x_213, 0, x_170);
lean_ctor_set(x_213, 1, x_171);
lean_ctor_set(x_213, 2, x_172);
lean_ctor_set(x_213, 3, x_173);
lean_ctor_set(x_213, 4, x_174);
lean_ctor_set(x_213, 5, x_175);
lean_ctor_set(x_213, 6, x_176);
lean_ctor_set(x_213, 7, x_177);
lean_ctor_set(x_213, 8, x_178);
lean_ctor_set(x_213, 9, x_179);
lean_ctor_set(x_213, 10, x_180);
lean_ctor_set(x_213, 11, x_181);
lean_ctor_set(x_213, 12, x_182);
lean_ctor_set(x_213, 13, x_183);
lean_ctor_set(x_213, 14, x_184);
lean_ctor_set(x_213, 15, x_185);
lean_ctor_set(x_213, 16, x_186);
lean_ctor_set(x_213, 17, x_187);
lean_ctor_set(x_213, 18, x_188);
lean_ctor_set(x_213, 19, x_189);
lean_ctor_set(x_213, 20, x_190);
lean_ctor_set(x_213, 21, x_191);
lean_ctor_set(x_213, 22, x_192);
lean_ctor_set(x_213, 23, x_193);
lean_ctor_set(x_213, 24, x_194);
lean_ctor_set(x_213, 25, x_195);
lean_ctor_set(x_213, 26, x_196);
lean_ctor_set(x_213, 27, x_197);
lean_ctor_set(x_213, 28, x_198);
lean_ctor_set(x_213, 29, x_199);
lean_ctor_set(x_213, 30, x_200);
lean_ctor_set(x_213, 31, x_201);
lean_ctor_set(x_213, 32, x_202);
lean_ctor_set(x_213, 33, x_204);
lean_ctor_set(x_213, 34, x_205);
lean_ctor_set(x_213, 35, x_212);
lean_ctor_set(x_213, 36, x_15);
lean_ctor_set(x_213, 37, x_208);
lean_ctor_set(x_213, 38, x_209);
lean_ctor_set_uint8(x_213, sizeof(void*)*39, x_203);
x_214 = lean_array_fset(x_169, x_5, x_213);
if (lean_is_scalar(x_159)) {
 x_215 = lean_alloc_ctor(0, 3, 0);
} else {
 x_215 = x_159;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_157);
lean_ctor_set(x_215, 2, x_158);
x_216 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_216, 0, x_153);
lean_ctor_set(x_216, 1, x_154);
lean_ctor_set(x_216, 2, x_155);
lean_ctor_set(x_216, 3, x_215);
lean_ctor_set(x_16, 14, x_216);
x_217 = lean_st_ref_set(x_6, x_16, x_20);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_219 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_218);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_220 = lean_ctor_get(x_16, 0);
x_221 = lean_ctor_get(x_16, 1);
x_222 = lean_ctor_get(x_16, 2);
x_223 = lean_ctor_get(x_16, 3);
x_224 = lean_ctor_get(x_16, 4);
x_225 = lean_ctor_get(x_16, 5);
x_226 = lean_ctor_get(x_16, 6);
x_227 = lean_ctor_get(x_16, 7);
x_228 = lean_ctor_get_uint8(x_16, sizeof(void*)*16);
x_229 = lean_ctor_get(x_16, 8);
x_230 = lean_ctor_get(x_16, 9);
x_231 = lean_ctor_get(x_16, 10);
x_232 = lean_ctor_get(x_16, 11);
x_233 = lean_ctor_get(x_16, 12);
x_234 = lean_ctor_get(x_16, 13);
x_235 = lean_ctor_get(x_16, 15);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_16);
x_236 = lean_ctor_get(x_17, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_17, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_17, 2);
lean_inc(x_238);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 x_239 = x_17;
} else {
 lean_dec_ref(x_17);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_18, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_18, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_18, 2);
lean_inc(x_242);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_243 = x_18;
} else {
 lean_dec_ref(x_18);
 x_243 = lean_box(0);
}
x_244 = lean_array_get_size(x_240);
x_245 = lean_nat_dec_lt(x_5, x_244);
lean_dec(x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_free_object(x_15);
if (lean_is_scalar(x_243)) {
 x_246 = lean_alloc_ctor(0, 3, 0);
} else {
 x_246 = x_243;
}
lean_ctor_set(x_246, 0, x_240);
lean_ctor_set(x_246, 1, x_241);
lean_ctor_set(x_246, 2, x_242);
if (lean_is_scalar(x_239)) {
 x_247 = lean_alloc_ctor(0, 4, 0);
} else {
 x_247 = x_239;
}
lean_ctor_set(x_247, 0, x_236);
lean_ctor_set(x_247, 1, x_237);
lean_ctor_set(x_247, 2, x_238);
lean_ctor_set(x_247, 3, x_246);
x_248 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_248, 0, x_220);
lean_ctor_set(x_248, 1, x_221);
lean_ctor_set(x_248, 2, x_222);
lean_ctor_set(x_248, 3, x_223);
lean_ctor_set(x_248, 4, x_224);
lean_ctor_set(x_248, 5, x_225);
lean_ctor_set(x_248, 6, x_226);
lean_ctor_set(x_248, 7, x_227);
lean_ctor_set(x_248, 8, x_229);
lean_ctor_set(x_248, 9, x_230);
lean_ctor_set(x_248, 10, x_231);
lean_ctor_set(x_248, 11, x_232);
lean_ctor_set(x_248, 12, x_233);
lean_ctor_set(x_248, 13, x_234);
lean_ctor_set(x_248, 14, x_247);
lean_ctor_set(x_248, 15, x_235);
lean_ctor_set_uint8(x_248, sizeof(void*)*16, x_228);
x_249 = lean_st_ref_set(x_6, x_248, x_20);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
lean_dec(x_249);
x_251 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_250);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_252 = lean_array_fget(x_240, x_5);
x_253 = lean_box(0);
x_254 = lean_array_fset(x_240, x_5, x_253);
x_255 = lean_ctor_get(x_252, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_252, 1);
lean_inc(x_256);
x_257 = lean_ctor_get(x_252, 2);
lean_inc(x_257);
x_258 = lean_ctor_get(x_252, 3);
lean_inc(x_258);
x_259 = lean_ctor_get(x_252, 4);
lean_inc(x_259);
x_260 = lean_ctor_get(x_252, 5);
lean_inc(x_260);
x_261 = lean_ctor_get(x_252, 6);
lean_inc(x_261);
x_262 = lean_ctor_get(x_252, 7);
lean_inc(x_262);
x_263 = lean_ctor_get(x_252, 8);
lean_inc(x_263);
x_264 = lean_ctor_get(x_252, 9);
lean_inc(x_264);
x_265 = lean_ctor_get(x_252, 10);
lean_inc(x_265);
x_266 = lean_ctor_get(x_252, 11);
lean_inc(x_266);
x_267 = lean_ctor_get(x_252, 12);
lean_inc(x_267);
x_268 = lean_ctor_get(x_252, 13);
lean_inc(x_268);
x_269 = lean_ctor_get(x_252, 14);
lean_inc(x_269);
x_270 = lean_ctor_get(x_252, 15);
lean_inc(x_270);
x_271 = lean_ctor_get(x_252, 16);
lean_inc(x_271);
x_272 = lean_ctor_get(x_252, 17);
lean_inc(x_272);
x_273 = lean_ctor_get(x_252, 18);
lean_inc(x_273);
x_274 = lean_ctor_get(x_252, 19);
lean_inc(x_274);
x_275 = lean_ctor_get(x_252, 20);
lean_inc(x_275);
x_276 = lean_ctor_get(x_252, 21);
lean_inc(x_276);
x_277 = lean_ctor_get(x_252, 22);
lean_inc(x_277);
x_278 = lean_ctor_get(x_252, 23);
lean_inc(x_278);
x_279 = lean_ctor_get(x_252, 24);
lean_inc(x_279);
x_280 = lean_ctor_get(x_252, 25);
lean_inc(x_280);
x_281 = lean_ctor_get(x_252, 26);
lean_inc(x_281);
x_282 = lean_ctor_get(x_252, 27);
lean_inc(x_282);
x_283 = lean_ctor_get(x_252, 28);
lean_inc(x_283);
x_284 = lean_ctor_get(x_252, 29);
lean_inc(x_284);
x_285 = lean_ctor_get(x_252, 30);
lean_inc(x_285);
x_286 = lean_ctor_get(x_252, 31);
lean_inc(x_286);
x_287 = lean_ctor_get(x_252, 32);
lean_inc(x_287);
x_288 = lean_ctor_get_uint8(x_252, sizeof(void*)*39);
x_289 = lean_ctor_get(x_252, 33);
lean_inc(x_289);
x_290 = lean_ctor_get(x_252, 34);
lean_inc(x_290);
x_291 = lean_ctor_get(x_252, 35);
lean_inc(x_291);
x_292 = lean_ctor_get(x_252, 36);
lean_inc(x_292);
x_293 = lean_ctor_get(x_252, 37);
lean_inc(x_293);
x_294 = lean_ctor_get(x_252, 38);
lean_inc(x_294);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 lean_ctor_release(x_252, 2);
 lean_ctor_release(x_252, 3);
 lean_ctor_release(x_252, 4);
 lean_ctor_release(x_252, 5);
 lean_ctor_release(x_252, 6);
 lean_ctor_release(x_252, 7);
 lean_ctor_release(x_252, 8);
 lean_ctor_release(x_252, 9);
 lean_ctor_release(x_252, 10);
 lean_ctor_release(x_252, 11);
 lean_ctor_release(x_252, 12);
 lean_ctor_release(x_252, 13);
 lean_ctor_release(x_252, 14);
 lean_ctor_release(x_252, 15);
 lean_ctor_release(x_252, 16);
 lean_ctor_release(x_252, 17);
 lean_ctor_release(x_252, 18);
 lean_ctor_release(x_252, 19);
 lean_ctor_release(x_252, 20);
 lean_ctor_release(x_252, 21);
 lean_ctor_release(x_252, 22);
 lean_ctor_release(x_252, 23);
 lean_ctor_release(x_252, 24);
 lean_ctor_release(x_252, 25);
 lean_ctor_release(x_252, 26);
 lean_ctor_release(x_252, 27);
 lean_ctor_release(x_252, 28);
 lean_ctor_release(x_252, 29);
 lean_ctor_release(x_252, 30);
 lean_ctor_release(x_252, 31);
 lean_ctor_release(x_252, 32);
 lean_ctor_release(x_252, 33);
 lean_ctor_release(x_252, 34);
 lean_ctor_release(x_252, 35);
 lean_ctor_release(x_252, 36);
 lean_ctor_release(x_252, 37);
 lean_ctor_release(x_252, 38);
 x_295 = x_252;
} else {
 lean_dec_ref(x_252);
 x_295 = lean_box(0);
}
lean_inc(x_3);
x_296 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_296, 0, x_3);
x_297 = l_Lean_PersistentArray_set___rarg(x_291, x_2, x_296);
lean_inc(x_2);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_292);
lean_ctor_set(x_15, 0, x_2);
if (lean_is_scalar(x_295)) {
 x_298 = lean_alloc_ctor(0, 39, 1);
} else {
 x_298 = x_295;
}
lean_ctor_set(x_298, 0, x_255);
lean_ctor_set(x_298, 1, x_256);
lean_ctor_set(x_298, 2, x_257);
lean_ctor_set(x_298, 3, x_258);
lean_ctor_set(x_298, 4, x_259);
lean_ctor_set(x_298, 5, x_260);
lean_ctor_set(x_298, 6, x_261);
lean_ctor_set(x_298, 7, x_262);
lean_ctor_set(x_298, 8, x_263);
lean_ctor_set(x_298, 9, x_264);
lean_ctor_set(x_298, 10, x_265);
lean_ctor_set(x_298, 11, x_266);
lean_ctor_set(x_298, 12, x_267);
lean_ctor_set(x_298, 13, x_268);
lean_ctor_set(x_298, 14, x_269);
lean_ctor_set(x_298, 15, x_270);
lean_ctor_set(x_298, 16, x_271);
lean_ctor_set(x_298, 17, x_272);
lean_ctor_set(x_298, 18, x_273);
lean_ctor_set(x_298, 19, x_274);
lean_ctor_set(x_298, 20, x_275);
lean_ctor_set(x_298, 21, x_276);
lean_ctor_set(x_298, 22, x_277);
lean_ctor_set(x_298, 23, x_278);
lean_ctor_set(x_298, 24, x_279);
lean_ctor_set(x_298, 25, x_280);
lean_ctor_set(x_298, 26, x_281);
lean_ctor_set(x_298, 27, x_282);
lean_ctor_set(x_298, 28, x_283);
lean_ctor_set(x_298, 29, x_284);
lean_ctor_set(x_298, 30, x_285);
lean_ctor_set(x_298, 31, x_286);
lean_ctor_set(x_298, 32, x_287);
lean_ctor_set(x_298, 33, x_289);
lean_ctor_set(x_298, 34, x_290);
lean_ctor_set(x_298, 35, x_297);
lean_ctor_set(x_298, 36, x_15);
lean_ctor_set(x_298, 37, x_293);
lean_ctor_set(x_298, 38, x_294);
lean_ctor_set_uint8(x_298, sizeof(void*)*39, x_288);
x_299 = lean_array_fset(x_254, x_5, x_298);
if (lean_is_scalar(x_243)) {
 x_300 = lean_alloc_ctor(0, 3, 0);
} else {
 x_300 = x_243;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_241);
lean_ctor_set(x_300, 2, x_242);
if (lean_is_scalar(x_239)) {
 x_301 = lean_alloc_ctor(0, 4, 0);
} else {
 x_301 = x_239;
}
lean_ctor_set(x_301, 0, x_236);
lean_ctor_set(x_301, 1, x_237);
lean_ctor_set(x_301, 2, x_238);
lean_ctor_set(x_301, 3, x_300);
x_302 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_302, 0, x_220);
lean_ctor_set(x_302, 1, x_221);
lean_ctor_set(x_302, 2, x_222);
lean_ctor_set(x_302, 3, x_223);
lean_ctor_set(x_302, 4, x_224);
lean_ctor_set(x_302, 5, x_225);
lean_ctor_set(x_302, 6, x_226);
lean_ctor_set(x_302, 7, x_227);
lean_ctor_set(x_302, 8, x_229);
lean_ctor_set(x_302, 9, x_230);
lean_ctor_set(x_302, 10, x_231);
lean_ctor_set(x_302, 11, x_232);
lean_ctor_set(x_302, 12, x_233);
lean_ctor_set(x_302, 13, x_234);
lean_ctor_set(x_302, 14, x_301);
lean_ctor_set(x_302, 15, x_235);
lean_ctor_set_uint8(x_302, sizeof(void*)*16, x_228);
x_303 = lean_st_ref_set(x_6, x_302, x_20);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
lean_dec(x_303);
x_305 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_304);
return x_305;
}
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_306 = lean_ctor_get(x_15, 1);
lean_inc(x_306);
lean_dec(x_15);
x_307 = lean_ctor_get(x_16, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_16, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_16, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_16, 3);
lean_inc(x_310);
x_311 = lean_ctor_get(x_16, 4);
lean_inc(x_311);
x_312 = lean_ctor_get(x_16, 5);
lean_inc(x_312);
x_313 = lean_ctor_get(x_16, 6);
lean_inc(x_313);
x_314 = lean_ctor_get(x_16, 7);
lean_inc(x_314);
x_315 = lean_ctor_get_uint8(x_16, sizeof(void*)*16);
x_316 = lean_ctor_get(x_16, 8);
lean_inc(x_316);
x_317 = lean_ctor_get(x_16, 9);
lean_inc(x_317);
x_318 = lean_ctor_get(x_16, 10);
lean_inc(x_318);
x_319 = lean_ctor_get(x_16, 11);
lean_inc(x_319);
x_320 = lean_ctor_get(x_16, 12);
lean_inc(x_320);
x_321 = lean_ctor_get(x_16, 13);
lean_inc(x_321);
x_322 = lean_ctor_get(x_16, 15);
lean_inc(x_322);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 lean_ctor_release(x_16, 6);
 lean_ctor_release(x_16, 7);
 lean_ctor_release(x_16, 8);
 lean_ctor_release(x_16, 9);
 lean_ctor_release(x_16, 10);
 lean_ctor_release(x_16, 11);
 lean_ctor_release(x_16, 12);
 lean_ctor_release(x_16, 13);
 lean_ctor_release(x_16, 14);
 lean_ctor_release(x_16, 15);
 x_323 = x_16;
} else {
 lean_dec_ref(x_16);
 x_323 = lean_box(0);
}
x_324 = lean_ctor_get(x_17, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_17, 1);
lean_inc(x_325);
x_326 = lean_ctor_get(x_17, 2);
lean_inc(x_326);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 x_327 = x_17;
} else {
 lean_dec_ref(x_17);
 x_327 = lean_box(0);
}
x_328 = lean_ctor_get(x_18, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_18, 1);
lean_inc(x_329);
x_330 = lean_ctor_get(x_18, 2);
lean_inc(x_330);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_331 = x_18;
} else {
 lean_dec_ref(x_18);
 x_331 = lean_box(0);
}
x_332 = lean_array_get_size(x_328);
x_333 = lean_nat_dec_lt(x_5, x_332);
lean_dec(x_332);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
if (lean_is_scalar(x_331)) {
 x_334 = lean_alloc_ctor(0, 3, 0);
} else {
 x_334 = x_331;
}
lean_ctor_set(x_334, 0, x_328);
lean_ctor_set(x_334, 1, x_329);
lean_ctor_set(x_334, 2, x_330);
if (lean_is_scalar(x_327)) {
 x_335 = lean_alloc_ctor(0, 4, 0);
} else {
 x_335 = x_327;
}
lean_ctor_set(x_335, 0, x_324);
lean_ctor_set(x_335, 1, x_325);
lean_ctor_set(x_335, 2, x_326);
lean_ctor_set(x_335, 3, x_334);
if (lean_is_scalar(x_323)) {
 x_336 = lean_alloc_ctor(0, 16, 1);
} else {
 x_336 = x_323;
}
lean_ctor_set(x_336, 0, x_307);
lean_ctor_set(x_336, 1, x_308);
lean_ctor_set(x_336, 2, x_309);
lean_ctor_set(x_336, 3, x_310);
lean_ctor_set(x_336, 4, x_311);
lean_ctor_set(x_336, 5, x_312);
lean_ctor_set(x_336, 6, x_313);
lean_ctor_set(x_336, 7, x_314);
lean_ctor_set(x_336, 8, x_316);
lean_ctor_set(x_336, 9, x_317);
lean_ctor_set(x_336, 10, x_318);
lean_ctor_set(x_336, 11, x_319);
lean_ctor_set(x_336, 12, x_320);
lean_ctor_set(x_336, 13, x_321);
lean_ctor_set(x_336, 14, x_335);
lean_ctor_set(x_336, 15, x_322);
lean_ctor_set_uint8(x_336, sizeof(void*)*16, x_315);
x_337 = lean_st_ref_set(x_6, x_336, x_306);
x_338 = lean_ctor_get(x_337, 1);
lean_inc(x_338);
lean_dec(x_337);
x_339 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_338);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_340 = lean_array_fget(x_328, x_5);
x_341 = lean_box(0);
x_342 = lean_array_fset(x_328, x_5, x_341);
x_343 = lean_ctor_get(x_340, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_340, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_340, 2);
lean_inc(x_345);
x_346 = lean_ctor_get(x_340, 3);
lean_inc(x_346);
x_347 = lean_ctor_get(x_340, 4);
lean_inc(x_347);
x_348 = lean_ctor_get(x_340, 5);
lean_inc(x_348);
x_349 = lean_ctor_get(x_340, 6);
lean_inc(x_349);
x_350 = lean_ctor_get(x_340, 7);
lean_inc(x_350);
x_351 = lean_ctor_get(x_340, 8);
lean_inc(x_351);
x_352 = lean_ctor_get(x_340, 9);
lean_inc(x_352);
x_353 = lean_ctor_get(x_340, 10);
lean_inc(x_353);
x_354 = lean_ctor_get(x_340, 11);
lean_inc(x_354);
x_355 = lean_ctor_get(x_340, 12);
lean_inc(x_355);
x_356 = lean_ctor_get(x_340, 13);
lean_inc(x_356);
x_357 = lean_ctor_get(x_340, 14);
lean_inc(x_357);
x_358 = lean_ctor_get(x_340, 15);
lean_inc(x_358);
x_359 = lean_ctor_get(x_340, 16);
lean_inc(x_359);
x_360 = lean_ctor_get(x_340, 17);
lean_inc(x_360);
x_361 = lean_ctor_get(x_340, 18);
lean_inc(x_361);
x_362 = lean_ctor_get(x_340, 19);
lean_inc(x_362);
x_363 = lean_ctor_get(x_340, 20);
lean_inc(x_363);
x_364 = lean_ctor_get(x_340, 21);
lean_inc(x_364);
x_365 = lean_ctor_get(x_340, 22);
lean_inc(x_365);
x_366 = lean_ctor_get(x_340, 23);
lean_inc(x_366);
x_367 = lean_ctor_get(x_340, 24);
lean_inc(x_367);
x_368 = lean_ctor_get(x_340, 25);
lean_inc(x_368);
x_369 = lean_ctor_get(x_340, 26);
lean_inc(x_369);
x_370 = lean_ctor_get(x_340, 27);
lean_inc(x_370);
x_371 = lean_ctor_get(x_340, 28);
lean_inc(x_371);
x_372 = lean_ctor_get(x_340, 29);
lean_inc(x_372);
x_373 = lean_ctor_get(x_340, 30);
lean_inc(x_373);
x_374 = lean_ctor_get(x_340, 31);
lean_inc(x_374);
x_375 = lean_ctor_get(x_340, 32);
lean_inc(x_375);
x_376 = lean_ctor_get_uint8(x_340, sizeof(void*)*39);
x_377 = lean_ctor_get(x_340, 33);
lean_inc(x_377);
x_378 = lean_ctor_get(x_340, 34);
lean_inc(x_378);
x_379 = lean_ctor_get(x_340, 35);
lean_inc(x_379);
x_380 = lean_ctor_get(x_340, 36);
lean_inc(x_380);
x_381 = lean_ctor_get(x_340, 37);
lean_inc(x_381);
x_382 = lean_ctor_get(x_340, 38);
lean_inc(x_382);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 lean_ctor_release(x_340, 4);
 lean_ctor_release(x_340, 5);
 lean_ctor_release(x_340, 6);
 lean_ctor_release(x_340, 7);
 lean_ctor_release(x_340, 8);
 lean_ctor_release(x_340, 9);
 lean_ctor_release(x_340, 10);
 lean_ctor_release(x_340, 11);
 lean_ctor_release(x_340, 12);
 lean_ctor_release(x_340, 13);
 lean_ctor_release(x_340, 14);
 lean_ctor_release(x_340, 15);
 lean_ctor_release(x_340, 16);
 lean_ctor_release(x_340, 17);
 lean_ctor_release(x_340, 18);
 lean_ctor_release(x_340, 19);
 lean_ctor_release(x_340, 20);
 lean_ctor_release(x_340, 21);
 lean_ctor_release(x_340, 22);
 lean_ctor_release(x_340, 23);
 lean_ctor_release(x_340, 24);
 lean_ctor_release(x_340, 25);
 lean_ctor_release(x_340, 26);
 lean_ctor_release(x_340, 27);
 lean_ctor_release(x_340, 28);
 lean_ctor_release(x_340, 29);
 lean_ctor_release(x_340, 30);
 lean_ctor_release(x_340, 31);
 lean_ctor_release(x_340, 32);
 lean_ctor_release(x_340, 33);
 lean_ctor_release(x_340, 34);
 lean_ctor_release(x_340, 35);
 lean_ctor_release(x_340, 36);
 lean_ctor_release(x_340, 37);
 lean_ctor_release(x_340, 38);
 x_383 = x_340;
} else {
 lean_dec_ref(x_340);
 x_383 = lean_box(0);
}
lean_inc(x_3);
x_384 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_384, 0, x_3);
x_385 = l_Lean_PersistentArray_set___rarg(x_379, x_2, x_384);
lean_inc(x_2);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_2);
lean_ctor_set(x_386, 1, x_380);
if (lean_is_scalar(x_383)) {
 x_387 = lean_alloc_ctor(0, 39, 1);
} else {
 x_387 = x_383;
}
lean_ctor_set(x_387, 0, x_343);
lean_ctor_set(x_387, 1, x_344);
lean_ctor_set(x_387, 2, x_345);
lean_ctor_set(x_387, 3, x_346);
lean_ctor_set(x_387, 4, x_347);
lean_ctor_set(x_387, 5, x_348);
lean_ctor_set(x_387, 6, x_349);
lean_ctor_set(x_387, 7, x_350);
lean_ctor_set(x_387, 8, x_351);
lean_ctor_set(x_387, 9, x_352);
lean_ctor_set(x_387, 10, x_353);
lean_ctor_set(x_387, 11, x_354);
lean_ctor_set(x_387, 12, x_355);
lean_ctor_set(x_387, 13, x_356);
lean_ctor_set(x_387, 14, x_357);
lean_ctor_set(x_387, 15, x_358);
lean_ctor_set(x_387, 16, x_359);
lean_ctor_set(x_387, 17, x_360);
lean_ctor_set(x_387, 18, x_361);
lean_ctor_set(x_387, 19, x_362);
lean_ctor_set(x_387, 20, x_363);
lean_ctor_set(x_387, 21, x_364);
lean_ctor_set(x_387, 22, x_365);
lean_ctor_set(x_387, 23, x_366);
lean_ctor_set(x_387, 24, x_367);
lean_ctor_set(x_387, 25, x_368);
lean_ctor_set(x_387, 26, x_369);
lean_ctor_set(x_387, 27, x_370);
lean_ctor_set(x_387, 28, x_371);
lean_ctor_set(x_387, 29, x_372);
lean_ctor_set(x_387, 30, x_373);
lean_ctor_set(x_387, 31, x_374);
lean_ctor_set(x_387, 32, x_375);
lean_ctor_set(x_387, 33, x_377);
lean_ctor_set(x_387, 34, x_378);
lean_ctor_set(x_387, 35, x_385);
lean_ctor_set(x_387, 36, x_386);
lean_ctor_set(x_387, 37, x_381);
lean_ctor_set(x_387, 38, x_382);
lean_ctor_set_uint8(x_387, sizeof(void*)*39, x_376);
x_388 = lean_array_fset(x_342, x_5, x_387);
if (lean_is_scalar(x_331)) {
 x_389 = lean_alloc_ctor(0, 3, 0);
} else {
 x_389 = x_331;
}
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_329);
lean_ctor_set(x_389, 2, x_330);
if (lean_is_scalar(x_327)) {
 x_390 = lean_alloc_ctor(0, 4, 0);
} else {
 x_390 = x_327;
}
lean_ctor_set(x_390, 0, x_324);
lean_ctor_set(x_390, 1, x_325);
lean_ctor_set(x_390, 2, x_326);
lean_ctor_set(x_390, 3, x_389);
if (lean_is_scalar(x_323)) {
 x_391 = lean_alloc_ctor(0, 16, 1);
} else {
 x_391 = x_323;
}
lean_ctor_set(x_391, 0, x_307);
lean_ctor_set(x_391, 1, x_308);
lean_ctor_set(x_391, 2, x_309);
lean_ctor_set(x_391, 3, x_310);
lean_ctor_set(x_391, 4, x_311);
lean_ctor_set(x_391, 5, x_312);
lean_ctor_set(x_391, 6, x_313);
lean_ctor_set(x_391, 7, x_314);
lean_ctor_set(x_391, 8, x_316);
lean_ctor_set(x_391, 9, x_317);
lean_ctor_set(x_391, 10, x_318);
lean_ctor_set(x_391, 11, x_319);
lean_ctor_set(x_391, 12, x_320);
lean_ctor_set(x_391, 13, x_321);
lean_ctor_set(x_391, 14, x_390);
lean_ctor_set(x_391, 15, x_322);
lean_ctor_set_uint8(x_391, sizeof(void*)*16, x_315);
x_392 = lean_st_ref_set(x_6, x_391, x_306);
x_393 = lean_ctor_get(x_392, 1);
lean_inc(x_393);
lean_dec(x_392);
x_394 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_393);
return x_394;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__4;
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__1(x_1, x_2, x_3, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_19);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 1);
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_MessageData_ofExpr(x_26);
x_29 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_29);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_15, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_27);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__1(x_1, x_2, x_3, x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
lean_dec(x_32);
return x_34;
}
else
{
uint8_t x_35; 
lean_free_object(x_16);
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
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_dec(x_16);
x_40 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_MessageData_ofExpr(x_41);
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_15, x_46, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_42);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__1(x_1, x_2, x_3, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_49);
lean_dec(x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
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
x_51 = lean_ctor_get(x_40, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_53 = x_40;
} else {
 lean_dec_ref(x_40);
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
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(">> ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_24 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_15);
lean_free_object(x_14);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__2(x_18, x_21, x_22, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 1);
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_33 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_MessageData_ofExpr(x_34);
x_40 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__2;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_39);
lean_ctor_set(x_24, 0, x_40);
x_41 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_41);
lean_ctor_set(x_15, 0, x_24);
x_42 = l_Lean_MessageData_ofExpr(x_37);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_42);
lean_ctor_set(x_14, 0, x_15);
x_43 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_23, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__2(x_18, x_21, x_22, x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_47);
lean_dec(x_46);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_34);
lean_free_object(x_24);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_36);
if (x_49 == 0)
{
return x_36;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_36);
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
lean_free_object(x_24);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_33);
if (x_53 == 0)
{
return x_33;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_33, 0);
x_55 = lean_ctor_get(x_33, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_33);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_24, 1);
lean_inc(x_57);
lean_dec(x_24);
x_58 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_MessageData_ofExpr(x_59);
x_65 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__2;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_67);
lean_ctor_set(x_15, 0, x_66);
x_68 = l_Lean_MessageData_ofExpr(x_62);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_68);
lean_ctor_set(x_14, 0, x_15);
x_69 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_14);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_23, x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_63);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__2(x_18, x_21, x_22, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_73);
lean_dec(x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_59);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_75 = lean_ctor_get(x_61, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_61, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_77 = x_61;
} else {
 lean_dec_ref(x_61);
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
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_79 = lean_ctor_get(x_58, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_58, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_81 = x_58;
} else {
 lean_dec_ref(x_58);
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
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_15, 0);
x_84 = lean_ctor_get(x_15, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_15);
x_85 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_86 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_85, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_14);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_box(0);
x_91 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__2(x_18, x_83, x_84, x_90, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_86, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_93 = x_86;
} else {
 lean_dec_ref(x_86);
 x_93 = lean_box(0);
}
x_94 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_92);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_MessageData_ofExpr(x_95);
x_101 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__2;
if (lean_is_scalar(x_93)) {
 x_102 = lean_alloc_ctor(7, 2, 0);
} else {
 x_102 = x_93;
 lean_ctor_set_tag(x_102, 7);
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_MessageData_ofExpr(x_98);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_105);
lean_ctor_set(x_14, 0, x_104);
x_106 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_14);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_85, x_107, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_99);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__2(x_18, x_83, x_84, x_109, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_110);
lean_dec(x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_84);
lean_dec(x_83);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = lean_ctor_get(x_97, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_114 = x_97;
} else {
 lean_dec_ref(x_97);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_93);
lean_dec(x_84);
lean_dec(x_83);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_116 = lean_ctor_get(x_94, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_94, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_118 = x_94;
} else {
 lean_dec_ref(x_94);
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
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_120 = lean_ctor_get(x_14, 0);
lean_inc(x_120);
lean_dec(x_14);
x_121 = lean_ctor_get(x_15, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_15, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_123 = x_15;
} else {
 lean_dec_ref(x_15);
 x_123 = lean_box(0);
}
x_124 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5;
x_125 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_124, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_123);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = lean_box(0);
x_130 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__2(x_120, x_121, x_122, x_129, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_128);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_132 = x_125;
} else {
 lean_dec_ref(x_125);
 x_132 = lean_box(0);
}
x_133 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_121, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_122, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_Lean_MessageData_ofExpr(x_134);
x_140 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__2;
if (lean_is_scalar(x_132)) {
 x_141 = lean_alloc_ctor(7, 2, 0);
} else {
 x_141 = x_132;
 lean_ctor_set_tag(x_141, 7);
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
if (lean_is_scalar(x_123)) {
 x_143 = lean_alloc_ctor(7, 2, 0);
} else {
 x_143 = x_123;
 lean_ctor_set_tag(x_143, 7);
}
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_MessageData_ofExpr(x_137);
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_124, x_147, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_138);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__2(x_120, x_121, x_122, x_149, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_150);
lean_dec(x_149);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_152 = lean_ctor_get(x_136, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_136, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_154 = x_136;
} else {
 lean_dec_ref(x_136);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_132);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_156 = lean_ctor_get(x_133, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_133, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_158 = x_133;
} else {
 lean_dec_ref(x_133);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_160 = !lean_is_exclusive(x_13);
if (x_160 == 0)
{
return x_13;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_13, 0);
x_162 = lean_ctor_get(x_13, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_13);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3;
x_3 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__4___boxed), 11, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_10);
x_13 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_box(0);
x_18 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_506_(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3(x_14, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__2;
x_22 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__3;
x_27 = lean_unbox(x_24);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_22);
lean_dec(x_14);
x_28 = lean_box(0);
x_29 = lean_apply_11(x_26, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
lean_dec(x_14);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_MessageData_ofExpr(x_31);
x_34 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_33);
lean_ctor_set(x_22, 0, x_34);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_21, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_apply_11(x_26, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
return x_39;
}
else
{
uint8_t x_40; 
lean_free_object(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_30);
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_22, 0);
x_45 = lean_ctor_get(x_22, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_22);
x_46 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__3;
x_47 = lean_unbox(x_44);
lean_dec(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_14);
x_48 = lean_box(0);
x_49 = lean_apply_11(x_46, x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
lean_dec(x_14);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_MessageData_ofExpr(x_51);
x_54 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_21, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_52);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_apply_11(x_46, x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = lean_ctor_get(x_50, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_63 = x_50;
} else {
 lean_dec_ref(x_50);
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
}
else
{
uint8_t x_65; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
return x_13;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_13, 0);
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_13);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1;
x_13 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_MessageData_ofExpr(x_23);
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_25);
lean_ctor_set(x_13, 0, x_26);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_12, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5(x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_29);
return x_31;
}
else
{
uint8_t x_32; 
lean_free_object(x_13);
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
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_dec(x_13);
x_37 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_MessageData_ofExpr(x_38);
x_41 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_12, x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5(x_1, x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
lean_dec(x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
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
x_48 = lean_ctor_get(x_37, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_50 = x_37;
} else {
 lean_dec_ref(x_37);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___closed__2;
x_14 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l_Lean_MessageData_ofExpr(x_1);
x_25 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_MessageData_ofExpr(x_2);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
x_32 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_13, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
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
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
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
lean_dec(x_25);
lean_inc(x_35);
lean_inc(x_23);
x_36 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Grind_Linarith_Expr_norm(x_36);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_506_(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_free_object(x_24);
x_40 = lean_box(0);
x_41 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___lambda__1(x_1, x_2, x_23, x_35, x_37, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_33);
return x_41;
}
else
{
lean_object* x_42; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_11);
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
x_42 = lean_box(0);
lean_ctor_set(x_24, 0, x_42);
return x_24;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_24, 1);
lean_inc(x_43);
lean_dec(x_24);
x_44 = lean_ctor_get(x_25, 0);
lean_inc(x_44);
lean_dec(x_25);
lean_inc(x_44);
lean_inc(x_23);
x_45 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_45, 0, x_23);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Grind_Linarith_Expr_norm(x_45);
lean_dec(x_45);
x_47 = lean_box(0);
x_48 = l_Lean_Grind_Linarith_beqPoly____x40_Init_Grind_Ordered_Linarith___hyg_506_(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___lambda__1(x_1, x_2, x_23, x_44, x_46, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_23);
lean_dec(x_11);
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
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_23);
lean_dec(x_11);
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
x_53 = !lean_is_exclusive(x_24);
if (x_53 == 0)
{
return x_24;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_24, 0);
x_55 = lean_ctor_get(x_24, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_24);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_11);
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
x_57 = !lean_is_exclusive(x_14);
if (x_57 == 0)
{
return x_14;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_14, 0);
x_59 = lean_ctor_get(x_14, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_14);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEqImpl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_isCommRing(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEqImpl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_Meta_Grind_Arith_Linear_isOrdered(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Meta_Grind_Arith_Linear_isCommRing(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(x_1, x_2, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(x_1, x_2, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_22);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_dec(x_23);
x_39 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1;
x_40 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__1(x_39, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_box(0);
x_45 = l_Lean_Meta_Grind_Arith_Linear_processNewEqImpl___lambda__1(x_1, x_2, x_44, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_40, 1);
x_48 = lean_ctor_get(x_40, 0);
lean_dec(x_48);
x_49 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_51 = l_Lean_Meta_mkEq(x_1, x_2, x_8, x_9, x_10, x_11, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_MessageData_ofExpr(x_52);
x_55 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_54);
lean_ctor_set(x_40, 0, x_55);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_40);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_39, x_56, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_53);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Meta_Grind_Arith_Linear_processNewEqImpl___lambda__1(x_1, x_2, x_58, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_59);
lean_dec(x_58);
return x_60;
}
else
{
uint8_t x_61; 
lean_free_object(x_40);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_51);
if (x_61 == 0)
{
return x_51;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_51, 0);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_51);
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
lean_free_object(x_40);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_49);
if (x_65 == 0)
{
return x_49;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_49, 0);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_49);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_40, 1);
lean_inc(x_69);
lean_dec(x_40);
x_70 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_72 = l_Lean_Meta_mkEq(x_1, x_2, x_8, x_9, x_10, x_11, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_MessageData_ofExpr(x_73);
x_76 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert___spec__9(x_39, x_78, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_74);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Meta_Grind_Arith_Linear_processNewEqImpl___lambda__1(x_1, x_2, x_80, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_81);
lean_dec(x_80);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_ctor_get(x_72, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_72, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_85 = x_72;
} else {
 lean_dec_ref(x_72);
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
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_87 = lean_ctor_get(x_70, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_70, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_89 = x_70;
} else {
 lean_dec_ref(x_70);
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
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_23);
if (x_91 == 0)
{
return x_23;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_23, 0);
x_93 = lean_ctor_get(x_23, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_23);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_process_linarith_eq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_1, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Grind_Arith_Linear_processNewEqImpl___lambda__2(x_1, x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
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
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEqImpl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_processNewEqImpl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEqImpl___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_processNewEqImpl___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = lean_box(x_13);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 12, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Meta_Grind_Arith_Linear_withRingM___rarg(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_11);
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
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_box(x_13);
lean_inc(x_2);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 12, 2);
lean_closure_set(x_27, 0, x_2);
lean_closure_set(x_27, 1, x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Meta_Grind_Arith_Linear_withRingM___rarg(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_25);
lean_dec(x_11);
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
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = l_Lean_Meta_Grind_getGeneration(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_36);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = l_Lean_Meta_Grind_getGeneration(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_41);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_nat_dec_le(x_40, x_44);
lean_inc(x_37);
lean_inc(x_25);
lean_ctor_set_tag(x_42, 4);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set(x_42, 0, x_25);
x_47 = l_Lean_Grind_CommRing_Expr_toPoly(x_42);
if (x_46 == 0)
{
lean_object* x_48; 
lean_dec(x_44);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_47);
x_48 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_47, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
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
lean_dec(x_47);
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
lean_dec(x_51);
x_60 = lean_ctor_get(x_52, 0);
lean_inc(x_60);
lean_dec(x_52);
x_61 = l_Lean_Grind_Linarith_Expr_norm(x_60);
x_62 = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_2);
lean_ctor_set(x_62, 2, x_25);
lean_ctor_set(x_62, 3, x_37);
lean_ctor_set(x_62, 4, x_47);
lean_ctor_set(x_62, 5, x_60);
lean_ctor_set(x_38, 1, x_62);
lean_ctor_set(x_38, 0, x_61);
x_63 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_59);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_47);
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_64 = !lean_is_exclusive(x_51);
if (x_64 == 0)
{
return x_51;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_51, 0);
x_66 = lean_ctor_get(x_51, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_51);
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
lean_dec(x_47);
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_68 = !lean_is_exclusive(x_48);
if (x_68 == 0)
{
return x_48;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_48, 0);
x_70 = lean_ctor_get(x_48, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_48);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; 
lean_dec(x_40);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_47);
x_72 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_47, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
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
lean_dec(x_47);
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_75, 1);
lean_inc(x_83);
lean_dec(x_75);
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
lean_dec(x_76);
x_85 = l_Lean_Grind_Linarith_Expr_norm(x_84);
x_86 = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_2);
lean_ctor_set(x_86, 2, x_25);
lean_ctor_set(x_86, 3, x_37);
lean_ctor_set(x_86, 4, x_47);
lean_ctor_set(x_86, 5, x_84);
lean_ctor_set(x_38, 1, x_86);
lean_ctor_set(x_38, 0, x_85);
x_87 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_83);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_47);
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_88 = !lean_is_exclusive(x_75);
if (x_88 == 0)
{
return x_75;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_75, 0);
x_90 = lean_ctor_get(x_75, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_75);
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
lean_dec(x_47);
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_92 = !lean_is_exclusive(x_72);
if (x_92 == 0)
{
return x_72;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_72, 0);
x_94 = lean_ctor_get(x_72, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_72);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_42, 0);
x_97 = lean_ctor_get(x_42, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_42);
x_98 = lean_nat_dec_le(x_40, x_96);
lean_inc(x_37);
lean_inc(x_25);
x_99 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_99, 0, x_25);
lean_ctor_set(x_99, 1, x_37);
x_100 = l_Lean_Grind_CommRing_Expr_toPoly(x_99);
if (x_98 == 0)
{
lean_object* x_101; 
lean_dec(x_96);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_100);
x_101 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_100, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_97);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_104 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_102, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_100);
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = lean_box(0);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
lean_dec(x_104);
x_111 = lean_ctor_get(x_105, 0);
lean_inc(x_111);
lean_dec(x_105);
x_112 = l_Lean_Grind_Linarith_Expr_norm(x_111);
x_113 = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_2);
lean_ctor_set(x_113, 2, x_25);
lean_ctor_set(x_113, 3, x_37);
lean_ctor_set(x_113, 4, x_100);
lean_ctor_set(x_113, 5, x_111);
lean_ctor_set(x_38, 1, x_113);
lean_ctor_set(x_38, 0, x_112);
x_114 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_110);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_100);
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_115 = lean_ctor_get(x_104, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_104, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_117 = x_104;
} else {
 lean_dec_ref(x_104);
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
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_100);
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_119 = lean_ctor_get(x_101, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_101, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_121 = x_101;
} else {
 lean_dec_ref(x_101);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
lean_object* x_123; 
lean_dec(x_40);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_100);
x_123 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_100, x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_97);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_126 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_124, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_100);
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
x_130 = lean_box(0);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_128);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_126, 1);
lean_inc(x_132);
lean_dec(x_126);
x_133 = lean_ctor_get(x_127, 0);
lean_inc(x_133);
lean_dec(x_127);
x_134 = l_Lean_Grind_Linarith_Expr_norm(x_133);
x_135 = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(x_135, 0, x_1);
lean_ctor_set(x_135, 1, x_2);
lean_ctor_set(x_135, 2, x_25);
lean_ctor_set(x_135, 3, x_37);
lean_ctor_set(x_135, 4, x_100);
lean_ctor_set(x_135, 5, x_133);
lean_ctor_set(x_38, 1, x_135);
lean_ctor_set(x_38, 0, x_134);
x_136 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_132);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_100);
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_137 = lean_ctor_get(x_126, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_126, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_139 = x_126;
} else {
 lean_dec_ref(x_126);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_100);
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_141 = lean_ctor_get(x_123, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_123, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_143 = x_123;
} else {
 lean_dec_ref(x_123);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
x_145 = lean_ctor_get(x_38, 0);
x_146 = lean_ctor_get(x_38, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_38);
x_147 = l_Lean_Meta_Grind_getGeneration(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = lean_nat_dec_le(x_145, x_148);
lean_inc(x_37);
lean_inc(x_25);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(4, 2, 0);
} else {
 x_152 = x_150;
 lean_ctor_set_tag(x_152, 4);
}
lean_ctor_set(x_152, 0, x_25);
lean_ctor_set(x_152, 1, x_37);
x_153 = l_Lean_Grind_CommRing_Expr_toPoly(x_152);
if (x_151 == 0)
{
lean_object* x_154; 
lean_dec(x_148);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_153);
x_154 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_153, x_145, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_149);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_157 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_155, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_153);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = lean_box(0);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_159);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_157, 1);
lean_inc(x_163);
lean_dec(x_157);
x_164 = lean_ctor_get(x_158, 0);
lean_inc(x_164);
lean_dec(x_158);
x_165 = l_Lean_Grind_Linarith_Expr_norm(x_164);
x_166 = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(x_166, 0, x_1);
lean_ctor_set(x_166, 1, x_2);
lean_ctor_set(x_166, 2, x_25);
lean_ctor_set(x_166, 3, x_37);
lean_ctor_set(x_166, 4, x_153);
lean_ctor_set(x_166, 5, x_164);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_167, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_163);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_153);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_169 = lean_ctor_get(x_157, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_157, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_171 = x_157;
} else {
 lean_dec_ref(x_157);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_153);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_173 = lean_ctor_get(x_154, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_154, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_175 = x_154;
} else {
 lean_dec_ref(x_154);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
lean_object* x_177; 
lean_dec(x_145);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_153);
x_177 = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(x_153, x_148, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_149);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_180 = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(x_178, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_153);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
x_184 = lean_box(0);
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_183;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_182);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_186 = lean_ctor_get(x_180, 1);
lean_inc(x_186);
lean_dec(x_180);
x_187 = lean_ctor_get(x_181, 0);
lean_inc(x_187);
lean_dec(x_181);
x_188 = l_Lean_Grind_Linarith_Expr_norm(x_187);
x_189 = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(x_189, 0, x_1);
lean_ctor_set(x_189, 1, x_2);
lean_ctor_set(x_189, 2, x_25);
lean_ctor_set(x_189, 3, x_37);
lean_ctor_set(x_189, 4, x_153);
lean_ctor_set(x_189, 5, x_187);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(x_190, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_186);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_153);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_192 = lean_ctor_get(x_180, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_180, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_194 = x_180;
} else {
 lean_dec_ref(x_180);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_153);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
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
x_196 = lean_ctor_get(x_177, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_177, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_198 = x_177;
} else {
 lean_dec_ref(x_177);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
}
}
}
else
{
uint8_t x_200; 
lean_dec(x_25);
lean_dec(x_11);
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
x_200 = !lean_is_exclusive(x_28);
if (x_200 == 0)
{
return x_28;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_28, 0);
x_202 = lean_ctor_get(x_28, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_28);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_11);
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
x_204 = !lean_is_exclusive(x_16);
if (x_204 == 0)
{
return x_16;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_16, 0);
x_206 = lean_ctor_get(x_16, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_16);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
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
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
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
lean_dec(x_24);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
lean_inc(x_33);
lean_inc(x_23);
x_34 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Grind_Linarith_Expr_norm(x_34);
lean_dec(x_34);
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
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
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
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
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
lean_dec(x_22);
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(x_1, x_2, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(x_1, x_2, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_21);
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
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___spec__2___closed__2);
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
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__10);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__11);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___lambda__1___closed__2);
l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__1 = _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__1);
l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__2 = _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__2);
l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__3 = _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__3);
l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__4 = _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__4();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__4);
l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__5 = _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__5();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__5);
l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__6 = _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__6();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__6);
l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__7 = _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__7();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__7);
l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__8 = _init_l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__8();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___spec__1___closed__8);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__1);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__2);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__3);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__4 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___lambda__2___closed__4);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__2);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__3);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__4);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__5);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___spec__1___closed__6);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___spec__1___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___closed__1);
l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__1 = _init_l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__1);
l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__2 = _init_l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__2);
l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__3 = _init_l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__3);
l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__4 = _init_l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__4);
l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__5 = _init_l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_split___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___spec__1___closed__5);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lambda__1___closed__1);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__1);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__1);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__2);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__3);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__4 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lambda__3___closed__4);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___spec__1___closed__1);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__1);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__3___closed__2);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__1);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__2);
l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lambda__5___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

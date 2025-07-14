// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr
// Imports: Lean.Meta.Tactic.Simp.Arith.Int Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_addConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isNegEq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__0;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__2;
lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__3;
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__7;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__1;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2;
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__1;
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__7___boxed(lean_object**);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__8;
lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__0;
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___boxed(lean_object**);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Int_Linear_Poly_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5;
uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstLEInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNegEq___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Int_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0;
uint8_t l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(uint8_t, uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__2;
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_632_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0;
lean_object* lean_int_neg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__6;
lean_object* l_Int_OfNat_toIntLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = l_Int_Linear_Poly_isSorted(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Int_Linear_Poly_norm(x_12);
x_15 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_15, 0, x_1);
lean_inc(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_16;
x_3 = x_14;
goto block_11;
}
else
{
x_2 = x_1;
x_3 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Int_Linear_Poly_gcdCoeffs_x27(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_nat_to_int(x_4);
x_8 = l_Int_Linear_Poly_div(x_7, x_3);
lean_dec(x_7);
x_9 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cutsat", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_ctor_get(x_3, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_5, 0);
lean_inc(x_117);
x_118 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__8;
x_119 = lean_int_dec_le(x_118, x_1);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = l_Int_Linear_Poly_mul(x_116, x_4);
x_121 = lean_int_neg(x_1);
x_122 = l_Int_Linear_Poly_mul(x_117, x_121);
lean_dec(x_121);
x_123 = l_Int_Linear_Poly_combine(x_120, x_122);
x_18 = x_123;
goto block_115;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = l_Int_Linear_Poly_mul(x_117, x_1);
x_125 = lean_int_neg(x_4);
x_126 = l_Int_Linear_Poly_mul(x_116, x_125);
lean_dec(x_125);
x_127 = l_Int_Linear_Poly_combine(x_124, x_126);
x_18 = x_127;
goto block_115;
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
block_115:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__3;
x_20 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_19, x_9, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_12 = x_18;
x_13 = x_23;
goto block_17;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_20, 1);
x_26 = lean_ctor_get(x_20, 0);
lean_dec(x_26);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(x_2, x_6, x_25);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_3);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_3, x_6, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_5);
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_5, x_6, x_34);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_40 = l_Lean_MessageData_ofExpr(x_29);
lean_ctor_set_tag(x_35, 7);
lean_ctor_set(x_35, 1, x_40);
lean_ctor_set(x_35, 0, x_39);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__7;
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_41);
lean_ctor_set(x_31, 0, x_35);
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_33);
lean_ctor_set(x_27, 0, x_31);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_41);
lean_ctor_set(x_20, 0, x_27);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_20);
lean_ctor_set(x_42, 1, x_37);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
x_44 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_19, x_43, x_7, x_8, x_9, x_10, x_38);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_12 = x_18;
x_13 = x_45;
goto block_17;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_35, 0);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_35);
x_48 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_49 = l_Lean_MessageData_ofExpr(x_29);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__7;
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_51);
lean_ctor_set(x_31, 0, x_50);
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_33);
lean_ctor_set(x_27, 0, x_31);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_51);
lean_ctor_set(x_20, 0, x_27);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_20);
lean_ctor_set(x_52, 1, x_46);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
x_54 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_19, x_53, x_7, x_8, x_9, x_10, x_47);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_12 = x_18;
x_13 = x_55;
goto block_17;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_56 = lean_ctor_get(x_31, 0);
x_57 = lean_ctor_get(x_31, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_31);
lean_inc(x_5);
x_58 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_5, x_6, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_63 = l_Lean_MessageData_ofExpr(x_29);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(7, 2, 0);
} else {
 x_64 = x_61;
 lean_ctor_set_tag(x_64, 7);
}
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__7;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_56);
lean_ctor_set(x_27, 0, x_66);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_65);
lean_ctor_set(x_20, 0, x_27);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_20);
lean_ctor_set(x_67, 1, x_59);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
x_69 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_19, x_68, x_7, x_8, x_9, x_10, x_60);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_12 = x_18;
x_13 = x_70;
goto block_17;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_71 = lean_ctor_get(x_27, 0);
x_72 = lean_ctor_get(x_27, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_27);
lean_inc(x_3);
x_73 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_3, x_6, x_72);
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
lean_inc(x_5);
x_77 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_5, x_6, x_75);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_82 = l_Lean_MessageData_ofExpr(x_71);
if (lean_is_scalar(x_80)) {
 x_83 = lean_alloc_ctor(7, 2, 0);
} else {
 x_83 = x_80;
 lean_ctor_set_tag(x_83, 7);
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__7;
if (lean_is_scalar(x_76)) {
 x_85 = lean_alloc_ctor(7, 2, 0);
} else {
 x_85 = x_76;
 lean_ctor_set_tag(x_85, 7);
}
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_74);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_84);
lean_ctor_set(x_20, 0, x_86);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_20);
lean_ctor_set(x_87, 1, x_78);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_81);
x_89 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_19, x_88, x_7, x_8, x_9, x_10, x_79);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_12 = x_18;
x_13 = x_90;
goto block_17;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_91 = lean_ctor_get(x_20, 1);
lean_inc(x_91);
lean_dec(x_20);
x_92 = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(x_2, x_6, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
lean_inc(x_3);
x_96 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_3, x_6, x_94);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
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
lean_inc(x_5);
x_100 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_5, x_6, x_98);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_105 = l_Lean_MessageData_ofExpr(x_93);
if (lean_is_scalar(x_103)) {
 x_106 = lean_alloc_ctor(7, 2, 0);
} else {
 x_106 = x_103;
 lean_ctor_set_tag(x_106, 7);
}
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__7;
if (lean_is_scalar(x_99)) {
 x_108 = lean_alloc_ctor(7, 2, 0);
} else {
 x_108 = x_99;
 lean_ctor_set_tag(x_108, 7);
}
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
if (lean_is_scalar(x_95)) {
 x_109 = lean_alloc_ctor(7, 2, 0);
} else {
 x_109 = x_95;
 lean_ctor_set_tag(x_109, 7);
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_97);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_101);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_104);
x_113 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_19, x_112, x_7, x_8, x_9, x_10, x_102);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_12 = x_18;
x_13 = x_114;
goto block_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_5, 2);
x_12 = lean_ctor_get(x_5, 3);
x_13 = lean_ctor_get(x_5, 4);
x_14 = lean_ctor_get(x_5, 5);
x_15 = lean_ctor_get(x_5, 6);
x_16 = lean_ctor_get(x_5, 7);
x_17 = lean_ctor_get(x_5, 8);
x_18 = lean_ctor_get(x_5, 9);
x_19 = lean_ctor_get(x_5, 10);
x_20 = lean_ctor_get(x_5, 11);
x_21 = lean_ctor_get(x_5, 12);
x_22 = lean_nat_dec_eq(x_12, x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = l_Int_Linear_Poly_findVarToSubst___redArg(x_23, x_2, x_7);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_free_object(x_5);
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
lean_dec(x_10);
lean_dec(x_9);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_12, x_37);
lean_dec(x_12);
lean_ctor_set(x_5, 3, x_38);
x_39 = l_Int_Linear_Poly_coeff(x_36, x_35);
lean_dec(x_36);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg(x_39, x_35, x_32, x_34, x_1, x_2, x_3, x_4, x_5, x_6, x_33);
lean_dec(x_34);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_1 = x_41;
x_7 = x_42;
goto _start;
}
}
else
{
lean_object* x_44; 
lean_free_object(x_5);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_44 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_14, x_7);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; uint8_t x_60; 
x_45 = lean_ctor_get(x_5, 0);
x_46 = lean_ctor_get(x_5, 1);
x_47 = lean_ctor_get(x_5, 2);
x_48 = lean_ctor_get(x_5, 3);
x_49 = lean_ctor_get(x_5, 4);
x_50 = lean_ctor_get(x_5, 5);
x_51 = lean_ctor_get(x_5, 6);
x_52 = lean_ctor_get(x_5, 7);
x_53 = lean_ctor_get(x_5, 8);
x_54 = lean_ctor_get(x_5, 9);
x_55 = lean_ctor_get(x_5, 10);
x_56 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_57 = lean_ctor_get(x_5, 11);
x_58 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_59 = lean_ctor_get(x_5, 12);
lean_inc(x_59);
lean_inc(x_57);
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
lean_dec(x_5);
x_60 = lean_nat_dec_eq(x_48, x_49);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = l_Int_Linear_Poly_findVarToSubst___redArg(x_61, x_2, x_7);
lean_dec(x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
lean_dec(x_68);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_48, x_74);
lean_dec(x_48);
x_76 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_76, 0, x_45);
lean_ctor_set(x_76, 1, x_46);
lean_ctor_set(x_76, 2, x_47);
lean_ctor_set(x_76, 3, x_75);
lean_ctor_set(x_76, 4, x_49);
lean_ctor_set(x_76, 5, x_50);
lean_ctor_set(x_76, 6, x_51);
lean_ctor_set(x_76, 7, x_52);
lean_ctor_set(x_76, 8, x_53);
lean_ctor_set(x_76, 9, x_54);
lean_ctor_set(x_76, 10, x_55);
lean_ctor_set(x_76, 11, x_57);
lean_ctor_set(x_76, 12, x_59);
lean_ctor_set_uint8(x_76, sizeof(void*)*13, x_56);
lean_ctor_set_uint8(x_76, sizeof(void*)*13 + 1, x_58);
x_77 = l_Int_Linear_Poly_coeff(x_73, x_72);
lean_dec(x_73);
x_78 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg(x_77, x_72, x_69, x_71, x_1, x_2, x_3, x_4, x_76, x_6, x_70);
lean_dec(x_71);
lean_dec(x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_1 = x_79;
x_5 = x_76;
x_7 = x_80;
goto _start;
}
}
else
{
lean_object* x_82; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_1);
x_82 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_50, x_7);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isNegEq(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_int_neg(x_4);
x_6 = lean_int_dec_eq(x_3, x_5);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_18; uint8_t x_19; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
x_18 = lean_int_neg(x_12);
x_19 = lean_int_dec_eq(x_9, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
x_15 = x_19;
goto block_17;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_eq(x_10, x_13);
x_15 = x_20;
goto block_17;
}
block_17:
{
if (x_15 == 0)
{
return x_15;
}
else
{
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNegEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_Linear_Poly_isNegEq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0(x_1, x_7, x_5);
lean_dec(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_632_(x_13, x_1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_push___redArg(x_5, x_12);
x_6 = x_15;
goto block_10;
}
else
{
lean_dec(x_12);
x_6 = x_5;
goto block_10;
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_11 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__0(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_12);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
return x_3;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_14, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
return x_3;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_19 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__1(x_1, x_12, x_17, x_18, x_3);
return x_19;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArrayNode(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0;
x_8 = lean_usize_shift_right(x_3, x_4);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_7, x_6, x_9);
x_11 = 1;
x_12 = lean_usize_shift_left(x_11, x_4);
x_13 = lean_usize_sub(x_12, x_11);
x_14 = lean_usize_land(x_3, x_13);
x_15 = 5;
x_16 = lean_usize_sub(x_4, x_15);
x_17 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(x_1, x_10, x_14, x_16, x_5);
lean_dec(x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_9, x_18);
lean_dec(x_9);
x_20 = lean_array_get_size(x_6);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
return x_17;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_20, x_20);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
return x_17;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__0(x_1, x_6, x_23, x_24, x_17);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_usize_to_nat(x_3);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
return x_5;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_28, x_28);
if (x_30 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
return x_5;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_33 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__1(x_1, x_26, x_31, x_32, x_5);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get_usize(x_2, 4);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_nat_dec_le(x_10, x_4);
if (x_11 == 0)
{
size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_usize_of_nat(x_4);
x_13 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(x_1, x_7, x_12, x_9, x_3);
x_14 = lean_array_get_size(x_8);
x_15 = lean_nat_dec_lt(x_5, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
return x_13;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_14, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
return x_13;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_19 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__1(x_1, x_8, x_17, x_18, x_13);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_nat_sub(x_4, x_10);
x_21 = lean_array_get_size(x_8);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_3;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_3;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__1(x_1, x_8, x_24, x_25, x_3);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0(x_1, x_27, x_3);
x_30 = lean_array_get_size(x_28);
x_31 = lean_nat_dec_lt(x_5, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
return x_29;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
return x_29;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__1(x_1, x_28, x_33, x_34, x_29);
return x_35;
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__0;
x_4 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_5);
return x_2;
}
else
{
uint8_t x_10; 
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
x_21 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg(x_1, x_18, x_15, x_17);
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
x_32 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg(x_1, x_29, x_26, x_28);
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
lean_inc(x_35);
x_36 = lean_usize_to_nat(x_3);
x_37 = lean_array_get_size(x_35);
x_38 = lean_nat_dec_lt(x_36, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_dec(x_36);
lean_dec(x_35);
return x_2;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_2);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_2, 0);
lean_dec(x_40);
x_41 = lean_array_fget(x_35, x_36);
x_42 = lean_box(0);
x_43 = lean_array_fset(x_35, x_36, x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__2;
x_46 = l_Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(x_1, x_41, x_45, x_44);
lean_dec(x_41);
x_47 = lean_array_fset(x_43, x_36, x_46);
lean_dec(x_36);
lean_ctor_set(x_2, 0, x_47);
return x_2;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
x_48 = lean_array_fget(x_35, x_36);
x_49 = lean_box(0);
x_50 = lean_array_fset(x_35, x_36, x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__2;
x_53 = l_Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(x_1, x_48, x_52, x_51);
lean_dec(x_48);
x_54 = lean_array_fset(x_50, x_36, x_53);
lean_dec(x_36);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg(x_1, x_6, x_11, x_8);
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
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_array_fget(x_7, x_13);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_7, x_13, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__2;
x_21 = l_Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(x_1, x_16, x_20, x_19);
lean_dec(x_16);
x_22 = lean_array_fset(x_18, x_13, x_21);
lean_dec(x_13);
lean_ctor_set(x_3, 1, x_22);
return x_3;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
x_25 = lean_ctor_get(x_3, 2);
x_26 = lean_ctor_get_usize(x_3, 4);
x_27 = lean_ctor_get(x_3, 3);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_28 = lean_nat_dec_le(x_27, x_4);
if (x_28 == 0)
{
size_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_usize_of_nat(x_4);
x_30 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg(x_1, x_23, x_29, x_26);
x_31 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set_usize(x_31, 4, x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_nat_sub(x_4, x_27);
x_33 = lean_array_get_size(x_24);
x_34 = lean_nat_dec_lt(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_27);
lean_ctor_set_usize(x_35, 4, x_26);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_array_fget(x_24, x_32);
x_37 = lean_box(0);
x_38 = lean_array_fset(x_24, x_32, x_37);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__2;
x_41 = l_Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(x_1, x_36, x_40, x_39);
lean_dec(x_36);
x_42 = lean_array_fset(x_38, x_32, x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_25);
lean_ctor_set(x_43, 3, x_27);
lean_ctor_set_usize(x_43, 4, x_26);
return x_43;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArray(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_8);
x_9 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__8;
x_13 = lean_int_dec_lt(x_10, x_12);
lean_dec(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_st_ref_take(x_2, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 14);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_15, 14);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_16, 1);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_17, 9);
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_26 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_25, x_24, x_11);
lean_dec(x_11);
lean_dec(x_8);
lean_ctor_set(x_17, 9, x_26);
x_27 = lean_st_ref_set(x_2, x_15, x_18);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
x_36 = lean_ctor_get(x_17, 2);
x_37 = lean_ctor_get(x_17, 3);
x_38 = lean_ctor_get(x_17, 4);
x_39 = lean_ctor_get(x_17, 5);
x_40 = lean_ctor_get(x_17, 6);
x_41 = lean_ctor_get(x_17, 7);
x_42 = lean_ctor_get(x_17, 8);
x_43 = lean_ctor_get(x_17, 9);
x_44 = lean_ctor_get(x_17, 10);
x_45 = lean_ctor_get(x_17, 11);
x_46 = lean_ctor_get(x_17, 12);
x_47 = lean_ctor_get(x_17, 13);
x_48 = lean_ctor_get(x_17, 14);
x_49 = lean_ctor_get(x_17, 15);
x_50 = lean_ctor_get_uint8(x_17, sizeof(void*)*22);
x_51 = lean_ctor_get(x_17, 16);
x_52 = lean_ctor_get(x_17, 17);
x_53 = lean_ctor_get(x_17, 18);
x_54 = lean_ctor_get(x_17, 19);
x_55 = lean_ctor_get(x_17, 20);
x_56 = lean_ctor_get(x_17, 21);
x_57 = lean_ctor_get_uint8(x_17, sizeof(void*)*22 + 1);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
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
lean_dec(x_17);
x_58 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_59 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_58, x_43, x_11);
lean_dec(x_11);
lean_dec(x_8);
x_60 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_60, 0, x_34);
lean_ctor_set(x_60, 1, x_35);
lean_ctor_set(x_60, 2, x_36);
lean_ctor_set(x_60, 3, x_37);
lean_ctor_set(x_60, 4, x_38);
lean_ctor_set(x_60, 5, x_39);
lean_ctor_set(x_60, 6, x_40);
lean_ctor_set(x_60, 7, x_41);
lean_ctor_set(x_60, 8, x_42);
lean_ctor_set(x_60, 9, x_59);
lean_ctor_set(x_60, 10, x_44);
lean_ctor_set(x_60, 11, x_45);
lean_ctor_set(x_60, 12, x_46);
lean_ctor_set(x_60, 13, x_47);
lean_ctor_set(x_60, 14, x_48);
lean_ctor_set(x_60, 15, x_49);
lean_ctor_set(x_60, 16, x_51);
lean_ctor_set(x_60, 17, x_52);
lean_ctor_set(x_60, 18, x_53);
lean_ctor_set(x_60, 19, x_54);
lean_ctor_set(x_60, 20, x_55);
lean_ctor_set(x_60, 21, x_56);
lean_ctor_set_uint8(x_60, sizeof(void*)*22, x_50);
lean_ctor_set_uint8(x_60, sizeof(void*)*22 + 1, x_57);
lean_ctor_set(x_16, 1, x_60);
x_61 = lean_st_ref_set(x_2, x_15, x_18);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_66 = lean_ctor_get(x_16, 0);
x_67 = lean_ctor_get(x_16, 2);
x_68 = lean_ctor_get(x_16, 3);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_16);
x_69 = lean_ctor_get(x_17, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_17, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_17, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_17, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_17, 4);
lean_inc(x_73);
x_74 = lean_ctor_get(x_17, 5);
lean_inc(x_74);
x_75 = lean_ctor_get(x_17, 6);
lean_inc(x_75);
x_76 = lean_ctor_get(x_17, 7);
lean_inc(x_76);
x_77 = lean_ctor_get(x_17, 8);
lean_inc(x_77);
x_78 = lean_ctor_get(x_17, 9);
lean_inc(x_78);
x_79 = lean_ctor_get(x_17, 10);
lean_inc(x_79);
x_80 = lean_ctor_get(x_17, 11);
lean_inc(x_80);
x_81 = lean_ctor_get(x_17, 12);
lean_inc(x_81);
x_82 = lean_ctor_get(x_17, 13);
lean_inc(x_82);
x_83 = lean_ctor_get(x_17, 14);
lean_inc(x_83);
x_84 = lean_ctor_get(x_17, 15);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_17, sizeof(void*)*22);
x_86 = lean_ctor_get(x_17, 16);
lean_inc(x_86);
x_87 = lean_ctor_get(x_17, 17);
lean_inc(x_87);
x_88 = lean_ctor_get(x_17, 18);
lean_inc(x_88);
x_89 = lean_ctor_get(x_17, 19);
lean_inc(x_89);
x_90 = lean_ctor_get(x_17, 20);
lean_inc(x_90);
x_91 = lean_ctor_get(x_17, 21);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_17, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 lean_ctor_release(x_17, 6);
 lean_ctor_release(x_17, 7);
 lean_ctor_release(x_17, 8);
 lean_ctor_release(x_17, 9);
 lean_ctor_release(x_17, 10);
 lean_ctor_release(x_17, 11);
 lean_ctor_release(x_17, 12);
 lean_ctor_release(x_17, 13);
 lean_ctor_release(x_17, 14);
 lean_ctor_release(x_17, 15);
 lean_ctor_release(x_17, 16);
 lean_ctor_release(x_17, 17);
 lean_ctor_release(x_17, 18);
 lean_ctor_release(x_17, 19);
 lean_ctor_release(x_17, 20);
 lean_ctor_release(x_17, 21);
 x_93 = x_17;
} else {
 lean_dec_ref(x_17);
 x_93 = lean_box(0);
}
x_94 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_95 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_94, x_78, x_11);
lean_dec(x_11);
lean_dec(x_8);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(0, 22, 2);
} else {
 x_96 = x_93;
}
lean_ctor_set(x_96, 0, x_69);
lean_ctor_set(x_96, 1, x_70);
lean_ctor_set(x_96, 2, x_71);
lean_ctor_set(x_96, 3, x_72);
lean_ctor_set(x_96, 4, x_73);
lean_ctor_set(x_96, 5, x_74);
lean_ctor_set(x_96, 6, x_75);
lean_ctor_set(x_96, 7, x_76);
lean_ctor_set(x_96, 8, x_77);
lean_ctor_set(x_96, 9, x_95);
lean_ctor_set(x_96, 10, x_79);
lean_ctor_set(x_96, 11, x_80);
lean_ctor_set(x_96, 12, x_81);
lean_ctor_set(x_96, 13, x_82);
lean_ctor_set(x_96, 14, x_83);
lean_ctor_set(x_96, 15, x_84);
lean_ctor_set(x_96, 16, x_86);
lean_ctor_set(x_96, 17, x_87);
lean_ctor_set(x_96, 18, x_88);
lean_ctor_set(x_96, 19, x_89);
lean_ctor_set(x_96, 20, x_90);
lean_ctor_set(x_96, 21, x_91);
lean_ctor_set_uint8(x_96, sizeof(void*)*22, x_85);
lean_ctor_set_uint8(x_96, sizeof(void*)*22 + 1, x_92);
x_97 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_97, 0, x_66);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_67);
lean_ctor_set(x_97, 3, x_68);
lean_ctor_set(x_15, 14, x_97);
x_98 = lean_st_ref_set(x_2, x_15, x_18);
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
x_101 = lean_box(0);
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
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_103 = lean_ctor_get(x_15, 0);
x_104 = lean_ctor_get(x_15, 1);
x_105 = lean_ctor_get(x_15, 2);
x_106 = lean_ctor_get(x_15, 3);
x_107 = lean_ctor_get(x_15, 4);
x_108 = lean_ctor_get(x_15, 5);
x_109 = lean_ctor_get(x_15, 6);
x_110 = lean_ctor_get(x_15, 7);
x_111 = lean_ctor_get_uint8(x_15, sizeof(void*)*16);
x_112 = lean_ctor_get(x_15, 8);
x_113 = lean_ctor_get(x_15, 9);
x_114 = lean_ctor_get(x_15, 10);
x_115 = lean_ctor_get(x_15, 11);
x_116 = lean_ctor_get(x_15, 12);
x_117 = lean_ctor_get(x_15, 13);
x_118 = lean_ctor_get(x_15, 15);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_15);
x_119 = lean_ctor_get(x_16, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_16, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_16, 3);
lean_inc(x_121);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 x_122 = x_16;
} else {
 lean_dec_ref(x_16);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_17, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_17, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_17, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_17, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_17, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_17, 5);
lean_inc(x_128);
x_129 = lean_ctor_get(x_17, 6);
lean_inc(x_129);
x_130 = lean_ctor_get(x_17, 7);
lean_inc(x_130);
x_131 = lean_ctor_get(x_17, 8);
lean_inc(x_131);
x_132 = lean_ctor_get(x_17, 9);
lean_inc(x_132);
x_133 = lean_ctor_get(x_17, 10);
lean_inc(x_133);
x_134 = lean_ctor_get(x_17, 11);
lean_inc(x_134);
x_135 = lean_ctor_get(x_17, 12);
lean_inc(x_135);
x_136 = lean_ctor_get(x_17, 13);
lean_inc(x_136);
x_137 = lean_ctor_get(x_17, 14);
lean_inc(x_137);
x_138 = lean_ctor_get(x_17, 15);
lean_inc(x_138);
x_139 = lean_ctor_get_uint8(x_17, sizeof(void*)*22);
x_140 = lean_ctor_get(x_17, 16);
lean_inc(x_140);
x_141 = lean_ctor_get(x_17, 17);
lean_inc(x_141);
x_142 = lean_ctor_get(x_17, 18);
lean_inc(x_142);
x_143 = lean_ctor_get(x_17, 19);
lean_inc(x_143);
x_144 = lean_ctor_get(x_17, 20);
lean_inc(x_144);
x_145 = lean_ctor_get(x_17, 21);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_17, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 lean_ctor_release(x_17, 6);
 lean_ctor_release(x_17, 7);
 lean_ctor_release(x_17, 8);
 lean_ctor_release(x_17, 9);
 lean_ctor_release(x_17, 10);
 lean_ctor_release(x_17, 11);
 lean_ctor_release(x_17, 12);
 lean_ctor_release(x_17, 13);
 lean_ctor_release(x_17, 14);
 lean_ctor_release(x_17, 15);
 lean_ctor_release(x_17, 16);
 lean_ctor_release(x_17, 17);
 lean_ctor_release(x_17, 18);
 lean_ctor_release(x_17, 19);
 lean_ctor_release(x_17, 20);
 lean_ctor_release(x_17, 21);
 x_147 = x_17;
} else {
 lean_dec_ref(x_17);
 x_147 = lean_box(0);
}
x_148 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_149 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_148, x_132, x_11);
lean_dec(x_11);
lean_dec(x_8);
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(0, 22, 2);
} else {
 x_150 = x_147;
}
lean_ctor_set(x_150, 0, x_123);
lean_ctor_set(x_150, 1, x_124);
lean_ctor_set(x_150, 2, x_125);
lean_ctor_set(x_150, 3, x_126);
lean_ctor_set(x_150, 4, x_127);
lean_ctor_set(x_150, 5, x_128);
lean_ctor_set(x_150, 6, x_129);
lean_ctor_set(x_150, 7, x_130);
lean_ctor_set(x_150, 8, x_131);
lean_ctor_set(x_150, 9, x_149);
lean_ctor_set(x_150, 10, x_133);
lean_ctor_set(x_150, 11, x_134);
lean_ctor_set(x_150, 12, x_135);
lean_ctor_set(x_150, 13, x_136);
lean_ctor_set(x_150, 14, x_137);
lean_ctor_set(x_150, 15, x_138);
lean_ctor_set(x_150, 16, x_140);
lean_ctor_set(x_150, 17, x_141);
lean_ctor_set(x_150, 18, x_142);
lean_ctor_set(x_150, 19, x_143);
lean_ctor_set(x_150, 20, x_144);
lean_ctor_set(x_150, 21, x_145);
lean_ctor_set_uint8(x_150, sizeof(void*)*22, x_139);
lean_ctor_set_uint8(x_150, sizeof(void*)*22 + 1, x_146);
if (lean_is_scalar(x_122)) {
 x_151 = lean_alloc_ctor(0, 4, 0);
} else {
 x_151 = x_122;
}
lean_ctor_set(x_151, 0, x_119);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_151, 2, x_120);
lean_ctor_set(x_151, 3, x_121);
x_152 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_152, 0, x_103);
lean_ctor_set(x_152, 1, x_104);
lean_ctor_set(x_152, 2, x_105);
lean_ctor_set(x_152, 3, x_106);
lean_ctor_set(x_152, 4, x_107);
lean_ctor_set(x_152, 5, x_108);
lean_ctor_set(x_152, 6, x_109);
lean_ctor_set(x_152, 7, x_110);
lean_ctor_set(x_152, 8, x_112);
lean_ctor_set(x_152, 9, x_113);
lean_ctor_set(x_152, 10, x_114);
lean_ctor_set(x_152, 11, x_115);
lean_ctor_set(x_152, 12, x_116);
lean_ctor_set(x_152, 13, x_117);
lean_ctor_set(x_152, 14, x_151);
lean_ctor_set(x_152, 15, x_118);
lean_ctor_set_uint8(x_152, sizeof(void*)*16, x_111);
x_153 = lean_st_ref_set(x_2, x_152, x_18);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
x_156 = lean_box(0);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_st_ref_take(x_2, x_7);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_159, 14);
lean_inc(x_160);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 1);
lean_inc(x_162);
lean_dec(x_158);
x_163 = !lean_is_exclusive(x_159);
if (x_163 == 0)
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_ctor_get(x_159, 14);
lean_dec(x_164);
x_165 = !lean_is_exclusive(x_160);
if (x_165 == 0)
{
lean_object* x_166; uint8_t x_167; 
x_166 = lean_ctor_get(x_160, 1);
lean_dec(x_166);
x_167 = !lean_is_exclusive(x_161);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_168 = lean_ctor_get(x_161, 8);
x_169 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_170 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_169, x_168, x_11);
lean_dec(x_11);
lean_dec(x_8);
lean_ctor_set(x_161, 8, x_170);
x_171 = lean_st_ref_set(x_2, x_159, x_162);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_171, 0);
lean_dec(x_173);
x_174 = lean_box(0);
lean_ctor_set(x_171, 0, x_174);
return x_171;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
lean_dec(x_171);
x_176 = lean_box(0);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_178 = lean_ctor_get(x_161, 0);
x_179 = lean_ctor_get(x_161, 1);
x_180 = lean_ctor_get(x_161, 2);
x_181 = lean_ctor_get(x_161, 3);
x_182 = lean_ctor_get(x_161, 4);
x_183 = lean_ctor_get(x_161, 5);
x_184 = lean_ctor_get(x_161, 6);
x_185 = lean_ctor_get(x_161, 7);
x_186 = lean_ctor_get(x_161, 8);
x_187 = lean_ctor_get(x_161, 9);
x_188 = lean_ctor_get(x_161, 10);
x_189 = lean_ctor_get(x_161, 11);
x_190 = lean_ctor_get(x_161, 12);
x_191 = lean_ctor_get(x_161, 13);
x_192 = lean_ctor_get(x_161, 14);
x_193 = lean_ctor_get(x_161, 15);
x_194 = lean_ctor_get_uint8(x_161, sizeof(void*)*22);
x_195 = lean_ctor_get(x_161, 16);
x_196 = lean_ctor_get(x_161, 17);
x_197 = lean_ctor_get(x_161, 18);
x_198 = lean_ctor_get(x_161, 19);
x_199 = lean_ctor_get(x_161, 20);
x_200 = lean_ctor_get(x_161, 21);
x_201 = lean_ctor_get_uint8(x_161, sizeof(void*)*22 + 1);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_161);
x_202 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_203 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_202, x_186, x_11);
lean_dec(x_11);
lean_dec(x_8);
x_204 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_204, 0, x_178);
lean_ctor_set(x_204, 1, x_179);
lean_ctor_set(x_204, 2, x_180);
lean_ctor_set(x_204, 3, x_181);
lean_ctor_set(x_204, 4, x_182);
lean_ctor_set(x_204, 5, x_183);
lean_ctor_set(x_204, 6, x_184);
lean_ctor_set(x_204, 7, x_185);
lean_ctor_set(x_204, 8, x_203);
lean_ctor_set(x_204, 9, x_187);
lean_ctor_set(x_204, 10, x_188);
lean_ctor_set(x_204, 11, x_189);
lean_ctor_set(x_204, 12, x_190);
lean_ctor_set(x_204, 13, x_191);
lean_ctor_set(x_204, 14, x_192);
lean_ctor_set(x_204, 15, x_193);
lean_ctor_set(x_204, 16, x_195);
lean_ctor_set(x_204, 17, x_196);
lean_ctor_set(x_204, 18, x_197);
lean_ctor_set(x_204, 19, x_198);
lean_ctor_set(x_204, 20, x_199);
lean_ctor_set(x_204, 21, x_200);
lean_ctor_set_uint8(x_204, sizeof(void*)*22, x_194);
lean_ctor_set_uint8(x_204, sizeof(void*)*22 + 1, x_201);
lean_ctor_set(x_160, 1, x_204);
x_205 = lean_st_ref_set(x_2, x_159, x_162);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_207 = x_205;
} else {
 lean_dec_ref(x_205);
 x_207 = lean_box(0);
}
x_208 = lean_box(0);
if (lean_is_scalar(x_207)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_207;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_206);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_210 = lean_ctor_get(x_160, 0);
x_211 = lean_ctor_get(x_160, 2);
x_212 = lean_ctor_get(x_160, 3);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_160);
x_213 = lean_ctor_get(x_161, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_161, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_161, 2);
lean_inc(x_215);
x_216 = lean_ctor_get(x_161, 3);
lean_inc(x_216);
x_217 = lean_ctor_get(x_161, 4);
lean_inc(x_217);
x_218 = lean_ctor_get(x_161, 5);
lean_inc(x_218);
x_219 = lean_ctor_get(x_161, 6);
lean_inc(x_219);
x_220 = lean_ctor_get(x_161, 7);
lean_inc(x_220);
x_221 = lean_ctor_get(x_161, 8);
lean_inc(x_221);
x_222 = lean_ctor_get(x_161, 9);
lean_inc(x_222);
x_223 = lean_ctor_get(x_161, 10);
lean_inc(x_223);
x_224 = lean_ctor_get(x_161, 11);
lean_inc(x_224);
x_225 = lean_ctor_get(x_161, 12);
lean_inc(x_225);
x_226 = lean_ctor_get(x_161, 13);
lean_inc(x_226);
x_227 = lean_ctor_get(x_161, 14);
lean_inc(x_227);
x_228 = lean_ctor_get(x_161, 15);
lean_inc(x_228);
x_229 = lean_ctor_get_uint8(x_161, sizeof(void*)*22);
x_230 = lean_ctor_get(x_161, 16);
lean_inc(x_230);
x_231 = lean_ctor_get(x_161, 17);
lean_inc(x_231);
x_232 = lean_ctor_get(x_161, 18);
lean_inc(x_232);
x_233 = lean_ctor_get(x_161, 19);
lean_inc(x_233);
x_234 = lean_ctor_get(x_161, 20);
lean_inc(x_234);
x_235 = lean_ctor_get(x_161, 21);
lean_inc(x_235);
x_236 = lean_ctor_get_uint8(x_161, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 lean_ctor_release(x_161, 4);
 lean_ctor_release(x_161, 5);
 lean_ctor_release(x_161, 6);
 lean_ctor_release(x_161, 7);
 lean_ctor_release(x_161, 8);
 lean_ctor_release(x_161, 9);
 lean_ctor_release(x_161, 10);
 lean_ctor_release(x_161, 11);
 lean_ctor_release(x_161, 12);
 lean_ctor_release(x_161, 13);
 lean_ctor_release(x_161, 14);
 lean_ctor_release(x_161, 15);
 lean_ctor_release(x_161, 16);
 lean_ctor_release(x_161, 17);
 lean_ctor_release(x_161, 18);
 lean_ctor_release(x_161, 19);
 lean_ctor_release(x_161, 20);
 lean_ctor_release(x_161, 21);
 x_237 = x_161;
} else {
 lean_dec_ref(x_161);
 x_237 = lean_box(0);
}
x_238 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_239 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_238, x_221, x_11);
lean_dec(x_11);
lean_dec(x_8);
if (lean_is_scalar(x_237)) {
 x_240 = lean_alloc_ctor(0, 22, 2);
} else {
 x_240 = x_237;
}
lean_ctor_set(x_240, 0, x_213);
lean_ctor_set(x_240, 1, x_214);
lean_ctor_set(x_240, 2, x_215);
lean_ctor_set(x_240, 3, x_216);
lean_ctor_set(x_240, 4, x_217);
lean_ctor_set(x_240, 5, x_218);
lean_ctor_set(x_240, 6, x_219);
lean_ctor_set(x_240, 7, x_220);
lean_ctor_set(x_240, 8, x_239);
lean_ctor_set(x_240, 9, x_222);
lean_ctor_set(x_240, 10, x_223);
lean_ctor_set(x_240, 11, x_224);
lean_ctor_set(x_240, 12, x_225);
lean_ctor_set(x_240, 13, x_226);
lean_ctor_set(x_240, 14, x_227);
lean_ctor_set(x_240, 15, x_228);
lean_ctor_set(x_240, 16, x_230);
lean_ctor_set(x_240, 17, x_231);
lean_ctor_set(x_240, 18, x_232);
lean_ctor_set(x_240, 19, x_233);
lean_ctor_set(x_240, 20, x_234);
lean_ctor_set(x_240, 21, x_235);
lean_ctor_set_uint8(x_240, sizeof(void*)*22, x_229);
lean_ctor_set_uint8(x_240, sizeof(void*)*22 + 1, x_236);
x_241 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_241, 0, x_210);
lean_ctor_set(x_241, 1, x_240);
lean_ctor_set(x_241, 2, x_211);
lean_ctor_set(x_241, 3, x_212);
lean_ctor_set(x_159, 14, x_241);
x_242 = lean_st_ref_set(x_2, x_159, x_162);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_244 = x_242;
} else {
 lean_dec_ref(x_242);
 x_244 = lean_box(0);
}
x_245 = lean_box(0);
if (lean_is_scalar(x_244)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_244;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_243);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_247 = lean_ctor_get(x_159, 0);
x_248 = lean_ctor_get(x_159, 1);
x_249 = lean_ctor_get(x_159, 2);
x_250 = lean_ctor_get(x_159, 3);
x_251 = lean_ctor_get(x_159, 4);
x_252 = lean_ctor_get(x_159, 5);
x_253 = lean_ctor_get(x_159, 6);
x_254 = lean_ctor_get(x_159, 7);
x_255 = lean_ctor_get_uint8(x_159, sizeof(void*)*16);
x_256 = lean_ctor_get(x_159, 8);
x_257 = lean_ctor_get(x_159, 9);
x_258 = lean_ctor_get(x_159, 10);
x_259 = lean_ctor_get(x_159, 11);
x_260 = lean_ctor_get(x_159, 12);
x_261 = lean_ctor_get(x_159, 13);
x_262 = lean_ctor_get(x_159, 15);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_159);
x_263 = lean_ctor_get(x_160, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_160, 2);
lean_inc(x_264);
x_265 = lean_ctor_get(x_160, 3);
lean_inc(x_265);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 x_266 = x_160;
} else {
 lean_dec_ref(x_160);
 x_266 = lean_box(0);
}
x_267 = lean_ctor_get(x_161, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_161, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_161, 2);
lean_inc(x_269);
x_270 = lean_ctor_get(x_161, 3);
lean_inc(x_270);
x_271 = lean_ctor_get(x_161, 4);
lean_inc(x_271);
x_272 = lean_ctor_get(x_161, 5);
lean_inc(x_272);
x_273 = lean_ctor_get(x_161, 6);
lean_inc(x_273);
x_274 = lean_ctor_get(x_161, 7);
lean_inc(x_274);
x_275 = lean_ctor_get(x_161, 8);
lean_inc(x_275);
x_276 = lean_ctor_get(x_161, 9);
lean_inc(x_276);
x_277 = lean_ctor_get(x_161, 10);
lean_inc(x_277);
x_278 = lean_ctor_get(x_161, 11);
lean_inc(x_278);
x_279 = lean_ctor_get(x_161, 12);
lean_inc(x_279);
x_280 = lean_ctor_get(x_161, 13);
lean_inc(x_280);
x_281 = lean_ctor_get(x_161, 14);
lean_inc(x_281);
x_282 = lean_ctor_get(x_161, 15);
lean_inc(x_282);
x_283 = lean_ctor_get_uint8(x_161, sizeof(void*)*22);
x_284 = lean_ctor_get(x_161, 16);
lean_inc(x_284);
x_285 = lean_ctor_get(x_161, 17);
lean_inc(x_285);
x_286 = lean_ctor_get(x_161, 18);
lean_inc(x_286);
x_287 = lean_ctor_get(x_161, 19);
lean_inc(x_287);
x_288 = lean_ctor_get(x_161, 20);
lean_inc(x_288);
x_289 = lean_ctor_get(x_161, 21);
lean_inc(x_289);
x_290 = lean_ctor_get_uint8(x_161, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 lean_ctor_release(x_161, 4);
 lean_ctor_release(x_161, 5);
 lean_ctor_release(x_161, 6);
 lean_ctor_release(x_161, 7);
 lean_ctor_release(x_161, 8);
 lean_ctor_release(x_161, 9);
 lean_ctor_release(x_161, 10);
 lean_ctor_release(x_161, 11);
 lean_ctor_release(x_161, 12);
 lean_ctor_release(x_161, 13);
 lean_ctor_release(x_161, 14);
 lean_ctor_release(x_161, 15);
 lean_ctor_release(x_161, 16);
 lean_ctor_release(x_161, 17);
 lean_ctor_release(x_161, 18);
 lean_ctor_release(x_161, 19);
 lean_ctor_release(x_161, 20);
 lean_ctor_release(x_161, 21);
 x_291 = x_161;
} else {
 lean_dec_ref(x_161);
 x_291 = lean_box(0);
}
x_292 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_293 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_292, x_275, x_11);
lean_dec(x_11);
lean_dec(x_8);
if (lean_is_scalar(x_291)) {
 x_294 = lean_alloc_ctor(0, 22, 2);
} else {
 x_294 = x_291;
}
lean_ctor_set(x_294, 0, x_267);
lean_ctor_set(x_294, 1, x_268);
lean_ctor_set(x_294, 2, x_269);
lean_ctor_set(x_294, 3, x_270);
lean_ctor_set(x_294, 4, x_271);
lean_ctor_set(x_294, 5, x_272);
lean_ctor_set(x_294, 6, x_273);
lean_ctor_set(x_294, 7, x_274);
lean_ctor_set(x_294, 8, x_293);
lean_ctor_set(x_294, 9, x_276);
lean_ctor_set(x_294, 10, x_277);
lean_ctor_set(x_294, 11, x_278);
lean_ctor_set(x_294, 12, x_279);
lean_ctor_set(x_294, 13, x_280);
lean_ctor_set(x_294, 14, x_281);
lean_ctor_set(x_294, 15, x_282);
lean_ctor_set(x_294, 16, x_284);
lean_ctor_set(x_294, 17, x_285);
lean_ctor_set(x_294, 18, x_286);
lean_ctor_set(x_294, 19, x_287);
lean_ctor_set(x_294, 20, x_288);
lean_ctor_set(x_294, 21, x_289);
lean_ctor_set_uint8(x_294, sizeof(void*)*22, x_283);
lean_ctor_set_uint8(x_294, sizeof(void*)*22 + 1, x_290);
if (lean_is_scalar(x_266)) {
 x_295 = lean_alloc_ctor(0, 4, 0);
} else {
 x_295 = x_266;
}
lean_ctor_set(x_295, 0, x_263);
lean_ctor_set(x_295, 1, x_294);
lean_ctor_set(x_295, 2, x_264);
lean_ctor_set(x_295, 3, x_265);
x_296 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_296, 0, x_247);
lean_ctor_set(x_296, 1, x_248);
lean_ctor_set(x_296, 2, x_249);
lean_ctor_set(x_296, 3, x_250);
lean_ctor_set(x_296, 4, x_251);
lean_ctor_set(x_296, 5, x_252);
lean_ctor_set(x_296, 6, x_253);
lean_ctor_set(x_296, 7, x_254);
lean_ctor_set(x_296, 8, x_256);
lean_ctor_set(x_296, 9, x_257);
lean_ctor_set(x_296, 10, x_258);
lean_ctor_set(x_296, 11, x_259);
lean_ctor_set(x_296, 12, x_260);
lean_ctor_set(x_296, 13, x_261);
lean_ctor_set(x_296, 14, x_295);
lean_ctor_set(x_296, 15, x_262);
lean_ctor_set_uint8(x_296, sizeof(void*)*16, x_255);
x_297 = lean_st_ref_set(x_2, x_296, x_162);
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_299 = x_297;
} else {
 lean_dec_ref(x_297);
 x_299 = lean_box(0);
}
x_300 = lean_box(0);
if (lean_is_scalar(x_299)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_299;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_298);
return x_301;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg(x_1, x_2, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_9, x_8);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 0);
lean_dec(x_24);
x_25 = lean_array_uget(x_7, x_9);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_23);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_25, x_23, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_10, 0, x_30);
lean_ctor_set(x_26, 0, x_10);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_10, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_23);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_35);
lean_ctor_set(x_10, 0, x_6);
x_36 = 1;
x_37 = lean_usize_add(x_9, x_36);
x_9 = x_37;
x_19 = x_34;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_10);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_dec(x_10);
x_44 = lean_array_uget(x_7, x_9);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_43);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_45 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_44, x_43, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_43);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; 
lean_dec(x_43);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
lean_inc(x_6);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_6);
lean_ctor_set(x_54, 1, x_53);
x_55 = 1;
x_56 = lean_usize_add(x_9, x_55);
x_9 = x_56;
x_10 = x_54;
x_19 = x_52;
goto _start;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_43);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_45, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_60 = x_45;
} else {
 lean_dec_ref(x_45);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
x_21 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_19);
x_22 = lean_apply_11(x_1, x_21, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_ctor_set(x_6, 0, x_26);
lean_ctor_set(x_22, 0, x_6);
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
lean_ctor_set(x_6, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
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
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_31);
lean_ctor_set(x_6, 0, x_2);
x_32 = 1;
x_33 = lean_usize_add(x_5, x_32);
x_5 = x_33;
x_15 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_6);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_39);
x_41 = lean_apply_11(x_1, x_40, x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
lean_inc(x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
x_51 = 1;
x_52 = lean_usize_add(x_5, x_51);
x_5 = x_52;
x_6 = x_50;
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__1;
x_3 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__0;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("new eq: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = l_Int_Linear_Poly_isNegEq(x_1, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_5, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_5, 1, x_15);
lean_ctor_set(x_5, 0, x_21);
return x_5;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_2);
lean_inc(x_5);
x_24 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(x_5, x_7, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__2;
x_27 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_26, x_13, x_25);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_5);
lean_ctor_set_tag(x_27, 9);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_3);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_61; 
x_32 = lean_ctor_get(x_5, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_5, 0);
lean_dec(x_33);
lean_ctor_set(x_5, 1, x_27);
lean_ctor_set(x_5, 0, x_1);
x_61 = lean_unbox(x_29);
lean_dec(x_29);
if (x_61 == 0)
{
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_10;
x_38 = x_11;
x_39 = x_12;
x_40 = x_13;
x_41 = x_14;
x_42 = x_30;
goto block_60;
}
else
{
lean_object* x_62; uint8_t x_63; 
lean_inc(x_5);
x_62 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_5, x_7, x_30);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_66 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__4;
lean_ctor_set_tag(x_62, 7);
lean_ctor_set(x_62, 1, x_64);
lean_ctor_set(x_62, 0, x_66);
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_26, x_68, x_11, x_12, x_13, x_14, x_65);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_10;
x_38 = x_11;
x_39 = x_12;
x_40 = x_13;
x_41 = x_14;
x_42 = x_70;
goto block_60;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_62, 0);
x_72 = lean_ctor_get(x_62, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_62);
x_73 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__4;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
x_75 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_26, x_76, x_11, x_12, x_13, x_14, x_72);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_10;
x_38 = x_11;
x_39 = x_12;
x_40 = x_13;
x_41 = x_14;
x_42 = x_78;
goto block_60;
}
}
block_60:
{
lean_object* x_43; 
x_43 = lean_grind_cutsat_assert_eq(x_5, x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_box(x_17);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_4);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_43, 0, x_49);
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = lean_box(x_17);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_4);
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
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_102; 
lean_dec(x_5);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_27);
x_102 = lean_unbox(x_29);
lean_dec(x_29);
if (x_102 == 0)
{
x_80 = x_7;
x_81 = x_8;
x_82 = x_9;
x_83 = x_10;
x_84 = x_11;
x_85 = x_12;
x_86 = x_13;
x_87 = x_14;
x_88 = x_30;
goto block_101;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_inc(x_79);
x_103 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_79, x_7, x_30);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_107 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__4;
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(7, 2, 0);
} else {
 x_108 = x_106;
 lean_ctor_set_tag(x_108, 7);
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_104);
x_109 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_26, x_110, x_11, x_12, x_13, x_14, x_105);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_80 = x_7;
x_81 = x_8;
x_82 = x_9;
x_83 = x_10;
x_84 = x_11;
x_85 = x_12;
x_86 = x_13;
x_87 = x_14;
x_88 = x_112;
goto block_101;
}
block_101:
{
lean_object* x_89; 
x_89 = lean_grind_cutsat_assert_eq(x_79, x_80, x_81, x_82, x_83, x_84, x_85, x_86, x_87, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_box(x_17);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_4);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
if (lean_is_scalar(x_91)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_91;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_90);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_4);
x_97 = lean_ctor_get(x_89, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_89, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_99 = x_89;
} else {
 lean_dec_ref(x_89);
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
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_140; 
x_113 = lean_ctor_get(x_27, 0);
x_114 = lean_ctor_get(x_27, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_27);
lean_inc(x_5);
x_115 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_115, 0, x_3);
lean_ctor_set(x_115, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_116 = x_5;
} else {
 lean_dec_ref(x_5);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_1);
lean_ctor_set(x_117, 1, x_115);
x_140 = lean_unbox(x_113);
lean_dec(x_113);
if (x_140 == 0)
{
x_118 = x_7;
x_119 = x_8;
x_120 = x_9;
x_121 = x_10;
x_122 = x_11;
x_123 = x_12;
x_124 = x_13;
x_125 = x_14;
x_126 = x_114;
goto block_139;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_inc(x_117);
x_141 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_117, x_7, x_114);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__4;
if (lean_is_scalar(x_144)) {
 x_146 = lean_alloc_ctor(7, 2, 0);
} else {
 x_146 = x_144;
 lean_ctor_set_tag(x_146, 7);
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_142);
x_147 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_26, x_148, x_11, x_12, x_13, x_14, x_143);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_118 = x_7;
x_119 = x_8;
x_120 = x_9;
x_121 = x_10;
x_122 = x_11;
x_123 = x_12;
x_124 = x_13;
x_125 = x_14;
x_126 = x_150;
goto block_139;
}
block_139:
{
lean_object* x_127; 
x_127 = lean_grind_cutsat_assert_eq(x_117, x_118, x_119, x_120, x_121, x_122, x_123, x_124, x_125, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
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
x_130 = lean_box(x_17);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_4);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
if (lean_is_scalar(x_129)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_129;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_128);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_4);
x_135 = lean_ctor_get(x_127, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_127, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_137 = x_127;
} else {
 lean_dec_ref(x_127);
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
uint8_t x_151; 
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
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_24);
if (x_151 == 0)
{
return x_24;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_24, 0);
x_153 = lean_ctor_get(x_24, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_24);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
x_21 = lean_array_size(x_18);
x_22 = 0;
x_23 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_19, x_18, x_21, x_22, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_28);
lean_ctor_set(x_23, 0, x_6);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_24);
lean_free_object(x_6);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
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
lean_free_object(x_6);
x_38 = !lean_is_exclusive(x_23);
if (x_38 == 0)
{
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_6, 0);
lean_inc(x_42);
lean_dec(x_6);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
x_45 = lean_array_size(x_42);
x_46 = 0;
x_47 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_43, x_42, x_45, x_46, x_44, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_51 = x_47;
} else {
 lean_dec_ref(x_47);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_48);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_56 = x_47;
} else {
 lean_dec_ref(x_47);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_49, 0);
lean_inc(x_57);
lean_dec(x_49);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_47, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_61 = x_47;
} else {
 lean_dec_ref(x_47);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_6);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; size_t x_68; size_t x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_6, 0);
x_65 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___boxed), 15, 4);
lean_closure_set(x_65, 0, x_1);
lean_closure_set(x_65, 1, x_2);
lean_closure_set(x_65, 2, x_3);
lean_closure_set(x_65, 3, x_4);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_7);
x_68 = lean_array_size(x_64);
x_69 = 0;
x_70 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(x_65, x_66, x_64, x_68, x_69, x_67, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_64);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_70, 0);
lean_dec(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
lean_ctor_set(x_6, 0, x_75);
lean_ctor_set(x_70, 0, x_6);
return x_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_dec(x_71);
lean_ctor_set(x_6, 0, x_77);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_6);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_71);
lean_free_object(x_6);
x_79 = !lean_is_exclusive(x_70);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_70, 0);
lean_dec(x_80);
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_81);
return x_70;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_70, 1);
lean_inc(x_82);
lean_dec(x_70);
x_83 = lean_ctor_get(x_72, 0);
lean_inc(x_83);
lean_dec(x_72);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_free_object(x_6);
x_85 = !lean_is_exclusive(x_70);
if (x_85 == 0)
{
return x_70;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_70, 0);
x_87 = lean_ctor_get(x_70, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_70);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; size_t x_93; size_t x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_6, 0);
lean_inc(x_89);
lean_dec(x_6);
x_90 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___boxed), 15, 4);
lean_closure_set(x_90, 0, x_1);
lean_closure_set(x_90, 1, x_2);
lean_closure_set(x_90, 2, x_3);
lean_closure_set(x_90, 3, x_4);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_7);
x_93 = lean_array_size(x_89);
x_94 = 0;
x_95 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(x_90, x_91, x_89, x_93, x_94, x_92, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_89);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_99 = x_95;
} else {
 lean_dec_ref(x_95);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_99;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_98);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_96);
x_103 = lean_ctor_get(x_95, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_104 = x_95;
} else {
 lean_dec_ref(x_95);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_97, 0);
lean_inc(x_105);
lean_dec(x_97);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_95, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_95, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_109 = x_95;
} else {
 lean_dec_ref(x_95);
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
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
x_21 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_19);
x_22 = lean_apply_11(x_1, x_21, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_6, 0, x_23);
lean_ctor_set(x_22, 0, x_6);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_6, 0, x_28);
lean_ctor_set(x_22, 0, x_6);
return x_22;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_31 = x_23;
} else {
 lean_dec_ref(x_23);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_31;
 lean_ctor_set_tag(x_32, 1);
}
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_6, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_19);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_35);
lean_ctor_set(x_6, 0, x_2);
x_36 = 1;
x_37 = lean_usize_add(x_5, x_36);
x_5 = x_37;
x_15 = x_34;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_6);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_43);
x_45 = lean_apply_11(x_1, x_44, x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_50 = x_46;
} else {
 lean_dec_ref(x_46);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_50;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
lean_dec(x_43);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_dec(x_45);
x_55 = lean_ctor_get(x_46, 0);
lean_inc(x_55);
lean_dec(x_46);
lean_inc(x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_5, x_57);
x_5 = x_58;
x_6 = x_56;
x_15 = x_54;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_43);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_ctor_get(x_45, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_45, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_62 = x_45;
} else {
 lean_dec_ref(x_45);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = l_Int_Linear_Poly_isNegEq(x_1, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_5, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_5, 1, x_15);
lean_ctor_set(x_5, 0, x_21);
return x_5;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_2);
lean_inc(x_5);
x_24 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(x_5, x_7, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__2;
x_27 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_26, x_13, x_25);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_5);
lean_ctor_set_tag(x_27, 9);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_3);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_61; 
x_32 = lean_ctor_get(x_5, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_5, 0);
lean_dec(x_33);
lean_ctor_set(x_5, 1, x_27);
lean_ctor_set(x_5, 0, x_1);
x_61 = lean_unbox(x_29);
lean_dec(x_29);
if (x_61 == 0)
{
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_10;
x_38 = x_11;
x_39 = x_12;
x_40 = x_13;
x_41 = x_14;
x_42 = x_30;
goto block_60;
}
else
{
lean_object* x_62; uint8_t x_63; 
lean_inc(x_5);
x_62 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_5, x_7, x_30);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_66 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__4;
lean_ctor_set_tag(x_62, 7);
lean_ctor_set(x_62, 1, x_64);
lean_ctor_set(x_62, 0, x_66);
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_26, x_68, x_11, x_12, x_13, x_14, x_65);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_10;
x_38 = x_11;
x_39 = x_12;
x_40 = x_13;
x_41 = x_14;
x_42 = x_70;
goto block_60;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_62, 0);
x_72 = lean_ctor_get(x_62, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_62);
x_73 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__4;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
x_75 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_26, x_76, x_11, x_12, x_13, x_14, x_72);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_10;
x_38 = x_11;
x_39 = x_12;
x_40 = x_13;
x_41 = x_14;
x_42 = x_78;
goto block_60;
}
}
block_60:
{
lean_object* x_43; 
x_43 = lean_grind_cutsat_assert_eq(x_5, x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_box(x_17);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_4);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_43, 0, x_49);
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = lean_box(x_17);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_4);
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
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_102; 
lean_dec(x_5);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_27);
x_102 = lean_unbox(x_29);
lean_dec(x_29);
if (x_102 == 0)
{
x_80 = x_7;
x_81 = x_8;
x_82 = x_9;
x_83 = x_10;
x_84 = x_11;
x_85 = x_12;
x_86 = x_13;
x_87 = x_14;
x_88 = x_30;
goto block_101;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_inc(x_79);
x_103 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_79, x_7, x_30);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_107 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__4;
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(7, 2, 0);
} else {
 x_108 = x_106;
 lean_ctor_set_tag(x_108, 7);
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_104);
x_109 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_26, x_110, x_11, x_12, x_13, x_14, x_105);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_80 = x_7;
x_81 = x_8;
x_82 = x_9;
x_83 = x_10;
x_84 = x_11;
x_85 = x_12;
x_86 = x_13;
x_87 = x_14;
x_88 = x_112;
goto block_101;
}
block_101:
{
lean_object* x_89; 
x_89 = lean_grind_cutsat_assert_eq(x_79, x_80, x_81, x_82, x_83, x_84, x_85, x_86, x_87, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_box(x_17);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_4);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
if (lean_is_scalar(x_91)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_91;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_90);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_4);
x_97 = lean_ctor_get(x_89, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_89, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_99 = x_89;
} else {
 lean_dec_ref(x_89);
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
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_140; 
x_113 = lean_ctor_get(x_27, 0);
x_114 = lean_ctor_get(x_27, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_27);
lean_inc(x_5);
x_115 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_115, 0, x_3);
lean_ctor_set(x_115, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_116 = x_5;
} else {
 lean_dec_ref(x_5);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_1);
lean_ctor_set(x_117, 1, x_115);
x_140 = lean_unbox(x_113);
lean_dec(x_113);
if (x_140 == 0)
{
x_118 = x_7;
x_119 = x_8;
x_120 = x_9;
x_121 = x_10;
x_122 = x_11;
x_123 = x_12;
x_124 = x_13;
x_125 = x_14;
x_126 = x_114;
goto block_139;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_inc(x_117);
x_141 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_117, x_7, x_114);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__4;
if (lean_is_scalar(x_144)) {
 x_146 = lean_alloc_ctor(7, 2, 0);
} else {
 x_146 = x_144;
 lean_ctor_set_tag(x_146, 7);
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_142);
x_147 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_26, x_148, x_11, x_12, x_13, x_14, x_143);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_118 = x_7;
x_119 = x_8;
x_120 = x_9;
x_121 = x_10;
x_122 = x_11;
x_123 = x_12;
x_124 = x_13;
x_125 = x_14;
x_126 = x_150;
goto block_139;
}
block_139:
{
lean_object* x_127; 
x_127 = lean_grind_cutsat_assert_eq(x_117, x_118, x_119, x_120, x_121, x_122, x_123, x_124, x_125, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
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
x_130 = lean_box(x_17);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_4);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
if (lean_is_scalar(x_129)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_129;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_128);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_4);
x_135 = lean_ctor_get(x_127, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_127, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_137 = x_127;
} else {
 lean_dec_ref(x_127);
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
uint8_t x_151; 
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
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_24);
if (x_151 == 0)
{
return x_24;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_24, 0);
x_153 = lean_ctor_get(x_24, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_24);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(x_1, x_2, x_3, x_4, x_6, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___lam__0___boxed), 15, 4);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_3);
lean_closure_set(x_28, 3, x_4);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_array_size(x_17);
x_32 = 0;
x_33 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__3(x_28, x_29, x_17, x_31, x_32, x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_26);
lean_dec(x_17);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
lean_ctor_set(x_33, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_34);
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_33, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_44);
return x_33;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_dec(x_33);
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
lean_dec(x_35);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_33);
if (x_48 == 0)
{
return x_33;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_33, 0);
x_50 = lean_ctor_get(x_33, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_33);
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
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_18);
if (x_52 == 0)
{
return x_18;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_18, 0);
x_54 = lean_ctor_get(x_18, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_18);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0() {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_43; uint8_t x_44; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_43 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__8;
x_44 = lean_int_dec_lt(x_13, x_43);
lean_dec(x_13);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_16, 8);
lean_inc(x_45);
lean_dec(x_16);
x_46 = lean_ctor_get(x_45, 2);
lean_inc(x_46);
x_47 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_48 = lean_nat_dec_lt(x_14, x_46);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_14);
x_49 = l_outOfBounds___redArg(x_47);
x_18 = x_49;
goto block_42;
}
else
{
lean_object* x_50; 
x_50 = l_Lean_PersistentArray_get_x21___redArg(x_47, x_45, x_14);
lean_dec(x_14);
x_18 = x_50;
goto block_42;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_16, 9);
lean_inc(x_51);
lean_dec(x_16);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_54 = lean_nat_dec_lt(x_14, x_52);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_51);
lean_dec(x_14);
x_55 = l_outOfBounds___redArg(x_53);
x_18 = x_55;
goto block_42;
}
else
{
lean_object* x_56; 
x_56 = l_Lean_PersistentArray_get_x21___redArg(x_53, x_51, x_14);
lean_dec(x_14);
x_18 = x_56;
goto block_42;
}
}
block_42:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0;
x_21 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(x_11, x_20, x_1, x_19, x_18, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = 0;
x_27 = lean_box(x_26);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
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
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_21, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_34);
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
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
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
return x_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 0);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_21);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__0___boxed(lean_object** _args) {
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
x_20 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_21 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_22 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_20, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_7);
lean_dec(x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__3(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0(x_1, x_7, x_5);
lean_dec(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_632_(x_13, x_1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_push___redArg(x_5, x_12);
x_6 = x_15;
goto block_10;
}
else
{
lean_dec(x_12);
x_6 = x_5;
goto block_10;
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_11 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__0(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_12);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
return x_3;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_14, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
return x_3;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_19 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__1(x_1, x_12, x_17, x_18, x_3);
return x_19;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArrayNode(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___closed__0;
x_8 = lean_usize_shift_right(x_3, x_4);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_7, x_6, x_9);
x_11 = 1;
x_12 = lean_usize_shift_left(x_11, x_4);
x_13 = lean_usize_sub(x_12, x_11);
x_14 = lean_usize_land(x_3, x_13);
x_15 = 5;
x_16 = lean_usize_sub(x_4, x_15);
x_17 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(x_1, x_10, x_14, x_16, x_5);
lean_dec(x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_9, x_18);
lean_dec(x_9);
x_20 = lean_array_get_size(x_6);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
return x_17;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_20, x_20);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
return x_17;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__0(x_1, x_6, x_23, x_24, x_17);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_usize_to_nat(x_3);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
return x_5;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_28, x_28);
if (x_30 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
return x_5;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_33 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__1(x_1, x_26, x_31, x_32, x_5);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get_usize(x_2, 4);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_nat_dec_le(x_10, x_4);
if (x_11 == 0)
{
size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_usize_of_nat(x_4);
x_13 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(x_1, x_7, x_12, x_9, x_3);
x_14 = lean_array_get_size(x_8);
x_15 = lean_nat_dec_lt(x_5, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
return x_13;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_14, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
return x_13;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_19 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__1(x_1, x_8, x_17, x_18, x_13);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_nat_sub(x_4, x_10);
x_21 = lean_array_get_size(x_8);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_3;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_3;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__1(x_1, x_8, x_24, x_25, x_3);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0(x_1, x_27, x_3);
x_30 = lean_array_get_size(x_28);
x_31 = lean_nat_dec_lt(x_5, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
return x_29;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
return x_29;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__1(x_1, x_28, x_33, x_34, x_29);
return x_35;
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__0;
x_4 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_5);
return x_2;
}
else
{
uint8_t x_10; 
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
x_21 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg(x_1, x_18, x_15, x_17);
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
x_32 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg(x_1, x_29, x_26, x_28);
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
lean_inc(x_35);
x_36 = lean_usize_to_nat(x_3);
x_37 = lean_array_get_size(x_35);
x_38 = lean_nat_dec_lt(x_36, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_dec(x_36);
lean_dec(x_35);
return x_2;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_2);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_2, 0);
lean_dec(x_40);
x_41 = lean_array_fget(x_35, x_36);
x_42 = lean_box(0);
x_43 = lean_array_fset(x_35, x_36, x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__2;
x_46 = l_Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(x_1, x_41, x_45, x_44);
lean_dec(x_41);
x_47 = lean_array_fset(x_43, x_36, x_46);
lean_dec(x_36);
lean_ctor_set(x_2, 0, x_47);
return x_2;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
x_48 = lean_array_fget(x_35, x_36);
x_49 = lean_box(0);
x_50 = lean_array_fset(x_35, x_36, x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__2;
x_53 = l_Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(x_1, x_48, x_52, x_51);
lean_dec(x_48);
x_54 = lean_array_fset(x_50, x_36, x_53);
lean_dec(x_36);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg(x_1, x_6, x_11, x_8);
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
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_array_fget(x_7, x_13);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_7, x_13, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__2;
x_21 = l_Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(x_1, x_16, x_20, x_19);
lean_dec(x_16);
x_22 = lean_array_fset(x_18, x_13, x_21);
lean_dec(x_13);
lean_ctor_set(x_3, 1, x_22);
return x_3;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
x_25 = lean_ctor_get(x_3, 2);
x_26 = lean_ctor_get_usize(x_3, 4);
x_27 = lean_ctor_get(x_3, 3);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_28 = lean_nat_dec_le(x_27, x_4);
if (x_28 == 0)
{
size_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_usize_of_nat(x_4);
x_30 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg(x_1, x_23, x_29, x_26);
x_31 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set_usize(x_31, 4, x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_nat_sub(x_4, x_27);
x_33 = lean_array_get_size(x_24);
x_34 = lean_nat_dec_lt(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_27);
lean_ctor_set_usize(x_35, 4, x_26);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_array_fget(x_24, x_32);
x_37 = lean_box(0);
x_38 = lean_array_fset(x_24, x_32, x_37);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__2;
x_41 = l_Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(x_1, x_36, x_40, x_39);
lean_dec(x_36);
x_42 = lean_array_fset(x_38, x_32, x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_25);
lean_ctor_set(x_43, 3, x_27);
lean_ctor_set_usize(x_43, 4, x_26);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_10, x_9);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_26 = lean_array_uget(x_8, x_10);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_24);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_26, x_24, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_11, 0, x_31);
lean_ctor_set(x_27, 0, x_11);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_11, 0, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_11);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
lean_dec(x_24);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
lean_inc(x_7);
lean_ctor_set(x_11, 1, x_36);
lean_ctor_set(x_11, 0, x_7);
x_37 = 1;
x_38 = lean_usize_add(x_10, x_37);
x_10 = x_38;
x_20 = x_35;
goto _start;
}
}
else
{
uint8_t x_40; 
lean_free_object(x_11);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_27);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_dec(x_11);
x_45 = lean_array_uget(x_8, x_10);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_44);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_46 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_45, x_44, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
lean_dec(x_44);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
lean_inc(x_7);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_7);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_10, x_56);
x_10 = x_57;
x_11 = x_55;
x_20 = x_53;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_44);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_ctor_get(x_46, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_61 = x_46;
} else {
 lean_dec_ref(x_46);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
x_21 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_19);
x_22 = lean_apply_11(x_1, x_21, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_ctor_set(x_6, 0, x_26);
lean_ctor_set(x_22, 0, x_6);
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
lean_ctor_set(x_6, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
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
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_31);
lean_ctor_set(x_6, 0, x_2);
x_32 = 1;
x_33 = lean_usize_add(x_5, x_32);
x_5 = x_33;
x_15 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_6);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_39);
x_41 = lean_apply_11(x_1, x_40, x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
lean_inc(x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
x_51 = 1;
x_52 = lean_usize_add(x_5, x_51);
x_5 = x_52;
x_6 = x_50;
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_286; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
x_286 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_632_(x_17, x_18);
if (x_286 == 0)
{
uint8_t x_287; 
x_287 = l_Int_Linear_Poly_isNegEq(x_17, x_18);
x_19 = x_287;
goto block_285;
}
else
{
x_19 = x_286;
goto block_285;
}
block_285:
{
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_6, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_6, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_6, 1, x_16);
lean_ctor_set(x_6, 0, x_23);
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_2);
x_26 = lean_st_ref_take(x_8, x_16);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 14);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_26, 1);
x_32 = lean_ctor_get(x_26, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_27, 14);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_28, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_29, 10);
x_39 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_38, x_4);
lean_dec(x_18);
lean_ctor_set(x_29, 10, x_39);
x_40 = lean_st_ref_set(x_8, x_27, x_31);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_44 = l_Int_Linear_Poly_addConst(x_17, x_43);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 13);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_1, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_1, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_6);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_6, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_6, 0);
lean_dec(x_50);
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_44);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_6);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_1, 1, x_5);
lean_ctor_set(x_1, 0, x_52);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_40, 0, x_53);
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_6);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_26);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_1, 1, x_5);
lean_ctor_set(x_1, 0, x_56);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_40, 0, x_57);
return x_40;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_1);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_58 = x_6;
} else {
 lean_dec_ref(x_6);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_26);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_5);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_40, 0, x_63);
return x_40;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_64 = lean_ctor_get(x_40, 1);
lean_inc(x_64);
lean_dec(x_40);
x_65 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_66 = l_Int_Linear_Poly_addConst(x_17, x_65);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 13);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_67 = x_1;
} else {
 lean_dec_ref(x_1);
 x_67 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_68 = x_6;
} else {
 lean_dec_ref(x_6);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_26);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_5);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_64);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_75 = lean_ctor_get(x_29, 0);
x_76 = lean_ctor_get(x_29, 1);
x_77 = lean_ctor_get(x_29, 2);
x_78 = lean_ctor_get(x_29, 3);
x_79 = lean_ctor_get(x_29, 4);
x_80 = lean_ctor_get(x_29, 5);
x_81 = lean_ctor_get(x_29, 6);
x_82 = lean_ctor_get(x_29, 7);
x_83 = lean_ctor_get(x_29, 8);
x_84 = lean_ctor_get(x_29, 9);
x_85 = lean_ctor_get(x_29, 10);
x_86 = lean_ctor_get(x_29, 11);
x_87 = lean_ctor_get(x_29, 12);
x_88 = lean_ctor_get(x_29, 13);
x_89 = lean_ctor_get(x_29, 14);
x_90 = lean_ctor_get(x_29, 15);
x_91 = lean_ctor_get_uint8(x_29, sizeof(void*)*22);
x_92 = lean_ctor_get(x_29, 16);
x_93 = lean_ctor_get(x_29, 17);
x_94 = lean_ctor_get(x_29, 18);
x_95 = lean_ctor_get(x_29, 19);
x_96 = lean_ctor_get(x_29, 20);
x_97 = lean_ctor_get(x_29, 21);
x_98 = lean_ctor_get_uint8(x_29, sizeof(void*)*22 + 1);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
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
lean_dec(x_29);
x_99 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_85, x_4);
lean_dec(x_18);
x_100 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_100, 0, x_75);
lean_ctor_set(x_100, 1, x_76);
lean_ctor_set(x_100, 2, x_77);
lean_ctor_set(x_100, 3, x_78);
lean_ctor_set(x_100, 4, x_79);
lean_ctor_set(x_100, 5, x_80);
lean_ctor_set(x_100, 6, x_81);
lean_ctor_set(x_100, 7, x_82);
lean_ctor_set(x_100, 8, x_83);
lean_ctor_set(x_100, 9, x_84);
lean_ctor_set(x_100, 10, x_99);
lean_ctor_set(x_100, 11, x_86);
lean_ctor_set(x_100, 12, x_87);
lean_ctor_set(x_100, 13, x_88);
lean_ctor_set(x_100, 14, x_89);
lean_ctor_set(x_100, 15, x_90);
lean_ctor_set(x_100, 16, x_92);
lean_ctor_set(x_100, 17, x_93);
lean_ctor_set(x_100, 18, x_94);
lean_ctor_set(x_100, 19, x_95);
lean_ctor_set(x_100, 20, x_96);
lean_ctor_set(x_100, 21, x_97);
lean_ctor_set_uint8(x_100, sizeof(void*)*22, x_91);
lean_ctor_set_uint8(x_100, sizeof(void*)*22 + 1, x_98);
lean_ctor_set(x_28, 1, x_100);
x_101 = lean_st_ref_set(x_8, x_27, x_31);
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
x_104 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_105 = l_Int_Linear_Poly_addConst(x_17, x_104);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 13);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_106 = x_1;
} else {
 lean_dec_ref(x_1);
 x_106 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_107 = x_6;
} else {
 lean_dec_ref(x_6);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_26);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
if (lean_is_scalar(x_106)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_106;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_5);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
if (lean_is_scalar(x_103)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_103;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_102);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_114 = lean_ctor_get(x_28, 0);
x_115 = lean_ctor_get(x_28, 2);
x_116 = lean_ctor_get(x_28, 3);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_28);
x_117 = lean_ctor_get(x_29, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_29, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_29, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_29, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_29, 4);
lean_inc(x_121);
x_122 = lean_ctor_get(x_29, 5);
lean_inc(x_122);
x_123 = lean_ctor_get(x_29, 6);
lean_inc(x_123);
x_124 = lean_ctor_get(x_29, 7);
lean_inc(x_124);
x_125 = lean_ctor_get(x_29, 8);
lean_inc(x_125);
x_126 = lean_ctor_get(x_29, 9);
lean_inc(x_126);
x_127 = lean_ctor_get(x_29, 10);
lean_inc(x_127);
x_128 = lean_ctor_get(x_29, 11);
lean_inc(x_128);
x_129 = lean_ctor_get(x_29, 12);
lean_inc(x_129);
x_130 = lean_ctor_get(x_29, 13);
lean_inc(x_130);
x_131 = lean_ctor_get(x_29, 14);
lean_inc(x_131);
x_132 = lean_ctor_get(x_29, 15);
lean_inc(x_132);
x_133 = lean_ctor_get_uint8(x_29, sizeof(void*)*22);
x_134 = lean_ctor_get(x_29, 16);
lean_inc(x_134);
x_135 = lean_ctor_get(x_29, 17);
lean_inc(x_135);
x_136 = lean_ctor_get(x_29, 18);
lean_inc(x_136);
x_137 = lean_ctor_get(x_29, 19);
lean_inc(x_137);
x_138 = lean_ctor_get(x_29, 20);
lean_inc(x_138);
x_139 = lean_ctor_get(x_29, 21);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_29, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 lean_ctor_release(x_29, 5);
 lean_ctor_release(x_29, 6);
 lean_ctor_release(x_29, 7);
 lean_ctor_release(x_29, 8);
 lean_ctor_release(x_29, 9);
 lean_ctor_release(x_29, 10);
 lean_ctor_release(x_29, 11);
 lean_ctor_release(x_29, 12);
 lean_ctor_release(x_29, 13);
 lean_ctor_release(x_29, 14);
 lean_ctor_release(x_29, 15);
 lean_ctor_release(x_29, 16);
 lean_ctor_release(x_29, 17);
 lean_ctor_release(x_29, 18);
 lean_ctor_release(x_29, 19);
 lean_ctor_release(x_29, 20);
 lean_ctor_release(x_29, 21);
 x_141 = x_29;
} else {
 lean_dec_ref(x_29);
 x_141 = lean_box(0);
}
x_142 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_127, x_4);
lean_dec(x_18);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 22, 2);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_117);
lean_ctor_set(x_143, 1, x_118);
lean_ctor_set(x_143, 2, x_119);
lean_ctor_set(x_143, 3, x_120);
lean_ctor_set(x_143, 4, x_121);
lean_ctor_set(x_143, 5, x_122);
lean_ctor_set(x_143, 6, x_123);
lean_ctor_set(x_143, 7, x_124);
lean_ctor_set(x_143, 8, x_125);
lean_ctor_set(x_143, 9, x_126);
lean_ctor_set(x_143, 10, x_142);
lean_ctor_set(x_143, 11, x_128);
lean_ctor_set(x_143, 12, x_129);
lean_ctor_set(x_143, 13, x_130);
lean_ctor_set(x_143, 14, x_131);
lean_ctor_set(x_143, 15, x_132);
lean_ctor_set(x_143, 16, x_134);
lean_ctor_set(x_143, 17, x_135);
lean_ctor_set(x_143, 18, x_136);
lean_ctor_set(x_143, 19, x_137);
lean_ctor_set(x_143, 20, x_138);
lean_ctor_set(x_143, 21, x_139);
lean_ctor_set_uint8(x_143, sizeof(void*)*22, x_133);
lean_ctor_set_uint8(x_143, sizeof(void*)*22 + 1, x_140);
x_144 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_144, 0, x_114);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_144, 2, x_115);
lean_ctor_set(x_144, 3, x_116);
lean_ctor_set(x_27, 14, x_144);
x_145 = lean_st_ref_set(x_8, x_27, x_31);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
x_148 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_149 = l_Int_Linear_Poly_addConst(x_17, x_148);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 13);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_150 = x_1;
} else {
 lean_dec_ref(x_1);
 x_150 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_151 = x_6;
} else {
 lean_dec_ref(x_6);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_26);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
if (lean_is_scalar(x_150)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_150;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_5);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
if (lean_is_scalar(x_147)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_147;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_146);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_158 = lean_ctor_get(x_27, 0);
x_159 = lean_ctor_get(x_27, 1);
x_160 = lean_ctor_get(x_27, 2);
x_161 = lean_ctor_get(x_27, 3);
x_162 = lean_ctor_get(x_27, 4);
x_163 = lean_ctor_get(x_27, 5);
x_164 = lean_ctor_get(x_27, 6);
x_165 = lean_ctor_get(x_27, 7);
x_166 = lean_ctor_get_uint8(x_27, sizeof(void*)*16);
x_167 = lean_ctor_get(x_27, 8);
x_168 = lean_ctor_get(x_27, 9);
x_169 = lean_ctor_get(x_27, 10);
x_170 = lean_ctor_get(x_27, 11);
x_171 = lean_ctor_get(x_27, 12);
x_172 = lean_ctor_get(x_27, 13);
x_173 = lean_ctor_get(x_27, 15);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_27);
x_174 = lean_ctor_get(x_28, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_28, 2);
lean_inc(x_175);
x_176 = lean_ctor_get(x_28, 3);
lean_inc(x_176);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 x_177 = x_28;
} else {
 lean_dec_ref(x_28);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_29, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_29, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_29, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_29, 3);
lean_inc(x_181);
x_182 = lean_ctor_get(x_29, 4);
lean_inc(x_182);
x_183 = lean_ctor_get(x_29, 5);
lean_inc(x_183);
x_184 = lean_ctor_get(x_29, 6);
lean_inc(x_184);
x_185 = lean_ctor_get(x_29, 7);
lean_inc(x_185);
x_186 = lean_ctor_get(x_29, 8);
lean_inc(x_186);
x_187 = lean_ctor_get(x_29, 9);
lean_inc(x_187);
x_188 = lean_ctor_get(x_29, 10);
lean_inc(x_188);
x_189 = lean_ctor_get(x_29, 11);
lean_inc(x_189);
x_190 = lean_ctor_get(x_29, 12);
lean_inc(x_190);
x_191 = lean_ctor_get(x_29, 13);
lean_inc(x_191);
x_192 = lean_ctor_get(x_29, 14);
lean_inc(x_192);
x_193 = lean_ctor_get(x_29, 15);
lean_inc(x_193);
x_194 = lean_ctor_get_uint8(x_29, sizeof(void*)*22);
x_195 = lean_ctor_get(x_29, 16);
lean_inc(x_195);
x_196 = lean_ctor_get(x_29, 17);
lean_inc(x_196);
x_197 = lean_ctor_get(x_29, 18);
lean_inc(x_197);
x_198 = lean_ctor_get(x_29, 19);
lean_inc(x_198);
x_199 = lean_ctor_get(x_29, 20);
lean_inc(x_199);
x_200 = lean_ctor_get(x_29, 21);
lean_inc(x_200);
x_201 = lean_ctor_get_uint8(x_29, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 lean_ctor_release(x_29, 5);
 lean_ctor_release(x_29, 6);
 lean_ctor_release(x_29, 7);
 lean_ctor_release(x_29, 8);
 lean_ctor_release(x_29, 9);
 lean_ctor_release(x_29, 10);
 lean_ctor_release(x_29, 11);
 lean_ctor_release(x_29, 12);
 lean_ctor_release(x_29, 13);
 lean_ctor_release(x_29, 14);
 lean_ctor_release(x_29, 15);
 lean_ctor_release(x_29, 16);
 lean_ctor_release(x_29, 17);
 lean_ctor_release(x_29, 18);
 lean_ctor_release(x_29, 19);
 lean_ctor_release(x_29, 20);
 lean_ctor_release(x_29, 21);
 x_202 = x_29;
} else {
 lean_dec_ref(x_29);
 x_202 = lean_box(0);
}
x_203 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_188, x_4);
lean_dec(x_18);
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(0, 22, 2);
} else {
 x_204 = x_202;
}
lean_ctor_set(x_204, 0, x_178);
lean_ctor_set(x_204, 1, x_179);
lean_ctor_set(x_204, 2, x_180);
lean_ctor_set(x_204, 3, x_181);
lean_ctor_set(x_204, 4, x_182);
lean_ctor_set(x_204, 5, x_183);
lean_ctor_set(x_204, 6, x_184);
lean_ctor_set(x_204, 7, x_185);
lean_ctor_set(x_204, 8, x_186);
lean_ctor_set(x_204, 9, x_187);
lean_ctor_set(x_204, 10, x_203);
lean_ctor_set(x_204, 11, x_189);
lean_ctor_set(x_204, 12, x_190);
lean_ctor_set(x_204, 13, x_191);
lean_ctor_set(x_204, 14, x_192);
lean_ctor_set(x_204, 15, x_193);
lean_ctor_set(x_204, 16, x_195);
lean_ctor_set(x_204, 17, x_196);
lean_ctor_set(x_204, 18, x_197);
lean_ctor_set(x_204, 19, x_198);
lean_ctor_set(x_204, 20, x_199);
lean_ctor_set(x_204, 21, x_200);
lean_ctor_set_uint8(x_204, sizeof(void*)*22, x_194);
lean_ctor_set_uint8(x_204, sizeof(void*)*22 + 1, x_201);
if (lean_is_scalar(x_177)) {
 x_205 = lean_alloc_ctor(0, 4, 0);
} else {
 x_205 = x_177;
}
lean_ctor_set(x_205, 0, x_174);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_205, 2, x_175);
lean_ctor_set(x_205, 3, x_176);
x_206 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_206, 0, x_158);
lean_ctor_set(x_206, 1, x_159);
lean_ctor_set(x_206, 2, x_160);
lean_ctor_set(x_206, 3, x_161);
lean_ctor_set(x_206, 4, x_162);
lean_ctor_set(x_206, 5, x_163);
lean_ctor_set(x_206, 6, x_164);
lean_ctor_set(x_206, 7, x_165);
lean_ctor_set(x_206, 8, x_167);
lean_ctor_set(x_206, 9, x_168);
lean_ctor_set(x_206, 10, x_169);
lean_ctor_set(x_206, 11, x_170);
lean_ctor_set(x_206, 12, x_171);
lean_ctor_set(x_206, 13, x_172);
lean_ctor_set(x_206, 14, x_205);
lean_ctor_set(x_206, 15, x_173);
lean_ctor_set_uint8(x_206, sizeof(void*)*16, x_166);
x_207 = lean_st_ref_set(x_8, x_206, x_31);
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
x_210 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_211 = l_Int_Linear_Poly_addConst(x_17, x_210);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 13);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_212 = x_1;
} else {
 lean_dec_ref(x_1);
 x_212 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_213 = x_6;
} else {
 lean_dec_ref(x_6);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_26);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
if (lean_is_scalar(x_212)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_212;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_5);
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_217);
if (lean_is_scalar(x_209)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_209;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_208);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_220 = lean_ctor_get(x_26, 1);
lean_inc(x_220);
lean_dec(x_26);
x_221 = lean_ctor_get(x_27, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_27, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_27, 2);
lean_inc(x_223);
x_224 = lean_ctor_get(x_27, 3);
lean_inc(x_224);
x_225 = lean_ctor_get(x_27, 4);
lean_inc(x_225);
x_226 = lean_ctor_get(x_27, 5);
lean_inc(x_226);
x_227 = lean_ctor_get(x_27, 6);
lean_inc(x_227);
x_228 = lean_ctor_get(x_27, 7);
lean_inc(x_228);
x_229 = lean_ctor_get_uint8(x_27, sizeof(void*)*16);
x_230 = lean_ctor_get(x_27, 8);
lean_inc(x_230);
x_231 = lean_ctor_get(x_27, 9);
lean_inc(x_231);
x_232 = lean_ctor_get(x_27, 10);
lean_inc(x_232);
x_233 = lean_ctor_get(x_27, 11);
lean_inc(x_233);
x_234 = lean_ctor_get(x_27, 12);
lean_inc(x_234);
x_235 = lean_ctor_get(x_27, 13);
lean_inc(x_235);
x_236 = lean_ctor_get(x_27, 15);
lean_inc(x_236);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 lean_ctor_release(x_27, 6);
 lean_ctor_release(x_27, 7);
 lean_ctor_release(x_27, 8);
 lean_ctor_release(x_27, 9);
 lean_ctor_release(x_27, 10);
 lean_ctor_release(x_27, 11);
 lean_ctor_release(x_27, 12);
 lean_ctor_release(x_27, 13);
 lean_ctor_release(x_27, 14);
 lean_ctor_release(x_27, 15);
 x_237 = x_27;
} else {
 lean_dec_ref(x_27);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_28, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_28, 2);
lean_inc(x_239);
x_240 = lean_ctor_get(x_28, 3);
lean_inc(x_240);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 x_241 = x_28;
} else {
 lean_dec_ref(x_28);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_29, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_29, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_29, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_29, 3);
lean_inc(x_245);
x_246 = lean_ctor_get(x_29, 4);
lean_inc(x_246);
x_247 = lean_ctor_get(x_29, 5);
lean_inc(x_247);
x_248 = lean_ctor_get(x_29, 6);
lean_inc(x_248);
x_249 = lean_ctor_get(x_29, 7);
lean_inc(x_249);
x_250 = lean_ctor_get(x_29, 8);
lean_inc(x_250);
x_251 = lean_ctor_get(x_29, 9);
lean_inc(x_251);
x_252 = lean_ctor_get(x_29, 10);
lean_inc(x_252);
x_253 = lean_ctor_get(x_29, 11);
lean_inc(x_253);
x_254 = lean_ctor_get(x_29, 12);
lean_inc(x_254);
x_255 = lean_ctor_get(x_29, 13);
lean_inc(x_255);
x_256 = lean_ctor_get(x_29, 14);
lean_inc(x_256);
x_257 = lean_ctor_get(x_29, 15);
lean_inc(x_257);
x_258 = lean_ctor_get_uint8(x_29, sizeof(void*)*22);
x_259 = lean_ctor_get(x_29, 16);
lean_inc(x_259);
x_260 = lean_ctor_get(x_29, 17);
lean_inc(x_260);
x_261 = lean_ctor_get(x_29, 18);
lean_inc(x_261);
x_262 = lean_ctor_get(x_29, 19);
lean_inc(x_262);
x_263 = lean_ctor_get(x_29, 20);
lean_inc(x_263);
x_264 = lean_ctor_get(x_29, 21);
lean_inc(x_264);
x_265 = lean_ctor_get_uint8(x_29, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 lean_ctor_release(x_29, 5);
 lean_ctor_release(x_29, 6);
 lean_ctor_release(x_29, 7);
 lean_ctor_release(x_29, 8);
 lean_ctor_release(x_29, 9);
 lean_ctor_release(x_29, 10);
 lean_ctor_release(x_29, 11);
 lean_ctor_release(x_29, 12);
 lean_ctor_release(x_29, 13);
 lean_ctor_release(x_29, 14);
 lean_ctor_release(x_29, 15);
 lean_ctor_release(x_29, 16);
 lean_ctor_release(x_29, 17);
 lean_ctor_release(x_29, 18);
 lean_ctor_release(x_29, 19);
 lean_ctor_release(x_29, 20);
 lean_ctor_release(x_29, 21);
 x_266 = x_29;
} else {
 lean_dec_ref(x_29);
 x_266 = lean_box(0);
}
x_267 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_252, x_4);
lean_dec(x_18);
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(0, 22, 2);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_242);
lean_ctor_set(x_268, 1, x_243);
lean_ctor_set(x_268, 2, x_244);
lean_ctor_set(x_268, 3, x_245);
lean_ctor_set(x_268, 4, x_246);
lean_ctor_set(x_268, 5, x_247);
lean_ctor_set(x_268, 6, x_248);
lean_ctor_set(x_268, 7, x_249);
lean_ctor_set(x_268, 8, x_250);
lean_ctor_set(x_268, 9, x_251);
lean_ctor_set(x_268, 10, x_267);
lean_ctor_set(x_268, 11, x_253);
lean_ctor_set(x_268, 12, x_254);
lean_ctor_set(x_268, 13, x_255);
lean_ctor_set(x_268, 14, x_256);
lean_ctor_set(x_268, 15, x_257);
lean_ctor_set(x_268, 16, x_259);
lean_ctor_set(x_268, 17, x_260);
lean_ctor_set(x_268, 18, x_261);
lean_ctor_set(x_268, 19, x_262);
lean_ctor_set(x_268, 20, x_263);
lean_ctor_set(x_268, 21, x_264);
lean_ctor_set_uint8(x_268, sizeof(void*)*22, x_258);
lean_ctor_set_uint8(x_268, sizeof(void*)*22 + 1, x_265);
if (lean_is_scalar(x_241)) {
 x_269 = lean_alloc_ctor(0, 4, 0);
} else {
 x_269 = x_241;
}
lean_ctor_set(x_269, 0, x_238);
lean_ctor_set(x_269, 1, x_268);
lean_ctor_set(x_269, 2, x_239);
lean_ctor_set(x_269, 3, x_240);
if (lean_is_scalar(x_237)) {
 x_270 = lean_alloc_ctor(0, 16, 1);
} else {
 x_270 = x_237;
}
lean_ctor_set(x_270, 0, x_221);
lean_ctor_set(x_270, 1, x_222);
lean_ctor_set(x_270, 2, x_223);
lean_ctor_set(x_270, 3, x_224);
lean_ctor_set(x_270, 4, x_225);
lean_ctor_set(x_270, 5, x_226);
lean_ctor_set(x_270, 6, x_227);
lean_ctor_set(x_270, 7, x_228);
lean_ctor_set(x_270, 8, x_230);
lean_ctor_set(x_270, 9, x_231);
lean_ctor_set(x_270, 10, x_232);
lean_ctor_set(x_270, 11, x_233);
lean_ctor_set(x_270, 12, x_234);
lean_ctor_set(x_270, 13, x_235);
lean_ctor_set(x_270, 14, x_269);
lean_ctor_set(x_270, 15, x_236);
lean_ctor_set_uint8(x_270, sizeof(void*)*16, x_229);
x_271 = lean_st_ref_set(x_8, x_270, x_220);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
x_274 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_275 = l_Int_Linear_Poly_addConst(x_17, x_274);
lean_inc(x_6);
lean_inc(x_1);
x_276 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_276, 0, x_1);
lean_ctor_set(x_276, 1, x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_277 = x_1;
} else {
 lean_dec_ref(x_1);
 x_277 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_278 = x_6;
} else {
 lean_dec_ref(x_6);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_275);
lean_ctor_set(x_279, 1, x_276);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_279);
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_280);
if (lean_is_scalar(x_277)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_277;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_5);
x_283 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_283, 0, x_282);
if (lean_is_scalar(x_273)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_273;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_272);
return x_284;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
x_22 = lean_array_size(x_19);
x_23 = 0;
x_24 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_20, x_19, x_22, x_23, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_29);
lean_ctor_set(x_24, 0, x_7);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_25);
lean_free_object(x_7);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_35);
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
lean_dec(x_26);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_free_object(x_7);
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
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_7, 0);
lean_inc(x_43);
lean_dec(x_7);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_8);
x_46 = lean_array_size(x_43);
x_47 = 0;
x_48 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_44, x_43, x_46, x_47, x_45, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_43);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_49);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_57 = x_48;
} else {
 lean_dec_ref(x_48);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_50, 0);
lean_inc(x_58);
lean_dec(x_50);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_48, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_62 = x_48;
} else {
 lean_dec_ref(x_48);
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
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_7);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_7, 0);
x_66 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___boxed), 16, 5);
lean_closure_set(x_66, 0, x_1);
lean_closure_set(x_66, 1, x_2);
lean_closure_set(x_66, 2, x_3);
lean_closure_set(x_66, 3, x_4);
lean_closure_set(x_66, 4, x_5);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_8);
x_69 = lean_array_size(x_65);
x_70 = 0;
x_71 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__8(x_66, x_67, x_65, x_69, x_70, x_68, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_65);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_71);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_71, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
lean_ctor_set(x_7, 0, x_76);
lean_ctor_set(x_71, 0, x_7);
return x_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_dec(x_71);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
lean_ctor_set(x_7, 0, x_78);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_7);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_72);
lean_free_object(x_7);
x_80 = !lean_is_exclusive(x_71);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_71, 0);
lean_dec(x_81);
x_82 = lean_ctor_get(x_73, 0);
lean_inc(x_82);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_82);
return x_71;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_71, 1);
lean_inc(x_83);
lean_dec(x_71);
x_84 = lean_ctor_get(x_73, 0);
lean_inc(x_84);
lean_dec(x_73);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_free_object(x_7);
x_86 = !lean_is_exclusive(x_71);
if (x_86 == 0)
{
return x_71;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_71, 0);
x_88 = lean_ctor_get(x_71, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_71);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; size_t x_94; size_t x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_7, 0);
lean_inc(x_90);
lean_dec(x_7);
x_91 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___boxed), 16, 5);
lean_closure_set(x_91, 0, x_1);
lean_closure_set(x_91, 1, x_2);
lean_closure_set(x_91, 2, x_3);
lean_closure_set(x_91, 3, x_4);
lean_closure_set(x_91, 4, x_5);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_8);
x_94 = lean_array_size(x_90);
x_95 = 0;
x_96 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__8(x_91, x_92, x_90, x_94, x_95, x_93, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_90);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_100 = x_96;
} else {
 lean_dec_ref(x_96);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_dec(x_97);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_99);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_97);
x_104 = lean_ctor_get(x_96, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_105 = x_96;
} else {
 lean_dec_ref(x_96);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_98, 0);
lean_inc(x_106);
lean_dec(x_98);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_96, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_96, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_110 = x_96;
} else {
 lean_dec_ref(x_96);
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
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
x_21 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_19);
x_22 = lean_apply_11(x_1, x_21, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_6, 0, x_23);
lean_ctor_set(x_22, 0, x_6);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_6, 0, x_28);
lean_ctor_set(x_22, 0, x_6);
return x_22;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_31 = x_23;
} else {
 lean_dec_ref(x_23);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_31;
 lean_ctor_set_tag(x_32, 1);
}
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_6, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_19);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_35);
lean_ctor_set(x_6, 0, x_2);
x_36 = 1;
x_37 = lean_usize_add(x_5, x_36);
x_5 = x_37;
x_15 = x_34;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_6);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_43);
x_45 = lean_apply_11(x_1, x_44, x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_50 = x_46;
} else {
 lean_dec_ref(x_46);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_50;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
lean_dec(x_43);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_dec(x_45);
x_55 = lean_ctor_get(x_46, 0);
lean_inc(x_55);
lean_dec(x_46);
lean_inc(x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_5, x_57);
x_5 = x_58;
x_6 = x_56;
x_15 = x_54;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_43);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_ctor_get(x_45, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_45, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_62 = x_45;
} else {
 lean_dec_ref(x_45);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_286; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
x_286 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_632_(x_17, x_18);
if (x_286 == 0)
{
uint8_t x_287; 
x_287 = l_Int_Linear_Poly_isNegEq(x_17, x_18);
x_19 = x_287;
goto block_285;
}
else
{
x_19 = x_286;
goto block_285;
}
block_285:
{
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_6, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_6, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_6, 1, x_16);
lean_ctor_set(x_6, 0, x_23);
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_2);
x_26 = lean_st_ref_take(x_8, x_16);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 14);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_26, 1);
x_32 = lean_ctor_get(x_26, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_27, 14);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_28, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_29, 10);
x_39 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_38, x_4);
lean_dec(x_18);
lean_ctor_set(x_29, 10, x_39);
x_40 = lean_st_ref_set(x_8, x_27, x_31);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_44 = l_Int_Linear_Poly_addConst(x_17, x_43);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 13);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_1, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_1, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_6);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_6, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_6, 0);
lean_dec(x_50);
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_44);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_6);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_1, 1, x_5);
lean_ctor_set(x_1, 0, x_52);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_40, 0, x_53);
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_6);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_26);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_1, 1, x_5);
lean_ctor_set(x_1, 0, x_56);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_40, 0, x_57);
return x_40;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_1);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_58 = x_6;
} else {
 lean_dec_ref(x_6);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_26);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_5);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_40, 0, x_63);
return x_40;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_64 = lean_ctor_get(x_40, 1);
lean_inc(x_64);
lean_dec(x_40);
x_65 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_66 = l_Int_Linear_Poly_addConst(x_17, x_65);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 13);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_67 = x_1;
} else {
 lean_dec_ref(x_1);
 x_67 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_68 = x_6;
} else {
 lean_dec_ref(x_6);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_26);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_5);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_64);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_75 = lean_ctor_get(x_29, 0);
x_76 = lean_ctor_get(x_29, 1);
x_77 = lean_ctor_get(x_29, 2);
x_78 = lean_ctor_get(x_29, 3);
x_79 = lean_ctor_get(x_29, 4);
x_80 = lean_ctor_get(x_29, 5);
x_81 = lean_ctor_get(x_29, 6);
x_82 = lean_ctor_get(x_29, 7);
x_83 = lean_ctor_get(x_29, 8);
x_84 = lean_ctor_get(x_29, 9);
x_85 = lean_ctor_get(x_29, 10);
x_86 = lean_ctor_get(x_29, 11);
x_87 = lean_ctor_get(x_29, 12);
x_88 = lean_ctor_get(x_29, 13);
x_89 = lean_ctor_get(x_29, 14);
x_90 = lean_ctor_get(x_29, 15);
x_91 = lean_ctor_get_uint8(x_29, sizeof(void*)*22);
x_92 = lean_ctor_get(x_29, 16);
x_93 = lean_ctor_get(x_29, 17);
x_94 = lean_ctor_get(x_29, 18);
x_95 = lean_ctor_get(x_29, 19);
x_96 = lean_ctor_get(x_29, 20);
x_97 = lean_ctor_get(x_29, 21);
x_98 = lean_ctor_get_uint8(x_29, sizeof(void*)*22 + 1);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
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
lean_dec(x_29);
x_99 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_85, x_4);
lean_dec(x_18);
x_100 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_100, 0, x_75);
lean_ctor_set(x_100, 1, x_76);
lean_ctor_set(x_100, 2, x_77);
lean_ctor_set(x_100, 3, x_78);
lean_ctor_set(x_100, 4, x_79);
lean_ctor_set(x_100, 5, x_80);
lean_ctor_set(x_100, 6, x_81);
lean_ctor_set(x_100, 7, x_82);
lean_ctor_set(x_100, 8, x_83);
lean_ctor_set(x_100, 9, x_84);
lean_ctor_set(x_100, 10, x_99);
lean_ctor_set(x_100, 11, x_86);
lean_ctor_set(x_100, 12, x_87);
lean_ctor_set(x_100, 13, x_88);
lean_ctor_set(x_100, 14, x_89);
lean_ctor_set(x_100, 15, x_90);
lean_ctor_set(x_100, 16, x_92);
lean_ctor_set(x_100, 17, x_93);
lean_ctor_set(x_100, 18, x_94);
lean_ctor_set(x_100, 19, x_95);
lean_ctor_set(x_100, 20, x_96);
lean_ctor_set(x_100, 21, x_97);
lean_ctor_set_uint8(x_100, sizeof(void*)*22, x_91);
lean_ctor_set_uint8(x_100, sizeof(void*)*22 + 1, x_98);
lean_ctor_set(x_28, 1, x_100);
x_101 = lean_st_ref_set(x_8, x_27, x_31);
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
x_104 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_105 = l_Int_Linear_Poly_addConst(x_17, x_104);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 13);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_106 = x_1;
} else {
 lean_dec_ref(x_1);
 x_106 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_107 = x_6;
} else {
 lean_dec_ref(x_6);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_26);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
if (lean_is_scalar(x_106)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_106;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_5);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
if (lean_is_scalar(x_103)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_103;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_102);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_114 = lean_ctor_get(x_28, 0);
x_115 = lean_ctor_get(x_28, 2);
x_116 = lean_ctor_get(x_28, 3);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_28);
x_117 = lean_ctor_get(x_29, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_29, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_29, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_29, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_29, 4);
lean_inc(x_121);
x_122 = lean_ctor_get(x_29, 5);
lean_inc(x_122);
x_123 = lean_ctor_get(x_29, 6);
lean_inc(x_123);
x_124 = lean_ctor_get(x_29, 7);
lean_inc(x_124);
x_125 = lean_ctor_get(x_29, 8);
lean_inc(x_125);
x_126 = lean_ctor_get(x_29, 9);
lean_inc(x_126);
x_127 = lean_ctor_get(x_29, 10);
lean_inc(x_127);
x_128 = lean_ctor_get(x_29, 11);
lean_inc(x_128);
x_129 = lean_ctor_get(x_29, 12);
lean_inc(x_129);
x_130 = lean_ctor_get(x_29, 13);
lean_inc(x_130);
x_131 = lean_ctor_get(x_29, 14);
lean_inc(x_131);
x_132 = lean_ctor_get(x_29, 15);
lean_inc(x_132);
x_133 = lean_ctor_get_uint8(x_29, sizeof(void*)*22);
x_134 = lean_ctor_get(x_29, 16);
lean_inc(x_134);
x_135 = lean_ctor_get(x_29, 17);
lean_inc(x_135);
x_136 = lean_ctor_get(x_29, 18);
lean_inc(x_136);
x_137 = lean_ctor_get(x_29, 19);
lean_inc(x_137);
x_138 = lean_ctor_get(x_29, 20);
lean_inc(x_138);
x_139 = lean_ctor_get(x_29, 21);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_29, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 lean_ctor_release(x_29, 5);
 lean_ctor_release(x_29, 6);
 lean_ctor_release(x_29, 7);
 lean_ctor_release(x_29, 8);
 lean_ctor_release(x_29, 9);
 lean_ctor_release(x_29, 10);
 lean_ctor_release(x_29, 11);
 lean_ctor_release(x_29, 12);
 lean_ctor_release(x_29, 13);
 lean_ctor_release(x_29, 14);
 lean_ctor_release(x_29, 15);
 lean_ctor_release(x_29, 16);
 lean_ctor_release(x_29, 17);
 lean_ctor_release(x_29, 18);
 lean_ctor_release(x_29, 19);
 lean_ctor_release(x_29, 20);
 lean_ctor_release(x_29, 21);
 x_141 = x_29;
} else {
 lean_dec_ref(x_29);
 x_141 = lean_box(0);
}
x_142 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_127, x_4);
lean_dec(x_18);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 22, 2);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_117);
lean_ctor_set(x_143, 1, x_118);
lean_ctor_set(x_143, 2, x_119);
lean_ctor_set(x_143, 3, x_120);
lean_ctor_set(x_143, 4, x_121);
lean_ctor_set(x_143, 5, x_122);
lean_ctor_set(x_143, 6, x_123);
lean_ctor_set(x_143, 7, x_124);
lean_ctor_set(x_143, 8, x_125);
lean_ctor_set(x_143, 9, x_126);
lean_ctor_set(x_143, 10, x_142);
lean_ctor_set(x_143, 11, x_128);
lean_ctor_set(x_143, 12, x_129);
lean_ctor_set(x_143, 13, x_130);
lean_ctor_set(x_143, 14, x_131);
lean_ctor_set(x_143, 15, x_132);
lean_ctor_set(x_143, 16, x_134);
lean_ctor_set(x_143, 17, x_135);
lean_ctor_set(x_143, 18, x_136);
lean_ctor_set(x_143, 19, x_137);
lean_ctor_set(x_143, 20, x_138);
lean_ctor_set(x_143, 21, x_139);
lean_ctor_set_uint8(x_143, sizeof(void*)*22, x_133);
lean_ctor_set_uint8(x_143, sizeof(void*)*22 + 1, x_140);
x_144 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_144, 0, x_114);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_144, 2, x_115);
lean_ctor_set(x_144, 3, x_116);
lean_ctor_set(x_27, 14, x_144);
x_145 = lean_st_ref_set(x_8, x_27, x_31);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
x_148 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_149 = l_Int_Linear_Poly_addConst(x_17, x_148);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 13);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_150 = x_1;
} else {
 lean_dec_ref(x_1);
 x_150 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_151 = x_6;
} else {
 lean_dec_ref(x_6);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_26);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
if (lean_is_scalar(x_150)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_150;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_5);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
if (lean_is_scalar(x_147)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_147;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_146);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_158 = lean_ctor_get(x_27, 0);
x_159 = lean_ctor_get(x_27, 1);
x_160 = lean_ctor_get(x_27, 2);
x_161 = lean_ctor_get(x_27, 3);
x_162 = lean_ctor_get(x_27, 4);
x_163 = lean_ctor_get(x_27, 5);
x_164 = lean_ctor_get(x_27, 6);
x_165 = lean_ctor_get(x_27, 7);
x_166 = lean_ctor_get_uint8(x_27, sizeof(void*)*16);
x_167 = lean_ctor_get(x_27, 8);
x_168 = lean_ctor_get(x_27, 9);
x_169 = lean_ctor_get(x_27, 10);
x_170 = lean_ctor_get(x_27, 11);
x_171 = lean_ctor_get(x_27, 12);
x_172 = lean_ctor_get(x_27, 13);
x_173 = lean_ctor_get(x_27, 15);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_27);
x_174 = lean_ctor_get(x_28, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_28, 2);
lean_inc(x_175);
x_176 = lean_ctor_get(x_28, 3);
lean_inc(x_176);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 x_177 = x_28;
} else {
 lean_dec_ref(x_28);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_29, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_29, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_29, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_29, 3);
lean_inc(x_181);
x_182 = lean_ctor_get(x_29, 4);
lean_inc(x_182);
x_183 = lean_ctor_get(x_29, 5);
lean_inc(x_183);
x_184 = lean_ctor_get(x_29, 6);
lean_inc(x_184);
x_185 = lean_ctor_get(x_29, 7);
lean_inc(x_185);
x_186 = lean_ctor_get(x_29, 8);
lean_inc(x_186);
x_187 = lean_ctor_get(x_29, 9);
lean_inc(x_187);
x_188 = lean_ctor_get(x_29, 10);
lean_inc(x_188);
x_189 = lean_ctor_get(x_29, 11);
lean_inc(x_189);
x_190 = lean_ctor_get(x_29, 12);
lean_inc(x_190);
x_191 = lean_ctor_get(x_29, 13);
lean_inc(x_191);
x_192 = lean_ctor_get(x_29, 14);
lean_inc(x_192);
x_193 = lean_ctor_get(x_29, 15);
lean_inc(x_193);
x_194 = lean_ctor_get_uint8(x_29, sizeof(void*)*22);
x_195 = lean_ctor_get(x_29, 16);
lean_inc(x_195);
x_196 = lean_ctor_get(x_29, 17);
lean_inc(x_196);
x_197 = lean_ctor_get(x_29, 18);
lean_inc(x_197);
x_198 = lean_ctor_get(x_29, 19);
lean_inc(x_198);
x_199 = lean_ctor_get(x_29, 20);
lean_inc(x_199);
x_200 = lean_ctor_get(x_29, 21);
lean_inc(x_200);
x_201 = lean_ctor_get_uint8(x_29, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 lean_ctor_release(x_29, 5);
 lean_ctor_release(x_29, 6);
 lean_ctor_release(x_29, 7);
 lean_ctor_release(x_29, 8);
 lean_ctor_release(x_29, 9);
 lean_ctor_release(x_29, 10);
 lean_ctor_release(x_29, 11);
 lean_ctor_release(x_29, 12);
 lean_ctor_release(x_29, 13);
 lean_ctor_release(x_29, 14);
 lean_ctor_release(x_29, 15);
 lean_ctor_release(x_29, 16);
 lean_ctor_release(x_29, 17);
 lean_ctor_release(x_29, 18);
 lean_ctor_release(x_29, 19);
 lean_ctor_release(x_29, 20);
 lean_ctor_release(x_29, 21);
 x_202 = x_29;
} else {
 lean_dec_ref(x_29);
 x_202 = lean_box(0);
}
x_203 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_188, x_4);
lean_dec(x_18);
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(0, 22, 2);
} else {
 x_204 = x_202;
}
lean_ctor_set(x_204, 0, x_178);
lean_ctor_set(x_204, 1, x_179);
lean_ctor_set(x_204, 2, x_180);
lean_ctor_set(x_204, 3, x_181);
lean_ctor_set(x_204, 4, x_182);
lean_ctor_set(x_204, 5, x_183);
lean_ctor_set(x_204, 6, x_184);
lean_ctor_set(x_204, 7, x_185);
lean_ctor_set(x_204, 8, x_186);
lean_ctor_set(x_204, 9, x_187);
lean_ctor_set(x_204, 10, x_203);
lean_ctor_set(x_204, 11, x_189);
lean_ctor_set(x_204, 12, x_190);
lean_ctor_set(x_204, 13, x_191);
lean_ctor_set(x_204, 14, x_192);
lean_ctor_set(x_204, 15, x_193);
lean_ctor_set(x_204, 16, x_195);
lean_ctor_set(x_204, 17, x_196);
lean_ctor_set(x_204, 18, x_197);
lean_ctor_set(x_204, 19, x_198);
lean_ctor_set(x_204, 20, x_199);
lean_ctor_set(x_204, 21, x_200);
lean_ctor_set_uint8(x_204, sizeof(void*)*22, x_194);
lean_ctor_set_uint8(x_204, sizeof(void*)*22 + 1, x_201);
if (lean_is_scalar(x_177)) {
 x_205 = lean_alloc_ctor(0, 4, 0);
} else {
 x_205 = x_177;
}
lean_ctor_set(x_205, 0, x_174);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_205, 2, x_175);
lean_ctor_set(x_205, 3, x_176);
x_206 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_206, 0, x_158);
lean_ctor_set(x_206, 1, x_159);
lean_ctor_set(x_206, 2, x_160);
lean_ctor_set(x_206, 3, x_161);
lean_ctor_set(x_206, 4, x_162);
lean_ctor_set(x_206, 5, x_163);
lean_ctor_set(x_206, 6, x_164);
lean_ctor_set(x_206, 7, x_165);
lean_ctor_set(x_206, 8, x_167);
lean_ctor_set(x_206, 9, x_168);
lean_ctor_set(x_206, 10, x_169);
lean_ctor_set(x_206, 11, x_170);
lean_ctor_set(x_206, 12, x_171);
lean_ctor_set(x_206, 13, x_172);
lean_ctor_set(x_206, 14, x_205);
lean_ctor_set(x_206, 15, x_173);
lean_ctor_set_uint8(x_206, sizeof(void*)*16, x_166);
x_207 = lean_st_ref_set(x_8, x_206, x_31);
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
x_210 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_211 = l_Int_Linear_Poly_addConst(x_17, x_210);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 13);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_212 = x_1;
} else {
 lean_dec_ref(x_1);
 x_212 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_213 = x_6;
} else {
 lean_dec_ref(x_6);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_26);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
if (lean_is_scalar(x_212)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_212;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_5);
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_217);
if (lean_is_scalar(x_209)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_209;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_208);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_220 = lean_ctor_get(x_26, 1);
lean_inc(x_220);
lean_dec(x_26);
x_221 = lean_ctor_get(x_27, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_27, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_27, 2);
lean_inc(x_223);
x_224 = lean_ctor_get(x_27, 3);
lean_inc(x_224);
x_225 = lean_ctor_get(x_27, 4);
lean_inc(x_225);
x_226 = lean_ctor_get(x_27, 5);
lean_inc(x_226);
x_227 = lean_ctor_get(x_27, 6);
lean_inc(x_227);
x_228 = lean_ctor_get(x_27, 7);
lean_inc(x_228);
x_229 = lean_ctor_get_uint8(x_27, sizeof(void*)*16);
x_230 = lean_ctor_get(x_27, 8);
lean_inc(x_230);
x_231 = lean_ctor_get(x_27, 9);
lean_inc(x_231);
x_232 = lean_ctor_get(x_27, 10);
lean_inc(x_232);
x_233 = lean_ctor_get(x_27, 11);
lean_inc(x_233);
x_234 = lean_ctor_get(x_27, 12);
lean_inc(x_234);
x_235 = lean_ctor_get(x_27, 13);
lean_inc(x_235);
x_236 = lean_ctor_get(x_27, 15);
lean_inc(x_236);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 lean_ctor_release(x_27, 6);
 lean_ctor_release(x_27, 7);
 lean_ctor_release(x_27, 8);
 lean_ctor_release(x_27, 9);
 lean_ctor_release(x_27, 10);
 lean_ctor_release(x_27, 11);
 lean_ctor_release(x_27, 12);
 lean_ctor_release(x_27, 13);
 lean_ctor_release(x_27, 14);
 lean_ctor_release(x_27, 15);
 x_237 = x_27;
} else {
 lean_dec_ref(x_27);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_28, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_28, 2);
lean_inc(x_239);
x_240 = lean_ctor_get(x_28, 3);
lean_inc(x_240);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 x_241 = x_28;
} else {
 lean_dec_ref(x_28);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_29, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_29, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_29, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_29, 3);
lean_inc(x_245);
x_246 = lean_ctor_get(x_29, 4);
lean_inc(x_246);
x_247 = lean_ctor_get(x_29, 5);
lean_inc(x_247);
x_248 = lean_ctor_get(x_29, 6);
lean_inc(x_248);
x_249 = lean_ctor_get(x_29, 7);
lean_inc(x_249);
x_250 = lean_ctor_get(x_29, 8);
lean_inc(x_250);
x_251 = lean_ctor_get(x_29, 9);
lean_inc(x_251);
x_252 = lean_ctor_get(x_29, 10);
lean_inc(x_252);
x_253 = lean_ctor_get(x_29, 11);
lean_inc(x_253);
x_254 = lean_ctor_get(x_29, 12);
lean_inc(x_254);
x_255 = lean_ctor_get(x_29, 13);
lean_inc(x_255);
x_256 = lean_ctor_get(x_29, 14);
lean_inc(x_256);
x_257 = lean_ctor_get(x_29, 15);
lean_inc(x_257);
x_258 = lean_ctor_get_uint8(x_29, sizeof(void*)*22);
x_259 = lean_ctor_get(x_29, 16);
lean_inc(x_259);
x_260 = lean_ctor_get(x_29, 17);
lean_inc(x_260);
x_261 = lean_ctor_get(x_29, 18);
lean_inc(x_261);
x_262 = lean_ctor_get(x_29, 19);
lean_inc(x_262);
x_263 = lean_ctor_get(x_29, 20);
lean_inc(x_263);
x_264 = lean_ctor_get(x_29, 21);
lean_inc(x_264);
x_265 = lean_ctor_get_uint8(x_29, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 lean_ctor_release(x_29, 5);
 lean_ctor_release(x_29, 6);
 lean_ctor_release(x_29, 7);
 lean_ctor_release(x_29, 8);
 lean_ctor_release(x_29, 9);
 lean_ctor_release(x_29, 10);
 lean_ctor_release(x_29, 11);
 lean_ctor_release(x_29, 12);
 lean_ctor_release(x_29, 13);
 lean_ctor_release(x_29, 14);
 lean_ctor_release(x_29, 15);
 lean_ctor_release(x_29, 16);
 lean_ctor_release(x_29, 17);
 lean_ctor_release(x_29, 18);
 lean_ctor_release(x_29, 19);
 lean_ctor_release(x_29, 20);
 lean_ctor_release(x_29, 21);
 x_266 = x_29;
} else {
 lean_dec_ref(x_29);
 x_266 = lean_box(0);
}
x_267 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_252, x_4);
lean_dec(x_18);
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(0, 22, 2);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_242);
lean_ctor_set(x_268, 1, x_243);
lean_ctor_set(x_268, 2, x_244);
lean_ctor_set(x_268, 3, x_245);
lean_ctor_set(x_268, 4, x_246);
lean_ctor_set(x_268, 5, x_247);
lean_ctor_set(x_268, 6, x_248);
lean_ctor_set(x_268, 7, x_249);
lean_ctor_set(x_268, 8, x_250);
lean_ctor_set(x_268, 9, x_251);
lean_ctor_set(x_268, 10, x_267);
lean_ctor_set(x_268, 11, x_253);
lean_ctor_set(x_268, 12, x_254);
lean_ctor_set(x_268, 13, x_255);
lean_ctor_set(x_268, 14, x_256);
lean_ctor_set(x_268, 15, x_257);
lean_ctor_set(x_268, 16, x_259);
lean_ctor_set(x_268, 17, x_260);
lean_ctor_set(x_268, 18, x_261);
lean_ctor_set(x_268, 19, x_262);
lean_ctor_set(x_268, 20, x_263);
lean_ctor_set(x_268, 21, x_264);
lean_ctor_set_uint8(x_268, sizeof(void*)*22, x_258);
lean_ctor_set_uint8(x_268, sizeof(void*)*22 + 1, x_265);
if (lean_is_scalar(x_241)) {
 x_269 = lean_alloc_ctor(0, 4, 0);
} else {
 x_269 = x_241;
}
lean_ctor_set(x_269, 0, x_238);
lean_ctor_set(x_269, 1, x_268);
lean_ctor_set(x_269, 2, x_239);
lean_ctor_set(x_269, 3, x_240);
if (lean_is_scalar(x_237)) {
 x_270 = lean_alloc_ctor(0, 16, 1);
} else {
 x_270 = x_237;
}
lean_ctor_set(x_270, 0, x_221);
lean_ctor_set(x_270, 1, x_222);
lean_ctor_set(x_270, 2, x_223);
lean_ctor_set(x_270, 3, x_224);
lean_ctor_set(x_270, 4, x_225);
lean_ctor_set(x_270, 5, x_226);
lean_ctor_set(x_270, 6, x_227);
lean_ctor_set(x_270, 7, x_228);
lean_ctor_set(x_270, 8, x_230);
lean_ctor_set(x_270, 9, x_231);
lean_ctor_set(x_270, 10, x_232);
lean_ctor_set(x_270, 11, x_233);
lean_ctor_set(x_270, 12, x_234);
lean_ctor_set(x_270, 13, x_235);
lean_ctor_set(x_270, 14, x_269);
lean_ctor_set(x_270, 15, x_236);
lean_ctor_set_uint8(x_270, sizeof(void*)*16, x_229);
x_271 = lean_st_ref_set(x_8, x_270, x_220);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
x_274 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_275 = l_Int_Linear_Poly_addConst(x_17, x_274);
lean_inc(x_6);
lean_inc(x_1);
x_276 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_276, 0, x_1);
lean_ctor_set(x_276, 1, x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_277 = x_1;
} else {
 lean_dec_ref(x_1);
 x_277 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_278 = x_6;
} else {
 lean_dec_ref(x_6);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_275);
lean_ctor_set(x_279, 1, x_276);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_279);
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_280);
if (lean_is_scalar(x_277)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_277;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_5);
x_283 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_283, 0, x_282);
if (lean_is_scalar(x_273)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_273;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_272);
return x_284;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_7, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7___lam__0___boxed), 16, 5);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_3);
lean_closure_set(x_29, 3, x_4);
lean_closure_set(x_29, 4, x_5);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_array_size(x_18);
x_33 = 0;
x_34 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__10(x_29, x_30, x_18, x_32, x_33, x_31, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_27);
lean_dec(x_18);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_35);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_34, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_45);
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_dec(x_34);
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
lean_dec(x_36);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
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
uint8_t x_53; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArray(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___closed__1() {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_41; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 10);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___closed__0;
x_41 = lean_nat_dec_lt(x_1, x_16);
lean_dec(x_16);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_14);
x_42 = l_outOfBounds___redArg(x_17);
x_18 = x_42;
goto block_40;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_PersistentArray_get_x21___redArg(x_17, x_14, x_1);
x_18 = x_43;
goto block_40;
}
block_40:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___closed__1;
x_21 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7(x_2, x_20, x_17, x_1, x_19, x_18, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
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
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_21, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg(x_1, x_2, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__7___boxed(lean_object** _args) {
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
x_21 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_22 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_23 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21, x_22, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_8);
lean_dec(x_6);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__8(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___boxed(lean_object** _args) {
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
x_18 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__10(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
lean_inc(x_1);
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
lean_inc(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_3, 0, x_20);
lean_ctor_set(x_16, 0, x_3);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
lean_inc(x_14);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_3, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
lean_inc(x_2);
lean_ctor_set(x_3, 1, x_25);
lean_ctor_set(x_3, 0, x_2);
x_12 = x_24;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_3);
lean_dec(x_14);
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
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_dec(x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_31);
lean_inc(x_1);
x_32 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(x_1, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
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
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
lean_inc(x_31);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec(x_33);
lean_inc(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
x_3 = x_41;
x_12 = x_39;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_31);
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
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_45 = x_32;
} else {
 lean_dec_ref(x_32);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(x_13, x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_17);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_27);
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_10; 
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
x_21 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(x_1, x_18, x_15, x_17);
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
x_32 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(x_1, x_29, x_26, x_28);
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
lean_inc(x_35);
x_36 = lean_usize_to_nat(x_3);
x_37 = lean_array_get_size(x_35);
x_38 = lean_nat_dec_lt(x_36, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_39; 
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(x_1, x_6, x_11, x_8);
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
x_28 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(x_1, x_21, x_27, x_24);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_331 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_unbox(x_332);
lean_dec(x_332);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; 
x_334 = lean_ctor_get(x_331, 1);
lean_inc(x_334);
lean_dec(x_331);
x_473 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7;
x_474 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_473, x_8, x_334);
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_unbox(x_475);
lean_dec(x_475);
if (x_476 == 0)
{
lean_object* x_477; 
x_477 = lean_ctor_get(x_474, 1);
lean_inc(x_477);
lean_dec(x_474);
x_335 = x_2;
x_336 = x_3;
x_337 = x_4;
x_338 = x_5;
x_339 = x_6;
x_340 = x_7;
x_341 = x_8;
x_342 = x_9;
x_343 = x_477;
goto block_472;
}
else
{
uint8_t x_478; 
x_478 = !lean_is_exclusive(x_474);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; 
x_479 = lean_ctor_get(x_474, 1);
x_480 = lean_ctor_get(x_474, 0);
lean_dec(x_480);
lean_inc(x_1);
x_481 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_1, x_2, x_479);
x_482 = !lean_is_exclusive(x_481);
if (x_482 == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_483 = lean_ctor_get(x_481, 0);
x_484 = lean_ctor_get(x_481, 1);
x_485 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
lean_ctor_set_tag(x_481, 7);
lean_ctor_set(x_481, 1, x_483);
lean_ctor_set(x_481, 0, x_485);
lean_ctor_set_tag(x_474, 7);
lean_ctor_set(x_474, 1, x_485);
lean_ctor_set(x_474, 0, x_481);
x_486 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_473, x_474, x_6, x_7, x_8, x_9, x_484);
x_487 = lean_ctor_get(x_486, 1);
lean_inc(x_487);
lean_dec(x_486);
x_335 = x_2;
x_336 = x_3;
x_337 = x_4;
x_338 = x_5;
x_339 = x_6;
x_340 = x_7;
x_341 = x_8;
x_342 = x_9;
x_343 = x_487;
goto block_472;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_488 = lean_ctor_get(x_481, 0);
x_489 = lean_ctor_get(x_481, 1);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_481);
x_490 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_491 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_488);
lean_ctor_set_tag(x_474, 7);
lean_ctor_set(x_474, 1, x_490);
lean_ctor_set(x_474, 0, x_491);
x_492 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_473, x_474, x_6, x_7, x_8, x_9, x_489);
x_493 = lean_ctor_get(x_492, 1);
lean_inc(x_493);
lean_dec(x_492);
x_335 = x_2;
x_336 = x_3;
x_337 = x_4;
x_338 = x_5;
x_339 = x_6;
x_340 = x_7;
x_341 = x_8;
x_342 = x_9;
x_343 = x_493;
goto block_472;
}
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_494 = lean_ctor_get(x_474, 1);
lean_inc(x_494);
lean_dec(x_474);
lean_inc(x_1);
x_495 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_1, x_2, x_494);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_498 = x_495;
} else {
 lean_dec_ref(x_495);
 x_498 = lean_box(0);
}
x_499 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
if (lean_is_scalar(x_498)) {
 x_500 = lean_alloc_ctor(7, 2, 0);
} else {
 x_500 = x_498;
 lean_ctor_set_tag(x_500, 7);
}
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_496);
x_501 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_501, 0, x_500);
lean_ctor_set(x_501, 1, x_499);
x_502 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_473, x_501, x_6, x_7, x_8, x_9, x_497);
x_503 = lean_ctor_get(x_502, 1);
lean_inc(x_503);
lean_dec(x_502);
x_335 = x_2;
x_336 = x_3;
x_337 = x_4;
x_338 = x_5;
x_339 = x_6;
x_340 = x_7;
x_341 = x_8;
x_342 = x_9;
x_343 = x_503;
goto block_472;
}
}
block_472:
{
lean_object* x_344; lean_object* x_345; 
x_344 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(x_1);
lean_inc(x_341);
x_345 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___redArg(x_344, x_335, x_339, x_340, x_341, x_342, x_343);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_ctor_get(x_346, 0);
lean_inc(x_348);
x_349 = l_Int_Linear_Poly_isUnsatLe(x_348);
if (x_349 == 0)
{
uint8_t x_350; 
x_350 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(x_346);
if (x_350 == 0)
{
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_351; 
lean_dec(x_348);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
x_351 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(x_346, x_335, x_339, x_340, x_341, x_342, x_347);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_348, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_348, 1);
lean_inc(x_353);
lean_dec(x_348);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_346);
x_354 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(x_346, x_335, x_336, x_337, x_338, x_339, x_340, x_341, x_342, x_347);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; uint8_t x_356; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_unbox(x_355);
lean_dec(x_355);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_ctor_get(x_354, 1);
lean_inc(x_357);
lean_dec(x_354);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_335);
x_358 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(x_346, x_335, x_336, x_337, x_338, x_339, x_340, x_341, x_342, x_357);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_361 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2;
x_362 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_361, x_341, x_360);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_unbox(x_363);
lean_dec(x_363);
if (x_364 == 0)
{
lean_object* x_365; 
x_365 = lean_ctor_get(x_362, 1);
lean_inc(x_365);
lean_dec(x_362);
x_56 = x_352;
x_57 = x_359;
x_58 = x_353;
x_59 = x_335;
x_60 = x_339;
x_61 = x_340;
x_62 = x_341;
x_63 = x_342;
x_64 = x_365;
goto block_330;
}
else
{
uint8_t x_366; 
x_366 = !lean_is_exclusive(x_362);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; 
x_367 = lean_ctor_get(x_362, 1);
x_368 = lean_ctor_get(x_362, 0);
lean_dec(x_368);
lean_inc(x_359);
x_369 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_359, x_335, x_367);
x_370 = !lean_is_exclusive(x_369);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_371 = lean_ctor_get(x_369, 0);
x_372 = lean_ctor_get(x_369, 1);
x_373 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
lean_ctor_set_tag(x_369, 7);
lean_ctor_set(x_369, 1, x_371);
lean_ctor_set(x_369, 0, x_373);
lean_ctor_set_tag(x_362, 7);
lean_ctor_set(x_362, 1, x_373);
lean_ctor_set(x_362, 0, x_369);
x_374 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_361, x_362, x_339, x_340, x_341, x_342, x_372);
x_375 = lean_ctor_get(x_374, 1);
lean_inc(x_375);
lean_dec(x_374);
x_56 = x_352;
x_57 = x_359;
x_58 = x_353;
x_59 = x_335;
x_60 = x_339;
x_61 = x_340;
x_62 = x_341;
x_63 = x_342;
x_64 = x_375;
goto block_330;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_376 = lean_ctor_get(x_369, 0);
x_377 = lean_ctor_get(x_369, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_369);
x_378 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_379 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_376);
lean_ctor_set_tag(x_362, 7);
lean_ctor_set(x_362, 1, x_378);
lean_ctor_set(x_362, 0, x_379);
x_380 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_361, x_362, x_339, x_340, x_341, x_342, x_377);
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
lean_dec(x_380);
x_56 = x_352;
x_57 = x_359;
x_58 = x_353;
x_59 = x_335;
x_60 = x_339;
x_61 = x_340;
x_62 = x_341;
x_63 = x_342;
x_64 = x_381;
goto block_330;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_382 = lean_ctor_get(x_362, 1);
lean_inc(x_382);
lean_dec(x_362);
lean_inc(x_359);
x_383 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_359, x_335, x_382);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_386 = x_383;
} else {
 lean_dec_ref(x_383);
 x_386 = lean_box(0);
}
x_387 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
if (lean_is_scalar(x_386)) {
 x_388 = lean_alloc_ctor(7, 2, 0);
} else {
 x_388 = x_386;
 lean_ctor_set_tag(x_388, 7);
}
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_384);
x_389 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_387);
x_390 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_361, x_389, x_339, x_340, x_341, x_342, x_385);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
lean_dec(x_390);
x_56 = x_352;
x_57 = x_359;
x_58 = x_353;
x_59 = x_335;
x_60 = x_339;
x_61 = x_340;
x_62 = x_341;
x_63 = x_342;
x_64 = x_391;
goto block_330;
}
}
}
else
{
uint8_t x_392; 
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
x_392 = !lean_is_exclusive(x_358);
if (x_392 == 0)
{
return x_358;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_358, 0);
x_394 = lean_ctor_get(x_358, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_358);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
return x_395;
}
}
}
else
{
uint8_t x_396; 
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_346);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
x_396 = !lean_is_exclusive(x_354);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; 
x_397 = lean_ctor_get(x_354, 0);
lean_dec(x_397);
x_398 = lean_box(0);
lean_ctor_set(x_354, 0, x_398);
return x_354;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_354, 1);
lean_inc(x_399);
lean_dec(x_354);
x_400 = lean_box(0);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
}
}
else
{
uint8_t x_402; 
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_346);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
x_402 = !lean_is_exclusive(x_354);
if (x_402 == 0)
{
return x_354;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_403 = lean_ctor_get(x_354, 0);
x_404 = lean_ctor_get(x_354, 1);
lean_inc(x_404);
lean_inc(x_403);
lean_dec(x_354);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set(x_405, 1, x_404);
return x_405;
}
}
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
lean_dec(x_348);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
x_406 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4;
x_407 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_406, x_341, x_347);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_unbox(x_408);
lean_dec(x_408);
if (x_409 == 0)
{
lean_object* x_410; 
lean_dec(x_346);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
x_410 = lean_ctor_get(x_407, 1);
lean_inc(x_410);
lean_dec(x_407);
x_11 = x_410;
goto block_14;
}
else
{
uint8_t x_411; 
x_411 = !lean_is_exclusive(x_407);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_412 = lean_ctor_get(x_407, 1);
x_413 = lean_ctor_get(x_407, 0);
lean_dec(x_413);
x_414 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_346, x_335, x_412);
lean_dec(x_335);
x_415 = !lean_is_exclusive(x_414);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_416 = lean_ctor_get(x_414, 0);
x_417 = lean_ctor_get(x_414, 1);
x_418 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
lean_ctor_set_tag(x_414, 7);
lean_ctor_set(x_414, 1, x_416);
lean_ctor_set(x_414, 0, x_418);
lean_ctor_set_tag(x_407, 7);
lean_ctor_set(x_407, 1, x_418);
lean_ctor_set(x_407, 0, x_414);
x_419 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_406, x_407, x_339, x_340, x_341, x_342, x_417);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec(x_419);
x_11 = x_420;
goto block_14;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_421 = lean_ctor_get(x_414, 0);
x_422 = lean_ctor_get(x_414, 1);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_414);
x_423 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_424 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_421);
lean_ctor_set_tag(x_407, 7);
lean_ctor_set(x_407, 1, x_423);
lean_ctor_set(x_407, 0, x_424);
x_425 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_406, x_407, x_339, x_340, x_341, x_342, x_422);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
lean_dec(x_425);
x_11 = x_426;
goto block_14;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_427 = lean_ctor_get(x_407, 1);
lean_inc(x_427);
lean_dec(x_407);
x_428 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_346, x_335, x_427);
lean_dec(x_335);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_431 = x_428;
} else {
 lean_dec_ref(x_428);
 x_431 = lean_box(0);
}
x_432 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
if (lean_is_scalar(x_431)) {
 x_433 = lean_alloc_ctor(7, 2, 0);
} else {
 x_433 = x_431;
 lean_ctor_set_tag(x_433, 7);
}
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_429);
x_434 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_432);
x_435 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_406, x_434, x_339, x_340, x_341, x_342, x_430);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
x_436 = lean_ctor_get(x_435, 1);
lean_inc(x_436);
lean_dec(x_435);
x_11 = x_436;
goto block_14;
}
}
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; 
lean_dec(x_348);
x_437 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6;
x_438 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_437, x_341, x_347);
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_unbox(x_439);
lean_dec(x_439);
if (x_440 == 0)
{
lean_object* x_441; 
x_441 = lean_ctor_get(x_438, 1);
lean_inc(x_441);
lean_dec(x_438);
x_15 = x_346;
x_16 = x_335;
x_17 = x_336;
x_18 = x_337;
x_19 = x_338;
x_20 = x_339;
x_21 = x_340;
x_22 = x_341;
x_23 = x_342;
x_24 = x_441;
goto block_33;
}
else
{
uint8_t x_442; 
x_442 = !lean_is_exclusive(x_438);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; 
x_443 = lean_ctor_get(x_438, 1);
x_444 = lean_ctor_get(x_438, 0);
lean_dec(x_444);
lean_inc(x_346);
x_445 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_346, x_335, x_443);
x_446 = !lean_is_exclusive(x_445);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_447 = lean_ctor_get(x_445, 0);
x_448 = lean_ctor_get(x_445, 1);
x_449 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
lean_ctor_set_tag(x_445, 7);
lean_ctor_set(x_445, 1, x_447);
lean_ctor_set(x_445, 0, x_449);
lean_ctor_set_tag(x_438, 7);
lean_ctor_set(x_438, 1, x_449);
lean_ctor_set(x_438, 0, x_445);
x_450 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_437, x_438, x_339, x_340, x_341, x_342, x_448);
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
lean_dec(x_450);
x_15 = x_346;
x_16 = x_335;
x_17 = x_336;
x_18 = x_337;
x_19 = x_338;
x_20 = x_339;
x_21 = x_340;
x_22 = x_341;
x_23 = x_342;
x_24 = x_451;
goto block_33;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_452 = lean_ctor_get(x_445, 0);
x_453 = lean_ctor_get(x_445, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_445);
x_454 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_455 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_452);
lean_ctor_set_tag(x_438, 7);
lean_ctor_set(x_438, 1, x_454);
lean_ctor_set(x_438, 0, x_455);
x_456 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_437, x_438, x_339, x_340, x_341, x_342, x_453);
x_457 = lean_ctor_get(x_456, 1);
lean_inc(x_457);
lean_dec(x_456);
x_15 = x_346;
x_16 = x_335;
x_17 = x_336;
x_18 = x_337;
x_19 = x_338;
x_20 = x_339;
x_21 = x_340;
x_22 = x_341;
x_23 = x_342;
x_24 = x_457;
goto block_33;
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_458 = lean_ctor_get(x_438, 1);
lean_inc(x_458);
lean_dec(x_438);
lean_inc(x_346);
x_459 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_346, x_335, x_458);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_462 = x_459;
} else {
 lean_dec_ref(x_459);
 x_462 = lean_box(0);
}
x_463 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
if (lean_is_scalar(x_462)) {
 x_464 = lean_alloc_ctor(7, 2, 0);
} else {
 x_464 = x_462;
 lean_ctor_set_tag(x_464, 7);
}
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_460);
x_465 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_463);
x_466 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_437, x_465, x_339, x_340, x_341, x_342, x_461);
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
lean_dec(x_466);
x_15 = x_346;
x_16 = x_335;
x_17 = x_336;
x_18 = x_337;
x_19 = x_338;
x_20 = x_339;
x_21 = x_340;
x_22 = x_341;
x_23 = x_342;
x_24 = x_467;
goto block_33;
}
}
}
}
else
{
uint8_t x_468; 
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
x_468 = !lean_is_exclusive(x_345);
if (x_468 == 0)
{
return x_345;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_469 = lean_ctor_get(x_345, 0);
x_470 = lean_ctor_get(x_345, 1);
lean_inc(x_470);
lean_inc(x_469);
lean_dec(x_345);
x_471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
return x_471;
}
}
}
}
else
{
uint8_t x_504; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_504 = !lean_is_exclusive(x_331);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; 
x_505 = lean_ctor_get(x_331, 0);
lean_dec(x_505);
x_506 = lean_box(0);
lean_ctor_set(x_331, 0, x_506);
return x_331;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_331, 1);
lean_inc(x_507);
lean_dec(x_331);
x_508 = lean_box(0);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_507);
return x_509;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_33:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_15);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_25, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
return x_26;
}
}
block_55:
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(x_34, x_36, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = 0;
x_43 = lean_unbox(x_40);
lean_dec(x_40);
x_44 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_43, x_42);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_36);
lean_dec(x_35);
x_45 = lean_box(0);
lean_ctor_set(x_38, 0, x_45);
return x_38;
}
else
{
lean_object* x_46; 
lean_free_object(x_38);
x_46 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_35, x_36, x_41);
lean_dec(x_36);
lean_dec(x_35);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_38, 0);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_38);
x_49 = 0;
x_50 = lean_unbox(x_47);
lean_dec(x_47);
x_51 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_50, x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_36);
lean_dec(x_35);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
lean_object* x_54; 
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_35, x_36, x_48);
lean_dec(x_36);
lean_dec(x_35);
return x_54;
}
}
}
block_330:
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
x_66 = l_Int_Linear_Poly_updateOccs___redArg(x_65, x_59, x_60, x_61, x_62, x_63, x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__8;
x_69 = lean_int_dec_lt(x_56, x_68);
lean_dec(x_56);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_st_ref_take(x_59, x_67);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 14);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_71, 14);
lean_dec(x_76);
x_77 = !lean_is_exclusive(x_72);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_72, 1);
lean_dec(x_78);
x_79 = !lean_is_exclusive(x_73);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_73, 9);
x_81 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_57);
x_82 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_57, x_81, x_80, x_58);
lean_ctor_set(x_73, 9, x_82);
x_83 = lean_st_ref_set(x_59, x_71, x_74);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_34 = x_57;
x_35 = x_58;
x_36 = x_59;
x_37 = x_84;
goto block_55;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_85 = lean_ctor_get(x_73, 0);
x_86 = lean_ctor_get(x_73, 1);
x_87 = lean_ctor_get(x_73, 2);
x_88 = lean_ctor_get(x_73, 3);
x_89 = lean_ctor_get(x_73, 4);
x_90 = lean_ctor_get(x_73, 5);
x_91 = lean_ctor_get(x_73, 6);
x_92 = lean_ctor_get(x_73, 7);
x_93 = lean_ctor_get(x_73, 8);
x_94 = lean_ctor_get(x_73, 9);
x_95 = lean_ctor_get(x_73, 10);
x_96 = lean_ctor_get(x_73, 11);
x_97 = lean_ctor_get(x_73, 12);
x_98 = lean_ctor_get(x_73, 13);
x_99 = lean_ctor_get(x_73, 14);
x_100 = lean_ctor_get(x_73, 15);
x_101 = lean_ctor_get_uint8(x_73, sizeof(void*)*22);
x_102 = lean_ctor_get(x_73, 16);
x_103 = lean_ctor_get(x_73, 17);
x_104 = lean_ctor_get(x_73, 18);
x_105 = lean_ctor_get(x_73, 19);
x_106 = lean_ctor_get(x_73, 20);
x_107 = lean_ctor_get(x_73, 21);
x_108 = lean_ctor_get_uint8(x_73, sizeof(void*)*22 + 1);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
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
lean_dec(x_73);
x_109 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_57);
x_110 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_57, x_109, x_94, x_58);
x_111 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_111, 0, x_85);
lean_ctor_set(x_111, 1, x_86);
lean_ctor_set(x_111, 2, x_87);
lean_ctor_set(x_111, 3, x_88);
lean_ctor_set(x_111, 4, x_89);
lean_ctor_set(x_111, 5, x_90);
lean_ctor_set(x_111, 6, x_91);
lean_ctor_set(x_111, 7, x_92);
lean_ctor_set(x_111, 8, x_93);
lean_ctor_set(x_111, 9, x_110);
lean_ctor_set(x_111, 10, x_95);
lean_ctor_set(x_111, 11, x_96);
lean_ctor_set(x_111, 12, x_97);
lean_ctor_set(x_111, 13, x_98);
lean_ctor_set(x_111, 14, x_99);
lean_ctor_set(x_111, 15, x_100);
lean_ctor_set(x_111, 16, x_102);
lean_ctor_set(x_111, 17, x_103);
lean_ctor_set(x_111, 18, x_104);
lean_ctor_set(x_111, 19, x_105);
lean_ctor_set(x_111, 20, x_106);
lean_ctor_set(x_111, 21, x_107);
lean_ctor_set_uint8(x_111, sizeof(void*)*22, x_101);
lean_ctor_set_uint8(x_111, sizeof(void*)*22 + 1, x_108);
lean_ctor_set(x_72, 1, x_111);
x_112 = lean_st_ref_set(x_59, x_71, x_74);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_34 = x_57;
x_35 = x_58;
x_36 = x_59;
x_37 = x_113;
goto block_55;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_114 = lean_ctor_get(x_72, 0);
x_115 = lean_ctor_get(x_72, 2);
x_116 = lean_ctor_get(x_72, 3);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_72);
x_117 = lean_ctor_get(x_73, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_73, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_73, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_73, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_73, 4);
lean_inc(x_121);
x_122 = lean_ctor_get(x_73, 5);
lean_inc(x_122);
x_123 = lean_ctor_get(x_73, 6);
lean_inc(x_123);
x_124 = lean_ctor_get(x_73, 7);
lean_inc(x_124);
x_125 = lean_ctor_get(x_73, 8);
lean_inc(x_125);
x_126 = lean_ctor_get(x_73, 9);
lean_inc(x_126);
x_127 = lean_ctor_get(x_73, 10);
lean_inc(x_127);
x_128 = lean_ctor_get(x_73, 11);
lean_inc(x_128);
x_129 = lean_ctor_get(x_73, 12);
lean_inc(x_129);
x_130 = lean_ctor_get(x_73, 13);
lean_inc(x_130);
x_131 = lean_ctor_get(x_73, 14);
lean_inc(x_131);
x_132 = lean_ctor_get(x_73, 15);
lean_inc(x_132);
x_133 = lean_ctor_get_uint8(x_73, sizeof(void*)*22);
x_134 = lean_ctor_get(x_73, 16);
lean_inc(x_134);
x_135 = lean_ctor_get(x_73, 17);
lean_inc(x_135);
x_136 = lean_ctor_get(x_73, 18);
lean_inc(x_136);
x_137 = lean_ctor_get(x_73, 19);
lean_inc(x_137);
x_138 = lean_ctor_get(x_73, 20);
lean_inc(x_138);
x_139 = lean_ctor_get(x_73, 21);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_73, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 lean_ctor_release(x_73, 4);
 lean_ctor_release(x_73, 5);
 lean_ctor_release(x_73, 6);
 lean_ctor_release(x_73, 7);
 lean_ctor_release(x_73, 8);
 lean_ctor_release(x_73, 9);
 lean_ctor_release(x_73, 10);
 lean_ctor_release(x_73, 11);
 lean_ctor_release(x_73, 12);
 lean_ctor_release(x_73, 13);
 lean_ctor_release(x_73, 14);
 lean_ctor_release(x_73, 15);
 lean_ctor_release(x_73, 16);
 lean_ctor_release(x_73, 17);
 lean_ctor_release(x_73, 18);
 lean_ctor_release(x_73, 19);
 lean_ctor_release(x_73, 20);
 lean_ctor_release(x_73, 21);
 x_141 = x_73;
} else {
 lean_dec_ref(x_73);
 x_141 = lean_box(0);
}
x_142 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_57);
x_143 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_57, x_142, x_126, x_58);
if (lean_is_scalar(x_141)) {
 x_144 = lean_alloc_ctor(0, 22, 2);
} else {
 x_144 = x_141;
}
lean_ctor_set(x_144, 0, x_117);
lean_ctor_set(x_144, 1, x_118);
lean_ctor_set(x_144, 2, x_119);
lean_ctor_set(x_144, 3, x_120);
lean_ctor_set(x_144, 4, x_121);
lean_ctor_set(x_144, 5, x_122);
lean_ctor_set(x_144, 6, x_123);
lean_ctor_set(x_144, 7, x_124);
lean_ctor_set(x_144, 8, x_125);
lean_ctor_set(x_144, 9, x_143);
lean_ctor_set(x_144, 10, x_127);
lean_ctor_set(x_144, 11, x_128);
lean_ctor_set(x_144, 12, x_129);
lean_ctor_set(x_144, 13, x_130);
lean_ctor_set(x_144, 14, x_131);
lean_ctor_set(x_144, 15, x_132);
lean_ctor_set(x_144, 16, x_134);
lean_ctor_set(x_144, 17, x_135);
lean_ctor_set(x_144, 18, x_136);
lean_ctor_set(x_144, 19, x_137);
lean_ctor_set(x_144, 20, x_138);
lean_ctor_set(x_144, 21, x_139);
lean_ctor_set_uint8(x_144, sizeof(void*)*22, x_133);
lean_ctor_set_uint8(x_144, sizeof(void*)*22 + 1, x_140);
x_145 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_145, 0, x_114);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_145, 2, x_115);
lean_ctor_set(x_145, 3, x_116);
lean_ctor_set(x_71, 14, x_145);
x_146 = lean_st_ref_set(x_59, x_71, x_74);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_34 = x_57;
x_35 = x_58;
x_36 = x_59;
x_37 = x_147;
goto block_55;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_148 = lean_ctor_get(x_71, 0);
x_149 = lean_ctor_get(x_71, 1);
x_150 = lean_ctor_get(x_71, 2);
x_151 = lean_ctor_get(x_71, 3);
x_152 = lean_ctor_get(x_71, 4);
x_153 = lean_ctor_get(x_71, 5);
x_154 = lean_ctor_get(x_71, 6);
x_155 = lean_ctor_get(x_71, 7);
x_156 = lean_ctor_get_uint8(x_71, sizeof(void*)*16);
x_157 = lean_ctor_get(x_71, 8);
x_158 = lean_ctor_get(x_71, 9);
x_159 = lean_ctor_get(x_71, 10);
x_160 = lean_ctor_get(x_71, 11);
x_161 = lean_ctor_get(x_71, 12);
x_162 = lean_ctor_get(x_71, 13);
x_163 = lean_ctor_get(x_71, 15);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_71);
x_164 = lean_ctor_get(x_72, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_72, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_72, 3);
lean_inc(x_166);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 x_167 = x_72;
} else {
 lean_dec_ref(x_72);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_73, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_73, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_73, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_73, 3);
lean_inc(x_171);
x_172 = lean_ctor_get(x_73, 4);
lean_inc(x_172);
x_173 = lean_ctor_get(x_73, 5);
lean_inc(x_173);
x_174 = lean_ctor_get(x_73, 6);
lean_inc(x_174);
x_175 = lean_ctor_get(x_73, 7);
lean_inc(x_175);
x_176 = lean_ctor_get(x_73, 8);
lean_inc(x_176);
x_177 = lean_ctor_get(x_73, 9);
lean_inc(x_177);
x_178 = lean_ctor_get(x_73, 10);
lean_inc(x_178);
x_179 = lean_ctor_get(x_73, 11);
lean_inc(x_179);
x_180 = lean_ctor_get(x_73, 12);
lean_inc(x_180);
x_181 = lean_ctor_get(x_73, 13);
lean_inc(x_181);
x_182 = lean_ctor_get(x_73, 14);
lean_inc(x_182);
x_183 = lean_ctor_get(x_73, 15);
lean_inc(x_183);
x_184 = lean_ctor_get_uint8(x_73, sizeof(void*)*22);
x_185 = lean_ctor_get(x_73, 16);
lean_inc(x_185);
x_186 = lean_ctor_get(x_73, 17);
lean_inc(x_186);
x_187 = lean_ctor_get(x_73, 18);
lean_inc(x_187);
x_188 = lean_ctor_get(x_73, 19);
lean_inc(x_188);
x_189 = lean_ctor_get(x_73, 20);
lean_inc(x_189);
x_190 = lean_ctor_get(x_73, 21);
lean_inc(x_190);
x_191 = lean_ctor_get_uint8(x_73, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 lean_ctor_release(x_73, 4);
 lean_ctor_release(x_73, 5);
 lean_ctor_release(x_73, 6);
 lean_ctor_release(x_73, 7);
 lean_ctor_release(x_73, 8);
 lean_ctor_release(x_73, 9);
 lean_ctor_release(x_73, 10);
 lean_ctor_release(x_73, 11);
 lean_ctor_release(x_73, 12);
 lean_ctor_release(x_73, 13);
 lean_ctor_release(x_73, 14);
 lean_ctor_release(x_73, 15);
 lean_ctor_release(x_73, 16);
 lean_ctor_release(x_73, 17);
 lean_ctor_release(x_73, 18);
 lean_ctor_release(x_73, 19);
 lean_ctor_release(x_73, 20);
 lean_ctor_release(x_73, 21);
 x_192 = x_73;
} else {
 lean_dec_ref(x_73);
 x_192 = lean_box(0);
}
x_193 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_57);
x_194 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_57, x_193, x_177, x_58);
if (lean_is_scalar(x_192)) {
 x_195 = lean_alloc_ctor(0, 22, 2);
} else {
 x_195 = x_192;
}
lean_ctor_set(x_195, 0, x_168);
lean_ctor_set(x_195, 1, x_169);
lean_ctor_set(x_195, 2, x_170);
lean_ctor_set(x_195, 3, x_171);
lean_ctor_set(x_195, 4, x_172);
lean_ctor_set(x_195, 5, x_173);
lean_ctor_set(x_195, 6, x_174);
lean_ctor_set(x_195, 7, x_175);
lean_ctor_set(x_195, 8, x_176);
lean_ctor_set(x_195, 9, x_194);
lean_ctor_set(x_195, 10, x_178);
lean_ctor_set(x_195, 11, x_179);
lean_ctor_set(x_195, 12, x_180);
lean_ctor_set(x_195, 13, x_181);
lean_ctor_set(x_195, 14, x_182);
lean_ctor_set(x_195, 15, x_183);
lean_ctor_set(x_195, 16, x_185);
lean_ctor_set(x_195, 17, x_186);
lean_ctor_set(x_195, 18, x_187);
lean_ctor_set(x_195, 19, x_188);
lean_ctor_set(x_195, 20, x_189);
lean_ctor_set(x_195, 21, x_190);
lean_ctor_set_uint8(x_195, sizeof(void*)*22, x_184);
lean_ctor_set_uint8(x_195, sizeof(void*)*22 + 1, x_191);
if (lean_is_scalar(x_167)) {
 x_196 = lean_alloc_ctor(0, 4, 0);
} else {
 x_196 = x_167;
}
lean_ctor_set(x_196, 0, x_164);
lean_ctor_set(x_196, 1, x_195);
lean_ctor_set(x_196, 2, x_165);
lean_ctor_set(x_196, 3, x_166);
x_197 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_197, 0, x_148);
lean_ctor_set(x_197, 1, x_149);
lean_ctor_set(x_197, 2, x_150);
lean_ctor_set(x_197, 3, x_151);
lean_ctor_set(x_197, 4, x_152);
lean_ctor_set(x_197, 5, x_153);
lean_ctor_set(x_197, 6, x_154);
lean_ctor_set(x_197, 7, x_155);
lean_ctor_set(x_197, 8, x_157);
lean_ctor_set(x_197, 9, x_158);
lean_ctor_set(x_197, 10, x_159);
lean_ctor_set(x_197, 11, x_160);
lean_ctor_set(x_197, 12, x_161);
lean_ctor_set(x_197, 13, x_162);
lean_ctor_set(x_197, 14, x_196);
lean_ctor_set(x_197, 15, x_163);
lean_ctor_set_uint8(x_197, sizeof(void*)*16, x_156);
x_198 = lean_st_ref_set(x_59, x_197, x_74);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_34 = x_57;
x_35 = x_58;
x_36 = x_59;
x_37 = x_199;
goto block_55;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_200 = lean_st_ref_take(x_59, x_67);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_201, 14);
lean_inc(x_202);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_200, 1);
lean_inc(x_204);
lean_dec(x_200);
x_205 = !lean_is_exclusive(x_201);
if (x_205 == 0)
{
lean_object* x_206; uint8_t x_207; 
x_206 = lean_ctor_get(x_201, 14);
lean_dec(x_206);
x_207 = !lean_is_exclusive(x_202);
if (x_207 == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_202, 1);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_203);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_210 = lean_ctor_get(x_203, 8);
x_211 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_57);
x_212 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_57, x_211, x_210, x_58);
lean_ctor_set(x_203, 8, x_212);
x_213 = lean_st_ref_set(x_59, x_201, x_204);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_34 = x_57;
x_35 = x_58;
x_36 = x_59;
x_37 = x_214;
goto block_55;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_215 = lean_ctor_get(x_203, 0);
x_216 = lean_ctor_get(x_203, 1);
x_217 = lean_ctor_get(x_203, 2);
x_218 = lean_ctor_get(x_203, 3);
x_219 = lean_ctor_get(x_203, 4);
x_220 = lean_ctor_get(x_203, 5);
x_221 = lean_ctor_get(x_203, 6);
x_222 = lean_ctor_get(x_203, 7);
x_223 = lean_ctor_get(x_203, 8);
x_224 = lean_ctor_get(x_203, 9);
x_225 = lean_ctor_get(x_203, 10);
x_226 = lean_ctor_get(x_203, 11);
x_227 = lean_ctor_get(x_203, 12);
x_228 = lean_ctor_get(x_203, 13);
x_229 = lean_ctor_get(x_203, 14);
x_230 = lean_ctor_get(x_203, 15);
x_231 = lean_ctor_get_uint8(x_203, sizeof(void*)*22);
x_232 = lean_ctor_get(x_203, 16);
x_233 = lean_ctor_get(x_203, 17);
x_234 = lean_ctor_get(x_203, 18);
x_235 = lean_ctor_get(x_203, 19);
x_236 = lean_ctor_get(x_203, 20);
x_237 = lean_ctor_get(x_203, 21);
x_238 = lean_ctor_get_uint8(x_203, sizeof(void*)*22 + 1);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_203);
x_239 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_57);
x_240 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_57, x_239, x_223, x_58);
x_241 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_241, 0, x_215);
lean_ctor_set(x_241, 1, x_216);
lean_ctor_set(x_241, 2, x_217);
lean_ctor_set(x_241, 3, x_218);
lean_ctor_set(x_241, 4, x_219);
lean_ctor_set(x_241, 5, x_220);
lean_ctor_set(x_241, 6, x_221);
lean_ctor_set(x_241, 7, x_222);
lean_ctor_set(x_241, 8, x_240);
lean_ctor_set(x_241, 9, x_224);
lean_ctor_set(x_241, 10, x_225);
lean_ctor_set(x_241, 11, x_226);
lean_ctor_set(x_241, 12, x_227);
lean_ctor_set(x_241, 13, x_228);
lean_ctor_set(x_241, 14, x_229);
lean_ctor_set(x_241, 15, x_230);
lean_ctor_set(x_241, 16, x_232);
lean_ctor_set(x_241, 17, x_233);
lean_ctor_set(x_241, 18, x_234);
lean_ctor_set(x_241, 19, x_235);
lean_ctor_set(x_241, 20, x_236);
lean_ctor_set(x_241, 21, x_237);
lean_ctor_set_uint8(x_241, sizeof(void*)*22, x_231);
lean_ctor_set_uint8(x_241, sizeof(void*)*22 + 1, x_238);
lean_ctor_set(x_202, 1, x_241);
x_242 = lean_st_ref_set(x_59, x_201, x_204);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_34 = x_57;
x_35 = x_58;
x_36 = x_59;
x_37 = x_243;
goto block_55;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_244 = lean_ctor_get(x_202, 0);
x_245 = lean_ctor_get(x_202, 2);
x_246 = lean_ctor_get(x_202, 3);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_202);
x_247 = lean_ctor_get(x_203, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_203, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_203, 2);
lean_inc(x_249);
x_250 = lean_ctor_get(x_203, 3);
lean_inc(x_250);
x_251 = lean_ctor_get(x_203, 4);
lean_inc(x_251);
x_252 = lean_ctor_get(x_203, 5);
lean_inc(x_252);
x_253 = lean_ctor_get(x_203, 6);
lean_inc(x_253);
x_254 = lean_ctor_get(x_203, 7);
lean_inc(x_254);
x_255 = lean_ctor_get(x_203, 8);
lean_inc(x_255);
x_256 = lean_ctor_get(x_203, 9);
lean_inc(x_256);
x_257 = lean_ctor_get(x_203, 10);
lean_inc(x_257);
x_258 = lean_ctor_get(x_203, 11);
lean_inc(x_258);
x_259 = lean_ctor_get(x_203, 12);
lean_inc(x_259);
x_260 = lean_ctor_get(x_203, 13);
lean_inc(x_260);
x_261 = lean_ctor_get(x_203, 14);
lean_inc(x_261);
x_262 = lean_ctor_get(x_203, 15);
lean_inc(x_262);
x_263 = lean_ctor_get_uint8(x_203, sizeof(void*)*22);
x_264 = lean_ctor_get(x_203, 16);
lean_inc(x_264);
x_265 = lean_ctor_get(x_203, 17);
lean_inc(x_265);
x_266 = lean_ctor_get(x_203, 18);
lean_inc(x_266);
x_267 = lean_ctor_get(x_203, 19);
lean_inc(x_267);
x_268 = lean_ctor_get(x_203, 20);
lean_inc(x_268);
x_269 = lean_ctor_get(x_203, 21);
lean_inc(x_269);
x_270 = lean_ctor_get_uint8(x_203, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 lean_ctor_release(x_203, 2);
 lean_ctor_release(x_203, 3);
 lean_ctor_release(x_203, 4);
 lean_ctor_release(x_203, 5);
 lean_ctor_release(x_203, 6);
 lean_ctor_release(x_203, 7);
 lean_ctor_release(x_203, 8);
 lean_ctor_release(x_203, 9);
 lean_ctor_release(x_203, 10);
 lean_ctor_release(x_203, 11);
 lean_ctor_release(x_203, 12);
 lean_ctor_release(x_203, 13);
 lean_ctor_release(x_203, 14);
 lean_ctor_release(x_203, 15);
 lean_ctor_release(x_203, 16);
 lean_ctor_release(x_203, 17);
 lean_ctor_release(x_203, 18);
 lean_ctor_release(x_203, 19);
 lean_ctor_release(x_203, 20);
 lean_ctor_release(x_203, 21);
 x_271 = x_203;
} else {
 lean_dec_ref(x_203);
 x_271 = lean_box(0);
}
x_272 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_57);
x_273 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_57, x_272, x_255, x_58);
if (lean_is_scalar(x_271)) {
 x_274 = lean_alloc_ctor(0, 22, 2);
} else {
 x_274 = x_271;
}
lean_ctor_set(x_274, 0, x_247);
lean_ctor_set(x_274, 1, x_248);
lean_ctor_set(x_274, 2, x_249);
lean_ctor_set(x_274, 3, x_250);
lean_ctor_set(x_274, 4, x_251);
lean_ctor_set(x_274, 5, x_252);
lean_ctor_set(x_274, 6, x_253);
lean_ctor_set(x_274, 7, x_254);
lean_ctor_set(x_274, 8, x_273);
lean_ctor_set(x_274, 9, x_256);
lean_ctor_set(x_274, 10, x_257);
lean_ctor_set(x_274, 11, x_258);
lean_ctor_set(x_274, 12, x_259);
lean_ctor_set(x_274, 13, x_260);
lean_ctor_set(x_274, 14, x_261);
lean_ctor_set(x_274, 15, x_262);
lean_ctor_set(x_274, 16, x_264);
lean_ctor_set(x_274, 17, x_265);
lean_ctor_set(x_274, 18, x_266);
lean_ctor_set(x_274, 19, x_267);
lean_ctor_set(x_274, 20, x_268);
lean_ctor_set(x_274, 21, x_269);
lean_ctor_set_uint8(x_274, sizeof(void*)*22, x_263);
lean_ctor_set_uint8(x_274, sizeof(void*)*22 + 1, x_270);
x_275 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_275, 0, x_244);
lean_ctor_set(x_275, 1, x_274);
lean_ctor_set(x_275, 2, x_245);
lean_ctor_set(x_275, 3, x_246);
lean_ctor_set(x_201, 14, x_275);
x_276 = lean_st_ref_set(x_59, x_201, x_204);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
lean_dec(x_276);
x_34 = x_57;
x_35 = x_58;
x_36 = x_59;
x_37 = x_277;
goto block_55;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_278 = lean_ctor_get(x_201, 0);
x_279 = lean_ctor_get(x_201, 1);
x_280 = lean_ctor_get(x_201, 2);
x_281 = lean_ctor_get(x_201, 3);
x_282 = lean_ctor_get(x_201, 4);
x_283 = lean_ctor_get(x_201, 5);
x_284 = lean_ctor_get(x_201, 6);
x_285 = lean_ctor_get(x_201, 7);
x_286 = lean_ctor_get_uint8(x_201, sizeof(void*)*16);
x_287 = lean_ctor_get(x_201, 8);
x_288 = lean_ctor_get(x_201, 9);
x_289 = lean_ctor_get(x_201, 10);
x_290 = lean_ctor_get(x_201, 11);
x_291 = lean_ctor_get(x_201, 12);
x_292 = lean_ctor_get(x_201, 13);
x_293 = lean_ctor_get(x_201, 15);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_201);
x_294 = lean_ctor_get(x_202, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_202, 2);
lean_inc(x_295);
x_296 = lean_ctor_get(x_202, 3);
lean_inc(x_296);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 lean_ctor_release(x_202, 2);
 lean_ctor_release(x_202, 3);
 x_297 = x_202;
} else {
 lean_dec_ref(x_202);
 x_297 = lean_box(0);
}
x_298 = lean_ctor_get(x_203, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_203, 1);
lean_inc(x_299);
x_300 = lean_ctor_get(x_203, 2);
lean_inc(x_300);
x_301 = lean_ctor_get(x_203, 3);
lean_inc(x_301);
x_302 = lean_ctor_get(x_203, 4);
lean_inc(x_302);
x_303 = lean_ctor_get(x_203, 5);
lean_inc(x_303);
x_304 = lean_ctor_get(x_203, 6);
lean_inc(x_304);
x_305 = lean_ctor_get(x_203, 7);
lean_inc(x_305);
x_306 = lean_ctor_get(x_203, 8);
lean_inc(x_306);
x_307 = lean_ctor_get(x_203, 9);
lean_inc(x_307);
x_308 = lean_ctor_get(x_203, 10);
lean_inc(x_308);
x_309 = lean_ctor_get(x_203, 11);
lean_inc(x_309);
x_310 = lean_ctor_get(x_203, 12);
lean_inc(x_310);
x_311 = lean_ctor_get(x_203, 13);
lean_inc(x_311);
x_312 = lean_ctor_get(x_203, 14);
lean_inc(x_312);
x_313 = lean_ctor_get(x_203, 15);
lean_inc(x_313);
x_314 = lean_ctor_get_uint8(x_203, sizeof(void*)*22);
x_315 = lean_ctor_get(x_203, 16);
lean_inc(x_315);
x_316 = lean_ctor_get(x_203, 17);
lean_inc(x_316);
x_317 = lean_ctor_get(x_203, 18);
lean_inc(x_317);
x_318 = lean_ctor_get(x_203, 19);
lean_inc(x_318);
x_319 = lean_ctor_get(x_203, 20);
lean_inc(x_319);
x_320 = lean_ctor_get(x_203, 21);
lean_inc(x_320);
x_321 = lean_ctor_get_uint8(x_203, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 lean_ctor_release(x_203, 2);
 lean_ctor_release(x_203, 3);
 lean_ctor_release(x_203, 4);
 lean_ctor_release(x_203, 5);
 lean_ctor_release(x_203, 6);
 lean_ctor_release(x_203, 7);
 lean_ctor_release(x_203, 8);
 lean_ctor_release(x_203, 9);
 lean_ctor_release(x_203, 10);
 lean_ctor_release(x_203, 11);
 lean_ctor_release(x_203, 12);
 lean_ctor_release(x_203, 13);
 lean_ctor_release(x_203, 14);
 lean_ctor_release(x_203, 15);
 lean_ctor_release(x_203, 16);
 lean_ctor_release(x_203, 17);
 lean_ctor_release(x_203, 18);
 lean_ctor_release(x_203, 19);
 lean_ctor_release(x_203, 20);
 lean_ctor_release(x_203, 21);
 x_322 = x_203;
} else {
 lean_dec_ref(x_203);
 x_322 = lean_box(0);
}
x_323 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_57);
x_324 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_57, x_323, x_306, x_58);
if (lean_is_scalar(x_322)) {
 x_325 = lean_alloc_ctor(0, 22, 2);
} else {
 x_325 = x_322;
}
lean_ctor_set(x_325, 0, x_298);
lean_ctor_set(x_325, 1, x_299);
lean_ctor_set(x_325, 2, x_300);
lean_ctor_set(x_325, 3, x_301);
lean_ctor_set(x_325, 4, x_302);
lean_ctor_set(x_325, 5, x_303);
lean_ctor_set(x_325, 6, x_304);
lean_ctor_set(x_325, 7, x_305);
lean_ctor_set(x_325, 8, x_324);
lean_ctor_set(x_325, 9, x_307);
lean_ctor_set(x_325, 10, x_308);
lean_ctor_set(x_325, 11, x_309);
lean_ctor_set(x_325, 12, x_310);
lean_ctor_set(x_325, 13, x_311);
lean_ctor_set(x_325, 14, x_312);
lean_ctor_set(x_325, 15, x_313);
lean_ctor_set(x_325, 16, x_315);
lean_ctor_set(x_325, 17, x_316);
lean_ctor_set(x_325, 18, x_317);
lean_ctor_set(x_325, 19, x_318);
lean_ctor_set(x_325, 20, x_319);
lean_ctor_set(x_325, 21, x_320);
lean_ctor_set_uint8(x_325, sizeof(void*)*22, x_314);
lean_ctor_set_uint8(x_325, sizeof(void*)*22 + 1, x_321);
if (lean_is_scalar(x_297)) {
 x_326 = lean_alloc_ctor(0, 4, 0);
} else {
 x_326 = x_297;
}
lean_ctor_set(x_326, 0, x_294);
lean_ctor_set(x_326, 1, x_325);
lean_ctor_set(x_326, 2, x_295);
lean_ctor_set(x_326, 3, x_296);
x_327 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_327, 0, x_278);
lean_ctor_set(x_327, 1, x_279);
lean_ctor_set(x_327, 2, x_280);
lean_ctor_set(x_327, 3, x_281);
lean_ctor_set(x_327, 4, x_282);
lean_ctor_set(x_327, 5, x_283);
lean_ctor_set(x_327, 6, x_284);
lean_ctor_set(x_327, 7, x_285);
lean_ctor_set(x_327, 8, x_287);
lean_ctor_set(x_327, 9, x_288);
lean_ctor_set(x_327, 10, x_289);
lean_ctor_set(x_327, 11, x_290);
lean_ctor_set(x_327, 12, x_291);
lean_ctor_set(x_327, 13, x_292);
lean_ctor_set(x_327, 14, x_326);
lean_ctor_set(x_327, 15, x_293);
lean_ctor_set_uint8(x_327, sizeof(void*)*16, x_286);
x_328 = lean_st_ref_set(x_59, x_327, x_204);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_34 = x_57;
x_35 = x_58;
x_36 = x_59;
x_37 = x_329;
goto block_55;
}
}
}
else
{
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected non normalized inequality constraint found", 53, 53);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Grind_getConfig___redArg(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*6 + 11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1;
x_21 = l_Lean_indentExpr(x_1);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_Grind_reportIssue(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; uint8_t x_19; 
lean_inc(x_1);
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_18 = l_Lean_Expr_cleanupAnnotations(x_12);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_17;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_17;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_17;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_17;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2;
x_31 = l_Lean_Expr_isConstOf(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_17;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_14);
x_32 = l_Lean_Meta_isInstLEInt___redArg(x_26, x_7, x_13);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_32, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_32, 0, x_37);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Meta_getIntValue_x3f(x_20, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_23);
lean_dec(x_2);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = lean_box(0);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_dec(x_42);
x_53 = !lean_is_exclusive(x_43);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_43, 0);
x_55 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__8;
x_56 = lean_int_dec_eq(x_54, x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
lean_free_object(x_43);
lean_dec(x_23);
lean_dec(x_2);
x_57 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
x_60 = lean_box(0);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec(x_1);
x_64 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_ctor_set(x_43, 0, x_66);
lean_ctor_set(x_64, 0, x_43);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_64);
lean_ctor_set(x_43, 0, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_43);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_free_object(x_43);
x_70 = !lean_is_exclusive(x_64);
if (x_70 == 0)
{
return x_64;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_64, 0);
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_64);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_43, 0);
lean_inc(x_74);
lean_dec(x_43);
x_75 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__8;
x_76 = lean_int_dec_eq(x_74, x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_23);
lean_dec(x_2);
x_77 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_box(0);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
else
{
lean_object* x_82; 
lean_dec(x_1);
x_82 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_83);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_90 = x_82;
} else {
 lean_dec_ref(x_82);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_42);
if (x_92 == 0)
{
return x_42;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_42, 0);
x_94 = lean_ctor_get(x_42, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_42);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
}
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
if (lean_is_scalar(x_14)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_14;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Int_Linear_Poly_normCommRing_x3f(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_grind_cutsat_assert_le(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
x_23 = lean_alloc_ctor(19, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_17, 1, x_23);
lean_ctor_set(x_17, 0, x_22);
x_24 = lean_grind_cutsat_assert_le(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(19, 3, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_grind_cutsat_assert_le(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
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
if (x_2 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0;
lean_inc(x_21);
x_24 = l_Int_Linear_Poly_mul(x_21, x_23);
x_25 = l_Int_Linear_Poly_addConst(x_24, x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_13, 0);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_13);
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_13, 0);
lean_inc(x_34);
lean_dec(x_13);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Int_OfNat_toIntLe_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
lean_inc(x_1);
x_24 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_3, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___redArg(x_3, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_22);
lean_inc(x_28);
x_30 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_28, x_22, x_6, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_25);
x_34 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_32, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_23);
x_37 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_28, x_23, x_6, x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_39, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_42);
lean_inc(x_35);
lean_ctor_set_tag(x_37, 3);
lean_ctor_set(x_37, 1, x_42);
lean_ctor_set(x_37, 0, x_35);
x_44 = l_Int_Linear_Expr_norm(x_37);
lean_dec(x_37);
if (x_2 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_46 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0;
x_47 = l_Int_Linear_Poly_mul(x_44, x_46);
x_48 = l_Int_Linear_Poly_addConst(x_47, x_45);
x_49 = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_22);
lean_ctor_set(x_49, 2, x_23);
lean_ctor_set(x_49, 3, x_35);
lean_ctor_set(x_49, 4, x_42);
lean_ctor_set(x_30, 1, x_49);
lean_ctor_set(x_30, 0, x_48);
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_22);
lean_ctor_set(x_51, 2, x_23);
lean_ctor_set(x_51, 3, x_35);
lean_ctor_set(x_51, 4, x_42);
lean_ctor_set(x_30, 1, x_51);
lean_ctor_set(x_30, 0, x_44);
x_52 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_free_object(x_37);
lean_dec(x_35);
lean_free_object(x_30);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_37, 0);
x_58 = lean_ctor_get(x_37, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_37);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_59 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_57, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_60);
lean_inc(x_35);
x_62 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_62, 0, x_35);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Int_Linear_Expr_norm(x_62);
lean_dec(x_62);
if (x_2 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_65 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0;
x_66 = l_Int_Linear_Poly_mul(x_63, x_65);
x_67 = l_Int_Linear_Poly_addConst(x_66, x_64);
x_68 = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_22);
lean_ctor_set(x_68, 2, x_23);
lean_ctor_set(x_68, 3, x_35);
lean_ctor_set(x_68, 4, x_60);
lean_ctor_set(x_30, 1, x_68);
lean_ctor_set(x_30, 0, x_67);
x_69 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_61);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_22);
lean_ctor_set(x_70, 2, x_23);
lean_ctor_set(x_70, 3, x_35);
lean_ctor_set(x_70, 4, x_60);
lean_ctor_set(x_30, 1, x_70);
lean_ctor_set(x_30, 0, x_63);
x_71 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_61);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_35);
lean_free_object(x_30);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = lean_ctor_get(x_59, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_59, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_74 = x_59;
} else {
 lean_dec_ref(x_59);
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
else
{
uint8_t x_76; 
lean_free_object(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_34);
if (x_76 == 0)
{
return x_34;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_34, 0);
x_78 = lean_ctor_get(x_34, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_34);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_30, 0);
x_81 = lean_ctor_get(x_30, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_30);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_25);
x_82 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_80, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_23);
x_85 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_28, x_23, x_6, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_89 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_86, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_90);
lean_inc(x_83);
if (lean_is_scalar(x_88)) {
 x_92 = lean_alloc_ctor(3, 2, 0);
} else {
 x_92 = x_88;
 lean_ctor_set_tag(x_92, 3);
}
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Int_Linear_Expr_norm(x_92);
lean_dec(x_92);
if (x_2 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_95 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0;
x_96 = l_Int_Linear_Poly_mul(x_93, x_95);
x_97 = l_Int_Linear_Poly_addConst(x_96, x_94);
x_98 = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_22);
lean_ctor_set(x_98, 2, x_23);
lean_ctor_set(x_98, 3, x_83);
lean_ctor_set(x_98, 4, x_90);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(x_99, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_91);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_101, 0, x_1);
lean_ctor_set(x_101, 1, x_22);
lean_ctor_set(x_101, 2, x_23);
lean_ctor_set(x_101, 3, x_83);
lean_ctor_set(x_101, 4, x_90);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_93);
lean_ctor_set(x_102, 1, x_101);
x_103 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(x_102, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_91);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_88);
lean_dec(x_83);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_104 = lean_ctor_get(x_89, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_89, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_106 = x_89;
} else {
 lean_dec_ref(x_89);
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
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_108 = lean_ctor_get(x_82, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
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
}
}
else
{
uint8_t x_112; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_12);
if (x_112 == 0)
{
return x_12;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_12, 0);
x_114 = lean_ctor_get(x_12, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_12);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
if (x_2 == 0)
{
lean_object* x_102; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_102 = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(x_3, x_4, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_50 = x_103;
x_51 = x_3;
x_52 = x_4;
x_53 = x_5;
x_54 = x_6;
x_55 = x_7;
x_56 = x_8;
x_57 = x_9;
x_58 = x_10;
x_59 = x_11;
x_60 = x_104;
goto block_101;
}
else
{
uint8_t x_105; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_102);
if (x_105 == 0)
{
return x_102;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_102, 0);
x_107 = lean_ctor_get(x_102, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_102);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_109 = l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(x_3, x_4, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_50 = x_110;
x_51 = x_3;
x_52 = x_4;
x_53 = x_5;
x_54 = x_6;
x_55 = x_7;
x_56 = x_8;
x_57 = x_9;
x_58 = x_10;
x_59 = x_11;
x_60 = x_111;
goto block_101;
}
else
{
uint8_t x_112; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
return x_109;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_109, 0);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_109);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
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
block_49:
{
lean_object* x_30; 
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_24);
lean_inc(x_18);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_26);
lean_inc(x_27);
lean_inc(x_20);
x_30 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_28, x_20, x_27, x_26, x_23, x_25, x_18, x_24, x_19, x_21, x_17);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_24);
lean_inc(x_18);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_26);
lean_inc(x_27);
x_33 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_29, x_20, x_27, x_26, x_23, x_25, x_18, x_24, x_19, x_21, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_34);
lean_inc(x_31);
x_36 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Int_Linear_Expr_norm(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(4, 4, 1);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_22);
lean_ctor_set(x_38, 2, x_31);
lean_ctor_set(x_38, 3, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(x_39, x_27, x_26, x_23, x_25, x_18, x_24, x_19, x_21, x_35);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_33);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_30);
if (x_45 == 0)
{
return x_30;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_30, 0);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_30);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
block_101:
{
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_1);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
lean_dec(x_50);
lean_inc(x_1);
x_64 = l_Lean_Expr_cleanupAnnotations(x_1);
x_65 = l_Lean_Expr_isApp(x_64);
if (x_65 == 0)
{
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_1);
x_13 = x_60;
goto block_16;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
x_67 = l_Lean_Expr_appFnCleanup___redArg(x_64);
x_68 = l_Lean_Expr_isApp(x_67);
if (x_68 == 0)
{
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_1);
x_13 = x_60;
goto block_16;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
x_70 = l_Lean_Expr_appFnCleanup___redArg(x_67);
x_71 = l_Lean_Expr_isApp(x_70);
if (x_71 == 0)
{
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_1);
x_13 = x_60;
goto block_16;
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = l_Lean_Expr_appFnCleanup___redArg(x_70);
x_73 = l_Lean_Expr_isApp(x_72);
if (x_73 == 0)
{
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_1);
x_13 = x_60;
goto block_16;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = l_Lean_Expr_appFnCleanup___redArg(x_72);
x_75 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2;
x_76 = l_Lean_Expr_isConstOf(x_74, x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_1);
x_13 = x_60;
goto block_16;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_inc(x_1);
x_77 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_52, x_60);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_69);
x_80 = l_Lean_Meta_Grind_Arith_Cutsat_toInt(x_69, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_59, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_66);
x_85 = l_Lean_Meta_Grind_Arith_Cutsat_toInt(x_66, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_59, x_82);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
lean_inc(x_88);
lean_inc(x_83);
x_90 = l_Lean_mkApp6(x_63, x_69, x_66, x_83, x_88, x_84, x_89);
if (x_2 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___closed__0;
x_92 = l_Lean_mkIntAdd(x_88, x_91);
x_17 = x_87;
x_18 = x_56;
x_19 = x_58;
x_20 = x_78;
x_21 = x_59;
x_22 = x_90;
x_23 = x_54;
x_24 = x_57;
x_25 = x_55;
x_26 = x_53;
x_27 = x_52;
x_28 = x_92;
x_29 = x_83;
goto block_49;
}
else
{
x_17 = x_87;
x_18 = x_56;
x_19 = x_58;
x_20 = x_78;
x_21 = x_59;
x_22 = x_90;
x_23 = x_54;
x_24 = x_57;
x_25 = x_55;
x_26 = x_53;
x_27 = x_52;
x_28 = x_83;
x_29 = x_88;
goto block_49;
}
}
else
{
uint8_t x_93; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_78);
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_85);
if (x_93 == 0)
{
return x_85;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_85, 0);
x_95 = lean_ctor_get(x_85, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_85);
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
lean_dec(x_78);
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_80);
if (x_97 == 0)
{
return x_80;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_80, 0);
x_99 = lean_ctor_get(x_80, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_80);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*6 + 20);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
lean_inc(x_1);
x_26 = l_Lean_Expr_cleanupAnnotations(x_1);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_25;
goto block_15;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_25;
goto block_15;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_25;
goto block_15;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_25;
goto block_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_35 = l_Lean_Expr_appFnCleanup___redArg(x_32);
x_36 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2;
x_37 = l_Lean_Expr_isConstOf(x_35, x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_25;
goto block_15;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1;
x_39 = l_Lean_Expr_isConstOf(x_34, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__3;
x_41 = l_Lean_Expr_isConstOf(x_34, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_box(x_2);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed), 12, 2);
lean_closure_set(x_43, 0, x_1);
lean_closure_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(x_34, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec(x_34);
x_45 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_dec(x_34);
x_46 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
return x_46;
}
}
}
}
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_5) == 0)
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
lean_dec(x_5);
lean_inc(x_1);
x_19 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_7, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_toInt(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_27 = x_23;
} else {
 lean_dec_ref(x_23);
 x_27 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_28 = l_Lean_Meta_Grind_Arith_Cutsat_toInt(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_33 = x_29;
} else {
 lean_dec_ref(x_29);
 x_33 = lean_box(0);
}
lean_inc(x_31);
lean_inc(x_25);
x_34 = l_Lean_mkApp6(x_18, x_2, x_3, x_25, x_31, x_26, x_32);
if (x_4 == 0)
{
x_35 = x_31;
x_36 = x_25;
goto block_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___closed__0;
x_58 = l_Lean_mkIntAdd(x_25, x_57);
x_35 = x_58;
x_36 = x_31;
goto block_56;
}
block_56:
{
lean_object* x_37; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_35, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_36, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_41);
lean_inc(x_38);
if (lean_is_scalar(x_33)) {
 x_43 = lean_alloc_ctor(3, 2, 0);
} else {
 x_43 = x_33;
 lean_ctor_set_tag(x_43, 3);
}
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Int_Linear_Expr_norm(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(4, 4, 1);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_45, 2, x_38);
lean_ctor_set(x_45, 3, x_41);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_4);
if (lean_is_scalar(x_27)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_27;
}
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_grind_cutsat_assert_le(x_46, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_42);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
return x_40;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
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
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_37);
if (x_52 == 0)
{
return x_37;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_37, 0);
x_54 = lean_ctor_get(x_37, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_37);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_28);
if (x_59 == 0)
{
return x_28;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_28, 0);
x_61 = lean_ctor_get(x_28, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_28);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_22);
if (x_63 == 0)
{
return x_22;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_1 == 0)
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(x_3, x_4, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_apply_11(x_2, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_16;
}
else
{
uint8_t x_17; 
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
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(x_3, x_4, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_apply_11(x_2, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
return x_24;
}
else
{
uint8_t x_25; 
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
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*6 + 20);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
lean_inc(x_1);
x_26 = l_Lean_Expr_cleanupAnnotations(x_1);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_25;
goto block_15;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_25;
goto block_15;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_25;
goto block_15;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_32);
x_35 = l_Lean_Expr_isApp(x_34);
if (x_35 == 0)
{
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_25;
goto block_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_34);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2;
x_39 = l_Lean_Expr_isConstOf(x_37, x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_25;
goto block_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_box(x_2);
x_41 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed), 15, 4);
lean_closure_set(x_41, 0, x_1);
lean_closure_set(x_41, 1, x_31);
lean_closure_set(x_41, 2, x_28);
lean_closure_set(x_41, 3, x_40);
x_42 = lean_box(x_2);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed), 12, 2);
lean_closure_set(x_43, 0, x_42);
lean_closure_set(x_43, 1, x_41);
x_44 = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(x_36, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
return x_44;
}
}
}
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Arith_Int(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__8 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__8);
l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0 = _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0();
lean_mark_persistent(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__0 = _init_l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__0();
lean_mark_persistent(l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__0);
l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__1 = _init_l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__1();
lean_mark_persistent(l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__1);
l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__2 = _init_l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__0 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__0();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__0);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__1 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__1();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__1);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__2 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__2();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__2);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__3 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__3();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__3);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__4 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__4();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___closed__0 = _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___closed__0();
lean_mark_persistent(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___closed__0);
l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__0 = _init_l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__0();
lean_mark_persistent(l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__0);
l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__1 = _init_l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__1();
lean_mark_persistent(l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__1);
l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__2 = _init_l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__2);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

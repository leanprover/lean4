// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr
// Imports: Lean.Meta.Tactic.Simp.Arith.Int Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt
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
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_addConst(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isNegEq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__0;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__8;
lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5;
uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstLEInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNegEq___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
size_t lean_usize_sub(size_t, size_t);
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
static lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__6;
lean_object* l_Int_OfNat_toIntLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0;
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
x_15 = lean_alloc_ctor(7, 1, 0);
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
x_9 = lean_alloc_ctor(8, 1, 0);
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
x_14 = lean_alloc_ctor(11, 3, 0);
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
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_20 = lean_int_neg(x_14);
x_21 = lean_int_dec_eq(x_11, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
x_17 = x_21;
goto block_19;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_12, x_15);
x_17 = x_22;
goto block_19;
}
block_19:
{
if (x_17 == 0)
{
return x_17;
}
else
{
x_1 = x_13;
x_2 = x_16;
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
x_14 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_13, x_1);
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
x_24 = lean_ctor_get(x_17, 7);
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_26 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_25, x_24, x_11);
lean_dec(x_11);
lean_dec(x_8);
lean_ctor_set(x_17, 7, x_26);
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
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
x_48 = lean_ctor_get_uint8(x_17, sizeof(void*)*19);
x_49 = lean_ctor_get(x_17, 14);
x_50 = lean_ctor_get(x_17, 15);
x_51 = lean_ctor_get(x_17, 16);
x_52 = lean_ctor_get(x_17, 17);
x_53 = lean_ctor_get(x_17, 18);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
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
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_55 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_54, x_41, x_11);
lean_dec(x_11);
lean_dec(x_8);
x_56 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_56, 0, x_34);
lean_ctor_set(x_56, 1, x_35);
lean_ctor_set(x_56, 2, x_36);
lean_ctor_set(x_56, 3, x_37);
lean_ctor_set(x_56, 4, x_38);
lean_ctor_set(x_56, 5, x_39);
lean_ctor_set(x_56, 6, x_40);
lean_ctor_set(x_56, 7, x_55);
lean_ctor_set(x_56, 8, x_42);
lean_ctor_set(x_56, 9, x_43);
lean_ctor_set(x_56, 10, x_44);
lean_ctor_set(x_56, 11, x_45);
lean_ctor_set(x_56, 12, x_46);
lean_ctor_set(x_56, 13, x_47);
lean_ctor_set(x_56, 14, x_49);
lean_ctor_set(x_56, 15, x_50);
lean_ctor_set(x_56, 16, x_51);
lean_ctor_set(x_56, 17, x_52);
lean_ctor_set(x_56, 18, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*19, x_48);
lean_ctor_set(x_16, 1, x_56);
x_57 = lean_st_ref_set(x_2, x_15, x_18);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_62 = lean_ctor_get(x_16, 0);
x_63 = lean_ctor_get(x_16, 2);
x_64 = lean_ctor_get(x_16, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_16);
x_65 = lean_ctor_get(x_17, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_17, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_17, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_17, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_17, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_17, 5);
lean_inc(x_70);
x_71 = lean_ctor_get(x_17, 6);
lean_inc(x_71);
x_72 = lean_ctor_get(x_17, 7);
lean_inc(x_72);
x_73 = lean_ctor_get(x_17, 8);
lean_inc(x_73);
x_74 = lean_ctor_get(x_17, 9);
lean_inc(x_74);
x_75 = lean_ctor_get(x_17, 10);
lean_inc(x_75);
x_76 = lean_ctor_get(x_17, 11);
lean_inc(x_76);
x_77 = lean_ctor_get(x_17, 12);
lean_inc(x_77);
x_78 = lean_ctor_get(x_17, 13);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_17, sizeof(void*)*19);
x_80 = lean_ctor_get(x_17, 14);
lean_inc(x_80);
x_81 = lean_ctor_get(x_17, 15);
lean_inc(x_81);
x_82 = lean_ctor_get(x_17, 16);
lean_inc(x_82);
x_83 = lean_ctor_get(x_17, 17);
lean_inc(x_83);
x_84 = lean_ctor_get(x_17, 18);
lean_inc(x_84);
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
 x_85 = x_17;
} else {
 lean_dec_ref(x_17);
 x_85 = lean_box(0);
}
x_86 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_87 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_86, x_72, x_11);
lean_dec(x_11);
lean_dec(x_8);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 19, 1);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_65);
lean_ctor_set(x_88, 1, x_66);
lean_ctor_set(x_88, 2, x_67);
lean_ctor_set(x_88, 3, x_68);
lean_ctor_set(x_88, 4, x_69);
lean_ctor_set(x_88, 5, x_70);
lean_ctor_set(x_88, 6, x_71);
lean_ctor_set(x_88, 7, x_87);
lean_ctor_set(x_88, 8, x_73);
lean_ctor_set(x_88, 9, x_74);
lean_ctor_set(x_88, 10, x_75);
lean_ctor_set(x_88, 11, x_76);
lean_ctor_set(x_88, 12, x_77);
lean_ctor_set(x_88, 13, x_78);
lean_ctor_set(x_88, 14, x_80);
lean_ctor_set(x_88, 15, x_81);
lean_ctor_set(x_88, 16, x_82);
lean_ctor_set(x_88, 17, x_83);
lean_ctor_set(x_88, 18, x_84);
lean_ctor_set_uint8(x_88, sizeof(void*)*19, x_79);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_62);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_63);
lean_ctor_set(x_89, 3, x_64);
lean_ctor_set(x_15, 14, x_89);
x_90 = lean_st_ref_set(x_2, x_15, x_18);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_95 = lean_ctor_get(x_15, 0);
x_96 = lean_ctor_get(x_15, 1);
x_97 = lean_ctor_get(x_15, 2);
x_98 = lean_ctor_get(x_15, 3);
x_99 = lean_ctor_get(x_15, 4);
x_100 = lean_ctor_get(x_15, 5);
x_101 = lean_ctor_get(x_15, 6);
x_102 = lean_ctor_get(x_15, 7);
x_103 = lean_ctor_get_uint8(x_15, sizeof(void*)*16);
x_104 = lean_ctor_get(x_15, 8);
x_105 = lean_ctor_get(x_15, 9);
x_106 = lean_ctor_get(x_15, 10);
x_107 = lean_ctor_get(x_15, 11);
x_108 = lean_ctor_get(x_15, 12);
x_109 = lean_ctor_get(x_15, 13);
x_110 = lean_ctor_get(x_15, 15);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_15);
x_111 = lean_ctor_get(x_16, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_16, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_16, 3);
lean_inc(x_113);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 x_114 = x_16;
} else {
 lean_dec_ref(x_16);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_17, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_17, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_17, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_17, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_17, 4);
lean_inc(x_119);
x_120 = lean_ctor_get(x_17, 5);
lean_inc(x_120);
x_121 = lean_ctor_get(x_17, 6);
lean_inc(x_121);
x_122 = lean_ctor_get(x_17, 7);
lean_inc(x_122);
x_123 = lean_ctor_get(x_17, 8);
lean_inc(x_123);
x_124 = lean_ctor_get(x_17, 9);
lean_inc(x_124);
x_125 = lean_ctor_get(x_17, 10);
lean_inc(x_125);
x_126 = lean_ctor_get(x_17, 11);
lean_inc(x_126);
x_127 = lean_ctor_get(x_17, 12);
lean_inc(x_127);
x_128 = lean_ctor_get(x_17, 13);
lean_inc(x_128);
x_129 = lean_ctor_get_uint8(x_17, sizeof(void*)*19);
x_130 = lean_ctor_get(x_17, 14);
lean_inc(x_130);
x_131 = lean_ctor_get(x_17, 15);
lean_inc(x_131);
x_132 = lean_ctor_get(x_17, 16);
lean_inc(x_132);
x_133 = lean_ctor_get(x_17, 17);
lean_inc(x_133);
x_134 = lean_ctor_get(x_17, 18);
lean_inc(x_134);
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
 x_135 = x_17;
} else {
 lean_dec_ref(x_17);
 x_135 = lean_box(0);
}
x_136 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_137 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_136, x_122, x_11);
lean_dec(x_11);
lean_dec(x_8);
if (lean_is_scalar(x_135)) {
 x_138 = lean_alloc_ctor(0, 19, 1);
} else {
 x_138 = x_135;
}
lean_ctor_set(x_138, 0, x_115);
lean_ctor_set(x_138, 1, x_116);
lean_ctor_set(x_138, 2, x_117);
lean_ctor_set(x_138, 3, x_118);
lean_ctor_set(x_138, 4, x_119);
lean_ctor_set(x_138, 5, x_120);
lean_ctor_set(x_138, 6, x_121);
lean_ctor_set(x_138, 7, x_137);
lean_ctor_set(x_138, 8, x_123);
lean_ctor_set(x_138, 9, x_124);
lean_ctor_set(x_138, 10, x_125);
lean_ctor_set(x_138, 11, x_126);
lean_ctor_set(x_138, 12, x_127);
lean_ctor_set(x_138, 13, x_128);
lean_ctor_set(x_138, 14, x_130);
lean_ctor_set(x_138, 15, x_131);
lean_ctor_set(x_138, 16, x_132);
lean_ctor_set(x_138, 17, x_133);
lean_ctor_set(x_138, 18, x_134);
lean_ctor_set_uint8(x_138, sizeof(void*)*19, x_129);
if (lean_is_scalar(x_114)) {
 x_139 = lean_alloc_ctor(0, 4, 0);
} else {
 x_139 = x_114;
}
lean_ctor_set(x_139, 0, x_111);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_139, 2, x_112);
lean_ctor_set(x_139, 3, x_113);
x_140 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_140, 0, x_95);
lean_ctor_set(x_140, 1, x_96);
lean_ctor_set(x_140, 2, x_97);
lean_ctor_set(x_140, 3, x_98);
lean_ctor_set(x_140, 4, x_99);
lean_ctor_set(x_140, 5, x_100);
lean_ctor_set(x_140, 6, x_101);
lean_ctor_set(x_140, 7, x_102);
lean_ctor_set(x_140, 8, x_104);
lean_ctor_set(x_140, 9, x_105);
lean_ctor_set(x_140, 10, x_106);
lean_ctor_set(x_140, 11, x_107);
lean_ctor_set(x_140, 12, x_108);
lean_ctor_set(x_140, 13, x_109);
lean_ctor_set(x_140, 14, x_139);
lean_ctor_set(x_140, 15, x_110);
lean_ctor_set_uint8(x_140, sizeof(void*)*16, x_103);
x_141 = lean_st_ref_set(x_2, x_140, x_18);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_box(0);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_146 = lean_st_ref_take(x_2, x_7);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_147, 14);
lean_inc(x_148);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_146, 1);
lean_inc(x_150);
lean_dec(x_146);
x_151 = !lean_is_exclusive(x_147);
if (x_151 == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_147, 14);
lean_dec(x_152);
x_153 = !lean_is_exclusive(x_148);
if (x_153 == 0)
{
lean_object* x_154; uint8_t x_155; 
x_154 = lean_ctor_get(x_148, 1);
lean_dec(x_154);
x_155 = !lean_is_exclusive(x_149);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_156 = lean_ctor_get(x_149, 6);
x_157 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_158 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_157, x_156, x_11);
lean_dec(x_11);
lean_dec(x_8);
lean_ctor_set(x_149, 6, x_158);
x_159 = lean_st_ref_set(x_2, x_147, x_150);
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_159, 0);
lean_dec(x_161);
x_162 = lean_box(0);
lean_ctor_set(x_159, 0, x_162);
return x_159;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
lean_dec(x_159);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_166 = lean_ctor_get(x_149, 0);
x_167 = lean_ctor_get(x_149, 1);
x_168 = lean_ctor_get(x_149, 2);
x_169 = lean_ctor_get(x_149, 3);
x_170 = lean_ctor_get(x_149, 4);
x_171 = lean_ctor_get(x_149, 5);
x_172 = lean_ctor_get(x_149, 6);
x_173 = lean_ctor_get(x_149, 7);
x_174 = lean_ctor_get(x_149, 8);
x_175 = lean_ctor_get(x_149, 9);
x_176 = lean_ctor_get(x_149, 10);
x_177 = lean_ctor_get(x_149, 11);
x_178 = lean_ctor_get(x_149, 12);
x_179 = lean_ctor_get(x_149, 13);
x_180 = lean_ctor_get_uint8(x_149, sizeof(void*)*19);
x_181 = lean_ctor_get(x_149, 14);
x_182 = lean_ctor_get(x_149, 15);
x_183 = lean_ctor_get(x_149, 16);
x_184 = lean_ctor_get(x_149, 17);
x_185 = lean_ctor_get(x_149, 18);
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
lean_dec(x_149);
x_186 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_187 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_186, x_172, x_11);
lean_dec(x_11);
lean_dec(x_8);
x_188 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_188, 0, x_166);
lean_ctor_set(x_188, 1, x_167);
lean_ctor_set(x_188, 2, x_168);
lean_ctor_set(x_188, 3, x_169);
lean_ctor_set(x_188, 4, x_170);
lean_ctor_set(x_188, 5, x_171);
lean_ctor_set(x_188, 6, x_187);
lean_ctor_set(x_188, 7, x_173);
lean_ctor_set(x_188, 8, x_174);
lean_ctor_set(x_188, 9, x_175);
lean_ctor_set(x_188, 10, x_176);
lean_ctor_set(x_188, 11, x_177);
lean_ctor_set(x_188, 12, x_178);
lean_ctor_set(x_188, 13, x_179);
lean_ctor_set(x_188, 14, x_181);
lean_ctor_set(x_188, 15, x_182);
lean_ctor_set(x_188, 16, x_183);
lean_ctor_set(x_188, 17, x_184);
lean_ctor_set(x_188, 18, x_185);
lean_ctor_set_uint8(x_188, sizeof(void*)*19, x_180);
lean_ctor_set(x_148, 1, x_188);
x_189 = lean_st_ref_set(x_2, x_147, x_150);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_191 = x_189;
} else {
 lean_dec_ref(x_189);
 x_191 = lean_box(0);
}
x_192 = lean_box(0);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_190);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_194 = lean_ctor_get(x_148, 0);
x_195 = lean_ctor_get(x_148, 2);
x_196 = lean_ctor_get(x_148, 3);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_148);
x_197 = lean_ctor_get(x_149, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_149, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_149, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_149, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_149, 4);
lean_inc(x_201);
x_202 = lean_ctor_get(x_149, 5);
lean_inc(x_202);
x_203 = lean_ctor_get(x_149, 6);
lean_inc(x_203);
x_204 = lean_ctor_get(x_149, 7);
lean_inc(x_204);
x_205 = lean_ctor_get(x_149, 8);
lean_inc(x_205);
x_206 = lean_ctor_get(x_149, 9);
lean_inc(x_206);
x_207 = lean_ctor_get(x_149, 10);
lean_inc(x_207);
x_208 = lean_ctor_get(x_149, 11);
lean_inc(x_208);
x_209 = lean_ctor_get(x_149, 12);
lean_inc(x_209);
x_210 = lean_ctor_get(x_149, 13);
lean_inc(x_210);
x_211 = lean_ctor_get_uint8(x_149, sizeof(void*)*19);
x_212 = lean_ctor_get(x_149, 14);
lean_inc(x_212);
x_213 = lean_ctor_get(x_149, 15);
lean_inc(x_213);
x_214 = lean_ctor_get(x_149, 16);
lean_inc(x_214);
x_215 = lean_ctor_get(x_149, 17);
lean_inc(x_215);
x_216 = lean_ctor_get(x_149, 18);
lean_inc(x_216);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 lean_ctor_release(x_149, 3);
 lean_ctor_release(x_149, 4);
 lean_ctor_release(x_149, 5);
 lean_ctor_release(x_149, 6);
 lean_ctor_release(x_149, 7);
 lean_ctor_release(x_149, 8);
 lean_ctor_release(x_149, 9);
 lean_ctor_release(x_149, 10);
 lean_ctor_release(x_149, 11);
 lean_ctor_release(x_149, 12);
 lean_ctor_release(x_149, 13);
 lean_ctor_release(x_149, 14);
 lean_ctor_release(x_149, 15);
 lean_ctor_release(x_149, 16);
 lean_ctor_release(x_149, 17);
 lean_ctor_release(x_149, 18);
 x_217 = x_149;
} else {
 lean_dec_ref(x_149);
 x_217 = lean_box(0);
}
x_218 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_219 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_218, x_203, x_11);
lean_dec(x_11);
lean_dec(x_8);
if (lean_is_scalar(x_217)) {
 x_220 = lean_alloc_ctor(0, 19, 1);
} else {
 x_220 = x_217;
}
lean_ctor_set(x_220, 0, x_197);
lean_ctor_set(x_220, 1, x_198);
lean_ctor_set(x_220, 2, x_199);
lean_ctor_set(x_220, 3, x_200);
lean_ctor_set(x_220, 4, x_201);
lean_ctor_set(x_220, 5, x_202);
lean_ctor_set(x_220, 6, x_219);
lean_ctor_set(x_220, 7, x_204);
lean_ctor_set(x_220, 8, x_205);
lean_ctor_set(x_220, 9, x_206);
lean_ctor_set(x_220, 10, x_207);
lean_ctor_set(x_220, 11, x_208);
lean_ctor_set(x_220, 12, x_209);
lean_ctor_set(x_220, 13, x_210);
lean_ctor_set(x_220, 14, x_212);
lean_ctor_set(x_220, 15, x_213);
lean_ctor_set(x_220, 16, x_214);
lean_ctor_set(x_220, 17, x_215);
lean_ctor_set(x_220, 18, x_216);
lean_ctor_set_uint8(x_220, sizeof(void*)*19, x_211);
x_221 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_221, 0, x_194);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set(x_221, 2, x_195);
lean_ctor_set(x_221, 3, x_196);
lean_ctor_set(x_147, 14, x_221);
x_222 = lean_st_ref_set(x_2, x_147, x_150);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_224 = x_222;
} else {
 lean_dec_ref(x_222);
 x_224 = lean_box(0);
}
x_225 = lean_box(0);
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_223);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_227 = lean_ctor_get(x_147, 0);
x_228 = lean_ctor_get(x_147, 1);
x_229 = lean_ctor_get(x_147, 2);
x_230 = lean_ctor_get(x_147, 3);
x_231 = lean_ctor_get(x_147, 4);
x_232 = lean_ctor_get(x_147, 5);
x_233 = lean_ctor_get(x_147, 6);
x_234 = lean_ctor_get(x_147, 7);
x_235 = lean_ctor_get_uint8(x_147, sizeof(void*)*16);
x_236 = lean_ctor_get(x_147, 8);
x_237 = lean_ctor_get(x_147, 9);
x_238 = lean_ctor_get(x_147, 10);
x_239 = lean_ctor_get(x_147, 11);
x_240 = lean_ctor_get(x_147, 12);
x_241 = lean_ctor_get(x_147, 13);
x_242 = lean_ctor_get(x_147, 15);
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
lean_dec(x_147);
x_243 = lean_ctor_get(x_148, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_148, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_148, 3);
lean_inc(x_245);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 lean_ctor_release(x_148, 3);
 x_246 = x_148;
} else {
 lean_dec_ref(x_148);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_149, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_149, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_149, 2);
lean_inc(x_249);
x_250 = lean_ctor_get(x_149, 3);
lean_inc(x_250);
x_251 = lean_ctor_get(x_149, 4);
lean_inc(x_251);
x_252 = lean_ctor_get(x_149, 5);
lean_inc(x_252);
x_253 = lean_ctor_get(x_149, 6);
lean_inc(x_253);
x_254 = lean_ctor_get(x_149, 7);
lean_inc(x_254);
x_255 = lean_ctor_get(x_149, 8);
lean_inc(x_255);
x_256 = lean_ctor_get(x_149, 9);
lean_inc(x_256);
x_257 = lean_ctor_get(x_149, 10);
lean_inc(x_257);
x_258 = lean_ctor_get(x_149, 11);
lean_inc(x_258);
x_259 = lean_ctor_get(x_149, 12);
lean_inc(x_259);
x_260 = lean_ctor_get(x_149, 13);
lean_inc(x_260);
x_261 = lean_ctor_get_uint8(x_149, sizeof(void*)*19);
x_262 = lean_ctor_get(x_149, 14);
lean_inc(x_262);
x_263 = lean_ctor_get(x_149, 15);
lean_inc(x_263);
x_264 = lean_ctor_get(x_149, 16);
lean_inc(x_264);
x_265 = lean_ctor_get(x_149, 17);
lean_inc(x_265);
x_266 = lean_ctor_get(x_149, 18);
lean_inc(x_266);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 lean_ctor_release(x_149, 3);
 lean_ctor_release(x_149, 4);
 lean_ctor_release(x_149, 5);
 lean_ctor_release(x_149, 6);
 lean_ctor_release(x_149, 7);
 lean_ctor_release(x_149, 8);
 lean_ctor_release(x_149, 9);
 lean_ctor_release(x_149, 10);
 lean_ctor_release(x_149, 11);
 lean_ctor_release(x_149, 12);
 lean_ctor_release(x_149, 13);
 lean_ctor_release(x_149, 14);
 lean_ctor_release(x_149, 15);
 lean_ctor_release(x_149, 16);
 lean_ctor_release(x_149, 17);
 lean_ctor_release(x_149, 18);
 x_267 = x_149;
} else {
 lean_dec_ref(x_149);
 x_267 = lean_box(0);
}
x_268 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_269 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__5(x_8, x_268, x_253, x_11);
lean_dec(x_11);
lean_dec(x_8);
if (lean_is_scalar(x_267)) {
 x_270 = lean_alloc_ctor(0, 19, 1);
} else {
 x_270 = x_267;
}
lean_ctor_set(x_270, 0, x_247);
lean_ctor_set(x_270, 1, x_248);
lean_ctor_set(x_270, 2, x_249);
lean_ctor_set(x_270, 3, x_250);
lean_ctor_set(x_270, 4, x_251);
lean_ctor_set(x_270, 5, x_252);
lean_ctor_set(x_270, 6, x_269);
lean_ctor_set(x_270, 7, x_254);
lean_ctor_set(x_270, 8, x_255);
lean_ctor_set(x_270, 9, x_256);
lean_ctor_set(x_270, 10, x_257);
lean_ctor_set(x_270, 11, x_258);
lean_ctor_set(x_270, 12, x_259);
lean_ctor_set(x_270, 13, x_260);
lean_ctor_set(x_270, 14, x_262);
lean_ctor_set(x_270, 15, x_263);
lean_ctor_set(x_270, 16, x_264);
lean_ctor_set(x_270, 17, x_265);
lean_ctor_set(x_270, 18, x_266);
lean_ctor_set_uint8(x_270, sizeof(void*)*19, x_261);
if (lean_is_scalar(x_246)) {
 x_271 = lean_alloc_ctor(0, 4, 0);
} else {
 x_271 = x_246;
}
lean_ctor_set(x_271, 0, x_243);
lean_ctor_set(x_271, 1, x_270);
lean_ctor_set(x_271, 2, x_244);
lean_ctor_set(x_271, 3, x_245);
x_272 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_272, 0, x_227);
lean_ctor_set(x_272, 1, x_228);
lean_ctor_set(x_272, 2, x_229);
lean_ctor_set(x_272, 3, x_230);
lean_ctor_set(x_272, 4, x_231);
lean_ctor_set(x_272, 5, x_232);
lean_ctor_set(x_272, 6, x_233);
lean_ctor_set(x_272, 7, x_234);
lean_ctor_set(x_272, 8, x_236);
lean_ctor_set(x_272, 9, x_237);
lean_ctor_set(x_272, 10, x_238);
lean_ctor_set(x_272, 11, x_239);
lean_ctor_set(x_272, 12, x_240);
lean_ctor_set(x_272, 13, x_241);
lean_ctor_set(x_272, 14, x_271);
lean_ctor_set(x_272, 15, x_242);
lean_ctor_set_uint8(x_272, sizeof(void*)*16, x_235);
x_273 = lean_st_ref_set(x_2, x_272, x_150);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_275 = x_273;
} else {
 lean_dec_ref(x_273);
 x_275 = lean_box(0);
}
x_276 = lean_box(0);
if (lean_is_scalar(x_275)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_275;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_274);
return x_277;
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
lean_ctor_set_tag(x_27, 8);
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
x_115 = lean_alloc_ctor(8, 2, 0);
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
lean_ctor_set_tag(x_27, 8);
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
x_115 = lean_alloc_ctor(8, 2, 0);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_41; uint8_t x_42; 
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
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__8;
x_42 = lean_int_dec_lt(x_13, x_41);
lean_dec(x_13);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_16, 6);
lean_inc(x_43);
lean_dec(x_16);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
x_45 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_46 = lean_nat_dec_lt(x_14, x_44);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_14);
x_47 = l_outOfBounds___redArg(x_45);
x_18 = x_47;
goto block_40;
}
else
{
lean_object* x_48; 
x_48 = l_Lean_PersistentArray_get_x21___redArg(x_45, x_43, x_14);
lean_dec(x_14);
x_18 = x_48;
goto block_40;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_16, 7);
lean_inc(x_49);
lean_dec(x_16);
x_50 = lean_ctor_get(x_49, 2);
lean_inc(x_50);
x_51 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
x_52 = lean_nat_dec_lt(x_14, x_50);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_49);
lean_dec(x_14);
x_53 = l_outOfBounds___redArg(x_51);
x_18 = x_53;
goto block_40;
}
else
{
lean_object* x_54; 
x_54 = l_Lean_PersistentArray_get_x21___redArg(x_51, x_49, x_14);
lean_dec(x_14);
x_18 = x_54;
goto block_40;
}
}
block_40:
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
x_14 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_13, x_1);
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
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_270; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
x_270 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_17, x_18);
if (x_270 == 0)
{
uint8_t x_271; 
x_271 = l_Int_Linear_Poly_isNegEq(x_17, x_18);
x_19 = x_271;
goto block_269;
}
else
{
x_19 = x_270;
goto block_269;
}
block_269:
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
x_38 = lean_ctor_get(x_29, 8);
x_39 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_38, x_4);
lean_dec(x_18);
lean_ctor_set(x_29, 8, x_39);
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
lean_ctor_set_tag(x_26, 12);
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
lean_ctor_set_tag(x_26, 12);
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
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
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
x_89 = lean_ctor_get_uint8(x_29, sizeof(void*)*19);
x_90 = lean_ctor_get(x_29, 14);
x_91 = lean_ctor_get(x_29, 15);
x_92 = lean_ctor_get(x_29, 16);
x_93 = lean_ctor_get(x_29, 17);
x_94 = lean_ctor_get(x_29, 18);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
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
x_95 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_83, x_4);
lean_dec(x_18);
x_96 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_96, 0, x_75);
lean_ctor_set(x_96, 1, x_76);
lean_ctor_set(x_96, 2, x_77);
lean_ctor_set(x_96, 3, x_78);
lean_ctor_set(x_96, 4, x_79);
lean_ctor_set(x_96, 5, x_80);
lean_ctor_set(x_96, 6, x_81);
lean_ctor_set(x_96, 7, x_82);
lean_ctor_set(x_96, 8, x_95);
lean_ctor_set(x_96, 9, x_84);
lean_ctor_set(x_96, 10, x_85);
lean_ctor_set(x_96, 11, x_86);
lean_ctor_set(x_96, 12, x_87);
lean_ctor_set(x_96, 13, x_88);
lean_ctor_set(x_96, 14, x_90);
lean_ctor_set(x_96, 15, x_91);
lean_ctor_set(x_96, 16, x_92);
lean_ctor_set(x_96, 17, x_93);
lean_ctor_set(x_96, 18, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*19, x_89);
lean_ctor_set(x_28, 1, x_96);
x_97 = lean_st_ref_set(x_8, x_27, x_31);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_101 = l_Int_Linear_Poly_addConst(x_17, x_100);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 12);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_102 = x_1;
} else {
 lean_dec_ref(x_1);
 x_102 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_103 = x_6;
} else {
 lean_dec_ref(x_6);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_26);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
if (lean_is_scalar(x_102)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_102;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_5);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
if (lean_is_scalar(x_99)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_99;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_98);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_110 = lean_ctor_get(x_28, 0);
x_111 = lean_ctor_get(x_28, 2);
x_112 = lean_ctor_get(x_28, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_28);
x_113 = lean_ctor_get(x_29, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_29, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_29, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_29, 3);
lean_inc(x_116);
x_117 = lean_ctor_get(x_29, 4);
lean_inc(x_117);
x_118 = lean_ctor_get(x_29, 5);
lean_inc(x_118);
x_119 = lean_ctor_get(x_29, 6);
lean_inc(x_119);
x_120 = lean_ctor_get(x_29, 7);
lean_inc(x_120);
x_121 = lean_ctor_get(x_29, 8);
lean_inc(x_121);
x_122 = lean_ctor_get(x_29, 9);
lean_inc(x_122);
x_123 = lean_ctor_get(x_29, 10);
lean_inc(x_123);
x_124 = lean_ctor_get(x_29, 11);
lean_inc(x_124);
x_125 = lean_ctor_get(x_29, 12);
lean_inc(x_125);
x_126 = lean_ctor_get(x_29, 13);
lean_inc(x_126);
x_127 = lean_ctor_get_uint8(x_29, sizeof(void*)*19);
x_128 = lean_ctor_get(x_29, 14);
lean_inc(x_128);
x_129 = lean_ctor_get(x_29, 15);
lean_inc(x_129);
x_130 = lean_ctor_get(x_29, 16);
lean_inc(x_130);
x_131 = lean_ctor_get(x_29, 17);
lean_inc(x_131);
x_132 = lean_ctor_get(x_29, 18);
lean_inc(x_132);
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
 x_133 = x_29;
} else {
 lean_dec_ref(x_29);
 x_133 = lean_box(0);
}
x_134 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_121, x_4);
lean_dec(x_18);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 19, 1);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_113);
lean_ctor_set(x_135, 1, x_114);
lean_ctor_set(x_135, 2, x_115);
lean_ctor_set(x_135, 3, x_116);
lean_ctor_set(x_135, 4, x_117);
lean_ctor_set(x_135, 5, x_118);
lean_ctor_set(x_135, 6, x_119);
lean_ctor_set(x_135, 7, x_120);
lean_ctor_set(x_135, 8, x_134);
lean_ctor_set(x_135, 9, x_122);
lean_ctor_set(x_135, 10, x_123);
lean_ctor_set(x_135, 11, x_124);
lean_ctor_set(x_135, 12, x_125);
lean_ctor_set(x_135, 13, x_126);
lean_ctor_set(x_135, 14, x_128);
lean_ctor_set(x_135, 15, x_129);
lean_ctor_set(x_135, 16, x_130);
lean_ctor_set(x_135, 17, x_131);
lean_ctor_set(x_135, 18, x_132);
lean_ctor_set_uint8(x_135, sizeof(void*)*19, x_127);
x_136 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_136, 0, x_110);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_111);
lean_ctor_set(x_136, 3, x_112);
lean_ctor_set(x_27, 14, x_136);
x_137 = lean_st_ref_set(x_8, x_27, x_31);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
x_140 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_141 = l_Int_Linear_Poly_addConst(x_17, x_140);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 12);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_142 = x_1;
} else {
 lean_dec_ref(x_1);
 x_142 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_143 = x_6;
} else {
 lean_dec_ref(x_6);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_26);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
if (lean_is_scalar(x_142)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_142;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_5);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_138);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_150 = lean_ctor_get(x_27, 0);
x_151 = lean_ctor_get(x_27, 1);
x_152 = lean_ctor_get(x_27, 2);
x_153 = lean_ctor_get(x_27, 3);
x_154 = lean_ctor_get(x_27, 4);
x_155 = lean_ctor_get(x_27, 5);
x_156 = lean_ctor_get(x_27, 6);
x_157 = lean_ctor_get(x_27, 7);
x_158 = lean_ctor_get_uint8(x_27, sizeof(void*)*16);
x_159 = lean_ctor_get(x_27, 8);
x_160 = lean_ctor_get(x_27, 9);
x_161 = lean_ctor_get(x_27, 10);
x_162 = lean_ctor_get(x_27, 11);
x_163 = lean_ctor_get(x_27, 12);
x_164 = lean_ctor_get(x_27, 13);
x_165 = lean_ctor_get(x_27, 15);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_27);
x_166 = lean_ctor_get(x_28, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_28, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_28, 3);
lean_inc(x_168);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 x_169 = x_28;
} else {
 lean_dec_ref(x_28);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_29, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_29, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_29, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_29, 3);
lean_inc(x_173);
x_174 = lean_ctor_get(x_29, 4);
lean_inc(x_174);
x_175 = lean_ctor_get(x_29, 5);
lean_inc(x_175);
x_176 = lean_ctor_get(x_29, 6);
lean_inc(x_176);
x_177 = lean_ctor_get(x_29, 7);
lean_inc(x_177);
x_178 = lean_ctor_get(x_29, 8);
lean_inc(x_178);
x_179 = lean_ctor_get(x_29, 9);
lean_inc(x_179);
x_180 = lean_ctor_get(x_29, 10);
lean_inc(x_180);
x_181 = lean_ctor_get(x_29, 11);
lean_inc(x_181);
x_182 = lean_ctor_get(x_29, 12);
lean_inc(x_182);
x_183 = lean_ctor_get(x_29, 13);
lean_inc(x_183);
x_184 = lean_ctor_get_uint8(x_29, sizeof(void*)*19);
x_185 = lean_ctor_get(x_29, 14);
lean_inc(x_185);
x_186 = lean_ctor_get(x_29, 15);
lean_inc(x_186);
x_187 = lean_ctor_get(x_29, 16);
lean_inc(x_187);
x_188 = lean_ctor_get(x_29, 17);
lean_inc(x_188);
x_189 = lean_ctor_get(x_29, 18);
lean_inc(x_189);
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
 x_190 = x_29;
} else {
 lean_dec_ref(x_29);
 x_190 = lean_box(0);
}
x_191 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_178, x_4);
lean_dec(x_18);
if (lean_is_scalar(x_190)) {
 x_192 = lean_alloc_ctor(0, 19, 1);
} else {
 x_192 = x_190;
}
lean_ctor_set(x_192, 0, x_170);
lean_ctor_set(x_192, 1, x_171);
lean_ctor_set(x_192, 2, x_172);
lean_ctor_set(x_192, 3, x_173);
lean_ctor_set(x_192, 4, x_174);
lean_ctor_set(x_192, 5, x_175);
lean_ctor_set(x_192, 6, x_176);
lean_ctor_set(x_192, 7, x_177);
lean_ctor_set(x_192, 8, x_191);
lean_ctor_set(x_192, 9, x_179);
lean_ctor_set(x_192, 10, x_180);
lean_ctor_set(x_192, 11, x_181);
lean_ctor_set(x_192, 12, x_182);
lean_ctor_set(x_192, 13, x_183);
lean_ctor_set(x_192, 14, x_185);
lean_ctor_set(x_192, 15, x_186);
lean_ctor_set(x_192, 16, x_187);
lean_ctor_set(x_192, 17, x_188);
lean_ctor_set(x_192, 18, x_189);
lean_ctor_set_uint8(x_192, sizeof(void*)*19, x_184);
if (lean_is_scalar(x_169)) {
 x_193 = lean_alloc_ctor(0, 4, 0);
} else {
 x_193 = x_169;
}
lean_ctor_set(x_193, 0, x_166);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set(x_193, 2, x_167);
lean_ctor_set(x_193, 3, x_168);
x_194 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_194, 0, x_150);
lean_ctor_set(x_194, 1, x_151);
lean_ctor_set(x_194, 2, x_152);
lean_ctor_set(x_194, 3, x_153);
lean_ctor_set(x_194, 4, x_154);
lean_ctor_set(x_194, 5, x_155);
lean_ctor_set(x_194, 6, x_156);
lean_ctor_set(x_194, 7, x_157);
lean_ctor_set(x_194, 8, x_159);
lean_ctor_set(x_194, 9, x_160);
lean_ctor_set(x_194, 10, x_161);
lean_ctor_set(x_194, 11, x_162);
lean_ctor_set(x_194, 12, x_163);
lean_ctor_set(x_194, 13, x_164);
lean_ctor_set(x_194, 14, x_193);
lean_ctor_set(x_194, 15, x_165);
lean_ctor_set_uint8(x_194, sizeof(void*)*16, x_158);
x_195 = lean_st_ref_set(x_8, x_194, x_31);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_197 = x_195;
} else {
 lean_dec_ref(x_195);
 x_197 = lean_box(0);
}
x_198 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_199 = l_Int_Linear_Poly_addConst(x_17, x_198);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 12);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_200 = x_1;
} else {
 lean_dec_ref(x_1);
 x_200 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_201 = x_6;
} else {
 lean_dec_ref(x_6);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_26);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
if (lean_is_scalar(x_200)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_200;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_5);
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_205);
if (lean_is_scalar(x_197)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_197;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_196);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_208 = lean_ctor_get(x_26, 1);
lean_inc(x_208);
lean_dec(x_26);
x_209 = lean_ctor_get(x_27, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_27, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_27, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_27, 3);
lean_inc(x_212);
x_213 = lean_ctor_get(x_27, 4);
lean_inc(x_213);
x_214 = lean_ctor_get(x_27, 5);
lean_inc(x_214);
x_215 = lean_ctor_get(x_27, 6);
lean_inc(x_215);
x_216 = lean_ctor_get(x_27, 7);
lean_inc(x_216);
x_217 = lean_ctor_get_uint8(x_27, sizeof(void*)*16);
x_218 = lean_ctor_get(x_27, 8);
lean_inc(x_218);
x_219 = lean_ctor_get(x_27, 9);
lean_inc(x_219);
x_220 = lean_ctor_get(x_27, 10);
lean_inc(x_220);
x_221 = lean_ctor_get(x_27, 11);
lean_inc(x_221);
x_222 = lean_ctor_get(x_27, 12);
lean_inc(x_222);
x_223 = lean_ctor_get(x_27, 13);
lean_inc(x_223);
x_224 = lean_ctor_get(x_27, 15);
lean_inc(x_224);
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
 x_225 = x_27;
} else {
 lean_dec_ref(x_27);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_28, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_28, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_28, 3);
lean_inc(x_228);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 x_229 = x_28;
} else {
 lean_dec_ref(x_28);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_29, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_29, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_29, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_29, 3);
lean_inc(x_233);
x_234 = lean_ctor_get(x_29, 4);
lean_inc(x_234);
x_235 = lean_ctor_get(x_29, 5);
lean_inc(x_235);
x_236 = lean_ctor_get(x_29, 6);
lean_inc(x_236);
x_237 = lean_ctor_get(x_29, 7);
lean_inc(x_237);
x_238 = lean_ctor_get(x_29, 8);
lean_inc(x_238);
x_239 = lean_ctor_get(x_29, 9);
lean_inc(x_239);
x_240 = lean_ctor_get(x_29, 10);
lean_inc(x_240);
x_241 = lean_ctor_get(x_29, 11);
lean_inc(x_241);
x_242 = lean_ctor_get(x_29, 12);
lean_inc(x_242);
x_243 = lean_ctor_get(x_29, 13);
lean_inc(x_243);
x_244 = lean_ctor_get_uint8(x_29, sizeof(void*)*19);
x_245 = lean_ctor_get(x_29, 14);
lean_inc(x_245);
x_246 = lean_ctor_get(x_29, 15);
lean_inc(x_246);
x_247 = lean_ctor_get(x_29, 16);
lean_inc(x_247);
x_248 = lean_ctor_get(x_29, 17);
lean_inc(x_248);
x_249 = lean_ctor_get(x_29, 18);
lean_inc(x_249);
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
 x_250 = x_29;
} else {
 lean_dec_ref(x_29);
 x_250 = lean_box(0);
}
x_251 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_238, x_4);
lean_dec(x_18);
if (lean_is_scalar(x_250)) {
 x_252 = lean_alloc_ctor(0, 19, 1);
} else {
 x_252 = x_250;
}
lean_ctor_set(x_252, 0, x_230);
lean_ctor_set(x_252, 1, x_231);
lean_ctor_set(x_252, 2, x_232);
lean_ctor_set(x_252, 3, x_233);
lean_ctor_set(x_252, 4, x_234);
lean_ctor_set(x_252, 5, x_235);
lean_ctor_set(x_252, 6, x_236);
lean_ctor_set(x_252, 7, x_237);
lean_ctor_set(x_252, 8, x_251);
lean_ctor_set(x_252, 9, x_239);
lean_ctor_set(x_252, 10, x_240);
lean_ctor_set(x_252, 11, x_241);
lean_ctor_set(x_252, 12, x_242);
lean_ctor_set(x_252, 13, x_243);
lean_ctor_set(x_252, 14, x_245);
lean_ctor_set(x_252, 15, x_246);
lean_ctor_set(x_252, 16, x_247);
lean_ctor_set(x_252, 17, x_248);
lean_ctor_set(x_252, 18, x_249);
lean_ctor_set_uint8(x_252, sizeof(void*)*19, x_244);
if (lean_is_scalar(x_229)) {
 x_253 = lean_alloc_ctor(0, 4, 0);
} else {
 x_253 = x_229;
}
lean_ctor_set(x_253, 0, x_226);
lean_ctor_set(x_253, 1, x_252);
lean_ctor_set(x_253, 2, x_227);
lean_ctor_set(x_253, 3, x_228);
if (lean_is_scalar(x_225)) {
 x_254 = lean_alloc_ctor(0, 16, 1);
} else {
 x_254 = x_225;
}
lean_ctor_set(x_254, 0, x_209);
lean_ctor_set(x_254, 1, x_210);
lean_ctor_set(x_254, 2, x_211);
lean_ctor_set(x_254, 3, x_212);
lean_ctor_set(x_254, 4, x_213);
lean_ctor_set(x_254, 5, x_214);
lean_ctor_set(x_254, 6, x_215);
lean_ctor_set(x_254, 7, x_216);
lean_ctor_set(x_254, 8, x_218);
lean_ctor_set(x_254, 9, x_219);
lean_ctor_set(x_254, 10, x_220);
lean_ctor_set(x_254, 11, x_221);
lean_ctor_set(x_254, 12, x_222);
lean_ctor_set(x_254, 13, x_223);
lean_ctor_set(x_254, 14, x_253);
lean_ctor_set(x_254, 15, x_224);
lean_ctor_set_uint8(x_254, sizeof(void*)*16, x_217);
x_255 = lean_st_ref_set(x_8, x_254, x_208);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_257 = x_255;
} else {
 lean_dec_ref(x_255);
 x_257 = lean_box(0);
}
x_258 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_259 = l_Int_Linear_Poly_addConst(x_17, x_258);
lean_inc(x_6);
lean_inc(x_1);
x_260 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_260, 0, x_1);
lean_ctor_set(x_260, 1, x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_261 = x_1;
} else {
 lean_dec_ref(x_1);
 x_261 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_262 = x_6;
} else {
 lean_dec_ref(x_6);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_259);
lean_ctor_set(x_263, 1, x_260);
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_263);
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_264);
if (lean_is_scalar(x_261)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_261;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_5);
x_267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_267, 0, x_266);
if (lean_is_scalar(x_257)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_257;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_256);
return x_268;
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
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_270; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
x_270 = l_Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_631_(x_17, x_18);
if (x_270 == 0)
{
uint8_t x_271; 
x_271 = l_Int_Linear_Poly_isNegEq(x_17, x_18);
x_19 = x_271;
goto block_269;
}
else
{
x_19 = x_270;
goto block_269;
}
block_269:
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
x_38 = lean_ctor_get(x_29, 8);
x_39 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_38, x_4);
lean_dec(x_18);
lean_ctor_set(x_29, 8, x_39);
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
lean_ctor_set_tag(x_26, 12);
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
lean_ctor_set_tag(x_26, 12);
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
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
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
x_89 = lean_ctor_get_uint8(x_29, sizeof(void*)*19);
x_90 = lean_ctor_get(x_29, 14);
x_91 = lean_ctor_get(x_29, 15);
x_92 = lean_ctor_get(x_29, 16);
x_93 = lean_ctor_get(x_29, 17);
x_94 = lean_ctor_get(x_29, 18);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
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
x_95 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_83, x_4);
lean_dec(x_18);
x_96 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_96, 0, x_75);
lean_ctor_set(x_96, 1, x_76);
lean_ctor_set(x_96, 2, x_77);
lean_ctor_set(x_96, 3, x_78);
lean_ctor_set(x_96, 4, x_79);
lean_ctor_set(x_96, 5, x_80);
lean_ctor_set(x_96, 6, x_81);
lean_ctor_set(x_96, 7, x_82);
lean_ctor_set(x_96, 8, x_95);
lean_ctor_set(x_96, 9, x_84);
lean_ctor_set(x_96, 10, x_85);
lean_ctor_set(x_96, 11, x_86);
lean_ctor_set(x_96, 12, x_87);
lean_ctor_set(x_96, 13, x_88);
lean_ctor_set(x_96, 14, x_90);
lean_ctor_set(x_96, 15, x_91);
lean_ctor_set(x_96, 16, x_92);
lean_ctor_set(x_96, 17, x_93);
lean_ctor_set(x_96, 18, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*19, x_89);
lean_ctor_set(x_28, 1, x_96);
x_97 = lean_st_ref_set(x_8, x_27, x_31);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_101 = l_Int_Linear_Poly_addConst(x_17, x_100);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 12);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_102 = x_1;
} else {
 lean_dec_ref(x_1);
 x_102 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_103 = x_6;
} else {
 lean_dec_ref(x_6);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_26);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
if (lean_is_scalar(x_102)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_102;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_5);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
if (lean_is_scalar(x_99)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_99;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_98);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_110 = lean_ctor_get(x_28, 0);
x_111 = lean_ctor_get(x_28, 2);
x_112 = lean_ctor_get(x_28, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_28);
x_113 = lean_ctor_get(x_29, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_29, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_29, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_29, 3);
lean_inc(x_116);
x_117 = lean_ctor_get(x_29, 4);
lean_inc(x_117);
x_118 = lean_ctor_get(x_29, 5);
lean_inc(x_118);
x_119 = lean_ctor_get(x_29, 6);
lean_inc(x_119);
x_120 = lean_ctor_get(x_29, 7);
lean_inc(x_120);
x_121 = lean_ctor_get(x_29, 8);
lean_inc(x_121);
x_122 = lean_ctor_get(x_29, 9);
lean_inc(x_122);
x_123 = lean_ctor_get(x_29, 10);
lean_inc(x_123);
x_124 = lean_ctor_get(x_29, 11);
lean_inc(x_124);
x_125 = lean_ctor_get(x_29, 12);
lean_inc(x_125);
x_126 = lean_ctor_get(x_29, 13);
lean_inc(x_126);
x_127 = lean_ctor_get_uint8(x_29, sizeof(void*)*19);
x_128 = lean_ctor_get(x_29, 14);
lean_inc(x_128);
x_129 = lean_ctor_get(x_29, 15);
lean_inc(x_129);
x_130 = lean_ctor_get(x_29, 16);
lean_inc(x_130);
x_131 = lean_ctor_get(x_29, 17);
lean_inc(x_131);
x_132 = lean_ctor_get(x_29, 18);
lean_inc(x_132);
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
 x_133 = x_29;
} else {
 lean_dec_ref(x_29);
 x_133 = lean_box(0);
}
x_134 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_121, x_4);
lean_dec(x_18);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 19, 1);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_113);
lean_ctor_set(x_135, 1, x_114);
lean_ctor_set(x_135, 2, x_115);
lean_ctor_set(x_135, 3, x_116);
lean_ctor_set(x_135, 4, x_117);
lean_ctor_set(x_135, 5, x_118);
lean_ctor_set(x_135, 6, x_119);
lean_ctor_set(x_135, 7, x_120);
lean_ctor_set(x_135, 8, x_134);
lean_ctor_set(x_135, 9, x_122);
lean_ctor_set(x_135, 10, x_123);
lean_ctor_set(x_135, 11, x_124);
lean_ctor_set(x_135, 12, x_125);
lean_ctor_set(x_135, 13, x_126);
lean_ctor_set(x_135, 14, x_128);
lean_ctor_set(x_135, 15, x_129);
lean_ctor_set(x_135, 16, x_130);
lean_ctor_set(x_135, 17, x_131);
lean_ctor_set(x_135, 18, x_132);
lean_ctor_set_uint8(x_135, sizeof(void*)*19, x_127);
x_136 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_136, 0, x_110);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_111);
lean_ctor_set(x_136, 3, x_112);
lean_ctor_set(x_27, 14, x_136);
x_137 = lean_st_ref_set(x_8, x_27, x_31);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
x_140 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_141 = l_Int_Linear_Poly_addConst(x_17, x_140);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 12);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_142 = x_1;
} else {
 lean_dec_ref(x_1);
 x_142 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_143 = x_6;
} else {
 lean_dec_ref(x_6);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_26);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
if (lean_is_scalar(x_142)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_142;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_5);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_138);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_150 = lean_ctor_get(x_27, 0);
x_151 = lean_ctor_get(x_27, 1);
x_152 = lean_ctor_get(x_27, 2);
x_153 = lean_ctor_get(x_27, 3);
x_154 = lean_ctor_get(x_27, 4);
x_155 = lean_ctor_get(x_27, 5);
x_156 = lean_ctor_get(x_27, 6);
x_157 = lean_ctor_get(x_27, 7);
x_158 = lean_ctor_get_uint8(x_27, sizeof(void*)*16);
x_159 = lean_ctor_get(x_27, 8);
x_160 = lean_ctor_get(x_27, 9);
x_161 = lean_ctor_get(x_27, 10);
x_162 = lean_ctor_get(x_27, 11);
x_163 = lean_ctor_get(x_27, 12);
x_164 = lean_ctor_get(x_27, 13);
x_165 = lean_ctor_get(x_27, 15);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_27);
x_166 = lean_ctor_get(x_28, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_28, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_28, 3);
lean_inc(x_168);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 x_169 = x_28;
} else {
 lean_dec_ref(x_28);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_29, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_29, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_29, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_29, 3);
lean_inc(x_173);
x_174 = lean_ctor_get(x_29, 4);
lean_inc(x_174);
x_175 = lean_ctor_get(x_29, 5);
lean_inc(x_175);
x_176 = lean_ctor_get(x_29, 6);
lean_inc(x_176);
x_177 = lean_ctor_get(x_29, 7);
lean_inc(x_177);
x_178 = lean_ctor_get(x_29, 8);
lean_inc(x_178);
x_179 = lean_ctor_get(x_29, 9);
lean_inc(x_179);
x_180 = lean_ctor_get(x_29, 10);
lean_inc(x_180);
x_181 = lean_ctor_get(x_29, 11);
lean_inc(x_181);
x_182 = lean_ctor_get(x_29, 12);
lean_inc(x_182);
x_183 = lean_ctor_get(x_29, 13);
lean_inc(x_183);
x_184 = lean_ctor_get_uint8(x_29, sizeof(void*)*19);
x_185 = lean_ctor_get(x_29, 14);
lean_inc(x_185);
x_186 = lean_ctor_get(x_29, 15);
lean_inc(x_186);
x_187 = lean_ctor_get(x_29, 16);
lean_inc(x_187);
x_188 = lean_ctor_get(x_29, 17);
lean_inc(x_188);
x_189 = lean_ctor_get(x_29, 18);
lean_inc(x_189);
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
 x_190 = x_29;
} else {
 lean_dec_ref(x_29);
 x_190 = lean_box(0);
}
x_191 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_178, x_4);
lean_dec(x_18);
if (lean_is_scalar(x_190)) {
 x_192 = lean_alloc_ctor(0, 19, 1);
} else {
 x_192 = x_190;
}
lean_ctor_set(x_192, 0, x_170);
lean_ctor_set(x_192, 1, x_171);
lean_ctor_set(x_192, 2, x_172);
lean_ctor_set(x_192, 3, x_173);
lean_ctor_set(x_192, 4, x_174);
lean_ctor_set(x_192, 5, x_175);
lean_ctor_set(x_192, 6, x_176);
lean_ctor_set(x_192, 7, x_177);
lean_ctor_set(x_192, 8, x_191);
lean_ctor_set(x_192, 9, x_179);
lean_ctor_set(x_192, 10, x_180);
lean_ctor_set(x_192, 11, x_181);
lean_ctor_set(x_192, 12, x_182);
lean_ctor_set(x_192, 13, x_183);
lean_ctor_set(x_192, 14, x_185);
lean_ctor_set(x_192, 15, x_186);
lean_ctor_set(x_192, 16, x_187);
lean_ctor_set(x_192, 17, x_188);
lean_ctor_set(x_192, 18, x_189);
lean_ctor_set_uint8(x_192, sizeof(void*)*19, x_184);
if (lean_is_scalar(x_169)) {
 x_193 = lean_alloc_ctor(0, 4, 0);
} else {
 x_193 = x_169;
}
lean_ctor_set(x_193, 0, x_166);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set(x_193, 2, x_167);
lean_ctor_set(x_193, 3, x_168);
x_194 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_194, 0, x_150);
lean_ctor_set(x_194, 1, x_151);
lean_ctor_set(x_194, 2, x_152);
lean_ctor_set(x_194, 3, x_153);
lean_ctor_set(x_194, 4, x_154);
lean_ctor_set(x_194, 5, x_155);
lean_ctor_set(x_194, 6, x_156);
lean_ctor_set(x_194, 7, x_157);
lean_ctor_set(x_194, 8, x_159);
lean_ctor_set(x_194, 9, x_160);
lean_ctor_set(x_194, 10, x_161);
lean_ctor_set(x_194, 11, x_162);
lean_ctor_set(x_194, 12, x_163);
lean_ctor_set(x_194, 13, x_164);
lean_ctor_set(x_194, 14, x_193);
lean_ctor_set(x_194, 15, x_165);
lean_ctor_set_uint8(x_194, sizeof(void*)*16, x_158);
x_195 = lean_st_ref_set(x_8, x_194, x_31);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_197 = x_195;
} else {
 lean_dec_ref(x_195);
 x_197 = lean_box(0);
}
x_198 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_199 = l_Int_Linear_Poly_addConst(x_17, x_198);
lean_inc(x_6);
lean_inc(x_1);
lean_ctor_set_tag(x_26, 12);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_200 = x_1;
} else {
 lean_dec_ref(x_1);
 x_200 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_201 = x_6;
} else {
 lean_dec_ref(x_6);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_26);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
if (lean_is_scalar(x_200)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_200;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_5);
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_205);
if (lean_is_scalar(x_197)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_197;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_196);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_208 = lean_ctor_get(x_26, 1);
lean_inc(x_208);
lean_dec(x_26);
x_209 = lean_ctor_get(x_27, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_27, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_27, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_27, 3);
lean_inc(x_212);
x_213 = lean_ctor_get(x_27, 4);
lean_inc(x_213);
x_214 = lean_ctor_get(x_27, 5);
lean_inc(x_214);
x_215 = lean_ctor_get(x_27, 6);
lean_inc(x_215);
x_216 = lean_ctor_get(x_27, 7);
lean_inc(x_216);
x_217 = lean_ctor_get_uint8(x_27, sizeof(void*)*16);
x_218 = lean_ctor_get(x_27, 8);
lean_inc(x_218);
x_219 = lean_ctor_get(x_27, 9);
lean_inc(x_219);
x_220 = lean_ctor_get(x_27, 10);
lean_inc(x_220);
x_221 = lean_ctor_get(x_27, 11);
lean_inc(x_221);
x_222 = lean_ctor_get(x_27, 12);
lean_inc(x_222);
x_223 = lean_ctor_get(x_27, 13);
lean_inc(x_223);
x_224 = lean_ctor_get(x_27, 15);
lean_inc(x_224);
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
 x_225 = x_27;
} else {
 lean_dec_ref(x_27);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_28, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_28, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_28, 3);
lean_inc(x_228);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 x_229 = x_28;
} else {
 lean_dec_ref(x_28);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_29, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_29, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_29, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_29, 3);
lean_inc(x_233);
x_234 = lean_ctor_get(x_29, 4);
lean_inc(x_234);
x_235 = lean_ctor_get(x_29, 5);
lean_inc(x_235);
x_236 = lean_ctor_get(x_29, 6);
lean_inc(x_236);
x_237 = lean_ctor_get(x_29, 7);
lean_inc(x_237);
x_238 = lean_ctor_get(x_29, 8);
lean_inc(x_238);
x_239 = lean_ctor_get(x_29, 9);
lean_inc(x_239);
x_240 = lean_ctor_get(x_29, 10);
lean_inc(x_240);
x_241 = lean_ctor_get(x_29, 11);
lean_inc(x_241);
x_242 = lean_ctor_get(x_29, 12);
lean_inc(x_242);
x_243 = lean_ctor_get(x_29, 13);
lean_inc(x_243);
x_244 = lean_ctor_get_uint8(x_29, sizeof(void*)*19);
x_245 = lean_ctor_get(x_29, 14);
lean_inc(x_245);
x_246 = lean_ctor_get(x_29, 15);
lean_inc(x_246);
x_247 = lean_ctor_get(x_29, 16);
lean_inc(x_247);
x_248 = lean_ctor_get(x_29, 17);
lean_inc(x_248);
x_249 = lean_ctor_get(x_29, 18);
lean_inc(x_249);
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
 x_250 = x_29;
} else {
 lean_dec_ref(x_29);
 x_250 = lean_box(0);
}
x_251 = l_Lean_PersistentArray_modify___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__5(x_18, x_3, x_238, x_4);
lean_dec(x_18);
if (lean_is_scalar(x_250)) {
 x_252 = lean_alloc_ctor(0, 19, 1);
} else {
 x_252 = x_250;
}
lean_ctor_set(x_252, 0, x_230);
lean_ctor_set(x_252, 1, x_231);
lean_ctor_set(x_252, 2, x_232);
lean_ctor_set(x_252, 3, x_233);
lean_ctor_set(x_252, 4, x_234);
lean_ctor_set(x_252, 5, x_235);
lean_ctor_set(x_252, 6, x_236);
lean_ctor_set(x_252, 7, x_237);
lean_ctor_set(x_252, 8, x_251);
lean_ctor_set(x_252, 9, x_239);
lean_ctor_set(x_252, 10, x_240);
lean_ctor_set(x_252, 11, x_241);
lean_ctor_set(x_252, 12, x_242);
lean_ctor_set(x_252, 13, x_243);
lean_ctor_set(x_252, 14, x_245);
lean_ctor_set(x_252, 15, x_246);
lean_ctor_set(x_252, 16, x_247);
lean_ctor_set(x_252, 17, x_248);
lean_ctor_set(x_252, 18, x_249);
lean_ctor_set_uint8(x_252, sizeof(void*)*19, x_244);
if (lean_is_scalar(x_229)) {
 x_253 = lean_alloc_ctor(0, 4, 0);
} else {
 x_253 = x_229;
}
lean_ctor_set(x_253, 0, x_226);
lean_ctor_set(x_253, 1, x_252);
lean_ctor_set(x_253, 2, x_227);
lean_ctor_set(x_253, 3, x_228);
if (lean_is_scalar(x_225)) {
 x_254 = lean_alloc_ctor(0, 16, 1);
} else {
 x_254 = x_225;
}
lean_ctor_set(x_254, 0, x_209);
lean_ctor_set(x_254, 1, x_210);
lean_ctor_set(x_254, 2, x_211);
lean_ctor_set(x_254, 3, x_212);
lean_ctor_set(x_254, 4, x_213);
lean_ctor_set(x_254, 5, x_214);
lean_ctor_set(x_254, 6, x_215);
lean_ctor_set(x_254, 7, x_216);
lean_ctor_set(x_254, 8, x_218);
lean_ctor_set(x_254, 9, x_219);
lean_ctor_set(x_254, 10, x_220);
lean_ctor_set(x_254, 11, x_221);
lean_ctor_set(x_254, 12, x_222);
lean_ctor_set(x_254, 13, x_223);
lean_ctor_set(x_254, 14, x_253);
lean_ctor_set(x_254, 15, x_224);
lean_ctor_set_uint8(x_254, sizeof(void*)*16, x_217);
x_255 = lean_st_ref_set(x_8, x_254, x_208);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_257 = x_255;
} else {
 lean_dec_ref(x_255);
 x_257 = lean_box(0);
}
x_258 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_259 = l_Int_Linear_Poly_addConst(x_17, x_258);
lean_inc(x_6);
lean_inc(x_1);
x_260 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_260, 0, x_1);
lean_ctor_set(x_260, 1, x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_261 = x_1;
} else {
 lean_dec_ref(x_1);
 x_261 = lean_box(0);
}
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_262 = x_6;
} else {
 lean_dec_ref(x_6);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_259);
lean_ctor_set(x_263, 1, x_260);
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_263);
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_264);
if (lean_is_scalar(x_261)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_261;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_5);
x_267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_267, 0, x_266);
if (lean_is_scalar(x_257)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_257;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_256);
return x_268;
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
x_14 = lean_ctor_get(x_13, 8);
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
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_309 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_unbox(x_310);
lean_dec(x_310);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_312 = lean_ctor_get(x_309, 1);
lean_inc(x_312);
lean_dec(x_309);
x_451 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7;
x_452 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_451, x_8, x_312);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_unbox(x_453);
lean_dec(x_453);
if (x_454 == 0)
{
lean_object* x_455; 
x_455 = lean_ctor_get(x_452, 1);
lean_inc(x_455);
lean_dec(x_452);
x_313 = x_2;
x_314 = x_3;
x_315 = x_4;
x_316 = x_5;
x_317 = x_6;
x_318 = x_7;
x_319 = x_8;
x_320 = x_9;
x_321 = x_455;
goto block_450;
}
else
{
uint8_t x_456; 
x_456 = !lean_is_exclusive(x_452);
if (x_456 == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; uint8_t x_460; 
x_457 = lean_ctor_get(x_452, 1);
x_458 = lean_ctor_get(x_452, 0);
lean_dec(x_458);
lean_inc(x_1);
x_459 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_1, x_2, x_457);
x_460 = !lean_is_exclusive(x_459);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_461 = lean_ctor_get(x_459, 0);
x_462 = lean_ctor_get(x_459, 1);
x_463 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
lean_ctor_set_tag(x_459, 7);
lean_ctor_set(x_459, 1, x_461);
lean_ctor_set(x_459, 0, x_463);
lean_ctor_set_tag(x_452, 7);
lean_ctor_set(x_452, 1, x_463);
lean_ctor_set(x_452, 0, x_459);
x_464 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_451, x_452, x_6, x_7, x_8, x_9, x_462);
x_465 = lean_ctor_get(x_464, 1);
lean_inc(x_465);
lean_dec(x_464);
x_313 = x_2;
x_314 = x_3;
x_315 = x_4;
x_316 = x_5;
x_317 = x_6;
x_318 = x_7;
x_319 = x_8;
x_320 = x_9;
x_321 = x_465;
goto block_450;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_466 = lean_ctor_get(x_459, 0);
x_467 = lean_ctor_get(x_459, 1);
lean_inc(x_467);
lean_inc(x_466);
lean_dec(x_459);
x_468 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_469 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_466);
lean_ctor_set_tag(x_452, 7);
lean_ctor_set(x_452, 1, x_468);
lean_ctor_set(x_452, 0, x_469);
x_470 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_451, x_452, x_6, x_7, x_8, x_9, x_467);
x_471 = lean_ctor_get(x_470, 1);
lean_inc(x_471);
lean_dec(x_470);
x_313 = x_2;
x_314 = x_3;
x_315 = x_4;
x_316 = x_5;
x_317 = x_6;
x_318 = x_7;
x_319 = x_8;
x_320 = x_9;
x_321 = x_471;
goto block_450;
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_472 = lean_ctor_get(x_452, 1);
lean_inc(x_472);
lean_dec(x_452);
lean_inc(x_1);
x_473 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_1, x_2, x_472);
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_476 = x_473;
} else {
 lean_dec_ref(x_473);
 x_476 = lean_box(0);
}
x_477 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
if (lean_is_scalar(x_476)) {
 x_478 = lean_alloc_ctor(7, 2, 0);
} else {
 x_478 = x_476;
 lean_ctor_set_tag(x_478, 7);
}
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_474);
x_479 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_477);
x_480 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_451, x_479, x_6, x_7, x_8, x_9, x_475);
x_481 = lean_ctor_get(x_480, 1);
lean_inc(x_481);
lean_dec(x_480);
x_313 = x_2;
x_314 = x_3;
x_315 = x_4;
x_316 = x_5;
x_317 = x_6;
x_318 = x_7;
x_319 = x_8;
x_320 = x_9;
x_321 = x_481;
goto block_450;
}
}
block_450:
{
lean_object* x_322; lean_object* x_323; 
x_322 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(x_1);
lean_inc(x_319);
x_323 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___redArg(x_322, x_313, x_317, x_318, x_319, x_320, x_321);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_ctor_get(x_324, 0);
lean_inc(x_326);
x_327 = l_Int_Linear_Poly_isUnsatLe(x_326);
if (x_327 == 0)
{
uint8_t x_328; 
x_328 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(x_324);
if (x_328 == 0)
{
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_329; 
lean_dec(x_326);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
x_329 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(x_324, x_313, x_317, x_318, x_319, x_320, x_325);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_313);
return x_329;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_326, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_326, 1);
lean_inc(x_331);
lean_dec(x_326);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_inc(x_314);
lean_inc(x_313);
lean_inc(x_324);
x_332 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(x_324, x_313, x_314, x_315, x_316, x_317, x_318, x_319, x_320, x_325);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; uint8_t x_334; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_unbox(x_333);
lean_dec(x_333);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; 
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
lean_dec(x_332);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_313);
x_336 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(x_324, x_313, x_314, x_315, x_316, x_317, x_318, x_319, x_320, x_335);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2;
x_340 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_339, x_319, x_338);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_unbox(x_341);
lean_dec(x_341);
if (x_342 == 0)
{
lean_object* x_343; 
x_343 = lean_ctor_get(x_340, 1);
lean_inc(x_343);
lean_dec(x_340);
x_58 = x_337;
x_59 = x_330;
x_60 = x_331;
x_61 = x_313;
x_62 = x_317;
x_63 = x_318;
x_64 = x_319;
x_65 = x_320;
x_66 = x_343;
goto block_308;
}
else
{
uint8_t x_344; 
x_344 = !lean_is_exclusive(x_340);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_345 = lean_ctor_get(x_340, 1);
x_346 = lean_ctor_get(x_340, 0);
lean_dec(x_346);
lean_inc(x_337);
x_347 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_337, x_313, x_345);
x_348 = !lean_is_exclusive(x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_349 = lean_ctor_get(x_347, 0);
x_350 = lean_ctor_get(x_347, 1);
x_351 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
lean_ctor_set_tag(x_347, 7);
lean_ctor_set(x_347, 1, x_349);
lean_ctor_set(x_347, 0, x_351);
lean_ctor_set_tag(x_340, 7);
lean_ctor_set(x_340, 1, x_351);
lean_ctor_set(x_340, 0, x_347);
x_352 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_339, x_340, x_317, x_318, x_319, x_320, x_350);
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
lean_dec(x_352);
x_58 = x_337;
x_59 = x_330;
x_60 = x_331;
x_61 = x_313;
x_62 = x_317;
x_63 = x_318;
x_64 = x_319;
x_65 = x_320;
x_66 = x_353;
goto block_308;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_354 = lean_ctor_get(x_347, 0);
x_355 = lean_ctor_get(x_347, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_347);
x_356 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_357 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_354);
lean_ctor_set_tag(x_340, 7);
lean_ctor_set(x_340, 1, x_356);
lean_ctor_set(x_340, 0, x_357);
x_358 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_339, x_340, x_317, x_318, x_319, x_320, x_355);
x_359 = lean_ctor_get(x_358, 1);
lean_inc(x_359);
lean_dec(x_358);
x_58 = x_337;
x_59 = x_330;
x_60 = x_331;
x_61 = x_313;
x_62 = x_317;
x_63 = x_318;
x_64 = x_319;
x_65 = x_320;
x_66 = x_359;
goto block_308;
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_360 = lean_ctor_get(x_340, 1);
lean_inc(x_360);
lean_dec(x_340);
lean_inc(x_337);
x_361 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_337, x_313, x_360);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_364 = x_361;
} else {
 lean_dec_ref(x_361);
 x_364 = lean_box(0);
}
x_365 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
if (lean_is_scalar(x_364)) {
 x_366 = lean_alloc_ctor(7, 2, 0);
} else {
 x_366 = x_364;
 lean_ctor_set_tag(x_366, 7);
}
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_362);
x_367 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_365);
x_368 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_339, x_367, x_317, x_318, x_319, x_320, x_363);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
lean_dec(x_368);
x_58 = x_337;
x_59 = x_330;
x_60 = x_331;
x_61 = x_313;
x_62 = x_317;
x_63 = x_318;
x_64 = x_319;
x_65 = x_320;
x_66 = x_369;
goto block_308;
}
}
}
else
{
uint8_t x_370; 
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_313);
x_370 = !lean_is_exclusive(x_336);
if (x_370 == 0)
{
return x_336;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_336, 0);
x_372 = lean_ctor_get(x_336, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_336);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
return x_373;
}
}
}
else
{
uint8_t x_374; 
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_324);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
x_374 = !lean_is_exclusive(x_332);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; 
x_375 = lean_ctor_get(x_332, 0);
lean_dec(x_375);
x_376 = lean_box(0);
lean_ctor_set(x_332, 0, x_376);
return x_332;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_332, 1);
lean_inc(x_377);
lean_dec(x_332);
x_378 = lean_box(0);
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
}
}
else
{
uint8_t x_380; 
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_324);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
x_380 = !lean_is_exclusive(x_332);
if (x_380 == 0)
{
return x_332;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_332, 0);
x_382 = lean_ctor_get(x_332, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_332);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
return x_383;
}
}
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
lean_dec(x_326);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
x_384 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4;
x_385 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_384, x_319, x_325);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_unbox(x_386);
lean_dec(x_386);
if (x_387 == 0)
{
lean_object* x_388; 
lean_dec(x_324);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_313);
x_388 = lean_ctor_get(x_385, 1);
lean_inc(x_388);
lean_dec(x_385);
x_11 = x_388;
goto block_14;
}
else
{
uint8_t x_389; 
x_389 = !lean_is_exclusive(x_385);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_390 = lean_ctor_get(x_385, 1);
x_391 = lean_ctor_get(x_385, 0);
lean_dec(x_391);
x_392 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_324, x_313, x_390);
lean_dec(x_313);
x_393 = !lean_is_exclusive(x_392);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_394 = lean_ctor_get(x_392, 0);
x_395 = lean_ctor_get(x_392, 1);
x_396 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
lean_ctor_set_tag(x_392, 7);
lean_ctor_set(x_392, 1, x_394);
lean_ctor_set(x_392, 0, x_396);
lean_ctor_set_tag(x_385, 7);
lean_ctor_set(x_385, 1, x_396);
lean_ctor_set(x_385, 0, x_392);
x_397 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_384, x_385, x_317, x_318, x_319, x_320, x_395);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
lean_dec(x_397);
x_11 = x_398;
goto block_14;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_399 = lean_ctor_get(x_392, 0);
x_400 = lean_ctor_get(x_392, 1);
lean_inc(x_400);
lean_inc(x_399);
lean_dec(x_392);
x_401 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_402 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_399);
lean_ctor_set_tag(x_385, 7);
lean_ctor_set(x_385, 1, x_401);
lean_ctor_set(x_385, 0, x_402);
x_403 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_384, x_385, x_317, x_318, x_319, x_320, x_400);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
lean_dec(x_403);
x_11 = x_404;
goto block_14;
}
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_405 = lean_ctor_get(x_385, 1);
lean_inc(x_405);
lean_dec(x_385);
x_406 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_324, x_313, x_405);
lean_dec(x_313);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_409 = x_406;
} else {
 lean_dec_ref(x_406);
 x_409 = lean_box(0);
}
x_410 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
if (lean_is_scalar(x_409)) {
 x_411 = lean_alloc_ctor(7, 2, 0);
} else {
 x_411 = x_409;
 lean_ctor_set_tag(x_411, 7);
}
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_407);
x_412 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_410);
x_413 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_384, x_412, x_317, x_318, x_319, x_320, x_408);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
lean_dec(x_413);
x_11 = x_414;
goto block_14;
}
}
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
lean_dec(x_326);
x_415 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6;
x_416 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_415, x_319, x_325);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_unbox(x_417);
lean_dec(x_417);
if (x_418 == 0)
{
lean_object* x_419; 
x_419 = lean_ctor_get(x_416, 1);
lean_inc(x_419);
lean_dec(x_416);
x_15 = x_324;
x_16 = x_313;
x_17 = x_314;
x_18 = x_315;
x_19 = x_316;
x_20 = x_317;
x_21 = x_318;
x_22 = x_319;
x_23 = x_320;
x_24 = x_419;
goto block_33;
}
else
{
uint8_t x_420; 
x_420 = !lean_is_exclusive(x_416);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_421 = lean_ctor_get(x_416, 1);
x_422 = lean_ctor_get(x_416, 0);
lean_dec(x_422);
lean_inc(x_324);
x_423 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_324, x_313, x_421);
x_424 = !lean_is_exclusive(x_423);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_425 = lean_ctor_get(x_423, 0);
x_426 = lean_ctor_get(x_423, 1);
x_427 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
lean_ctor_set_tag(x_423, 7);
lean_ctor_set(x_423, 1, x_425);
lean_ctor_set(x_423, 0, x_427);
lean_ctor_set_tag(x_416, 7);
lean_ctor_set(x_416, 1, x_427);
lean_ctor_set(x_416, 0, x_423);
x_428 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_415, x_416, x_317, x_318, x_319, x_320, x_426);
x_429 = lean_ctor_get(x_428, 1);
lean_inc(x_429);
lean_dec(x_428);
x_15 = x_324;
x_16 = x_313;
x_17 = x_314;
x_18 = x_315;
x_19 = x_316;
x_20 = x_317;
x_21 = x_318;
x_22 = x_319;
x_23 = x_320;
x_24 = x_429;
goto block_33;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_430 = lean_ctor_get(x_423, 0);
x_431 = lean_ctor_get(x_423, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_423);
x_432 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_433 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_430);
lean_ctor_set_tag(x_416, 7);
lean_ctor_set(x_416, 1, x_432);
lean_ctor_set(x_416, 0, x_433);
x_434 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_415, x_416, x_317, x_318, x_319, x_320, x_431);
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
lean_dec(x_434);
x_15 = x_324;
x_16 = x_313;
x_17 = x_314;
x_18 = x_315;
x_19 = x_316;
x_20 = x_317;
x_21 = x_318;
x_22 = x_319;
x_23 = x_320;
x_24 = x_435;
goto block_33;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_436 = lean_ctor_get(x_416, 1);
lean_inc(x_436);
lean_dec(x_416);
lean_inc(x_324);
x_437 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_324, x_313, x_436);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_440 = x_437;
} else {
 lean_dec_ref(x_437);
 x_440 = lean_box(0);
}
x_441 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
if (lean_is_scalar(x_440)) {
 x_442 = lean_alloc_ctor(7, 2, 0);
} else {
 x_442 = x_440;
 lean_ctor_set_tag(x_442, 7);
}
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_438);
x_443 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_441);
x_444 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_415, x_443, x_317, x_318, x_319, x_320, x_439);
x_445 = lean_ctor_get(x_444, 1);
lean_inc(x_445);
lean_dec(x_444);
x_15 = x_324;
x_16 = x_313;
x_17 = x_314;
x_18 = x_315;
x_19 = x_316;
x_20 = x_317;
x_21 = x_318;
x_22 = x_319;
x_23 = x_320;
x_24 = x_445;
goto block_33;
}
}
}
}
else
{
uint8_t x_446; 
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
x_446 = !lean_is_exclusive(x_323);
if (x_446 == 0)
{
return x_323;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_323, 0);
x_448 = lean_ctor_get(x_323, 1);
lean_inc(x_448);
lean_inc(x_447);
lean_dec(x_323);
x_449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_449, 0, x_447);
lean_ctor_set(x_449, 1, x_448);
return x_449;
}
}
}
}
else
{
uint8_t x_482; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_482 = !lean_is_exclusive(x_309);
if (x_482 == 0)
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_ctor_get(x_309, 0);
lean_dec(x_483);
x_484 = lean_box(0);
lean_ctor_set(x_309, 0, x_484);
return x_309;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_485 = lean_ctor_get(x_309, 1);
lean_inc(x_485);
lean_dec(x_309);
x_486 = lean_box(0);
x_487 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_485);
return x_487;
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
block_57:
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(x_34, x_36, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = lean_box(0);
x_43 = lean_unbox(x_40);
lean_dec(x_40);
x_44 = lean_unbox(x_42);
x_45 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_36);
lean_dec(x_35);
x_46 = lean_box(0);
lean_ctor_set(x_38, 0, x_46);
return x_38;
}
else
{
lean_object* x_47; 
lean_free_object(x_38);
x_47 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_35, x_36, x_41);
lean_dec(x_36);
lean_dec(x_35);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_38, 0);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_38);
x_50 = lean_box(0);
x_51 = lean_unbox(x_48);
lean_dec(x_48);
x_52 = lean_unbox(x_50);
x_53 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_36);
lean_dec(x_35);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
else
{
lean_object* x_56; 
x_56 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_35, x_36, x_49);
lean_dec(x_36);
lean_dec(x_35);
return x_56;
}
}
}
block_308:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_58, 0);
lean_inc(x_67);
x_68 = l_Int_Linear_Poly_updateOccs___redArg(x_67, x_61, x_62, x_63, x_64, x_65, x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__8;
x_71 = lean_int_dec_lt(x_59, x_70);
lean_dec(x_59);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_72 = lean_st_ref_take(x_61, x_69);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 14);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = !lean_is_exclusive(x_73);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_73, 14);
lean_dec(x_78);
x_79 = !lean_is_exclusive(x_74);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_74, 1);
lean_dec(x_80);
x_81 = !lean_is_exclusive(x_75);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_75, 7);
x_83 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_58);
x_84 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_58, x_83, x_82, x_60);
lean_ctor_set(x_75, 7, x_84);
x_85 = lean_st_ref_set(x_61, x_73, x_76);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_34 = x_58;
x_35 = x_60;
x_36 = x_61;
x_37 = x_86;
goto block_57;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_87 = lean_ctor_get(x_75, 0);
x_88 = lean_ctor_get(x_75, 1);
x_89 = lean_ctor_get(x_75, 2);
x_90 = lean_ctor_get(x_75, 3);
x_91 = lean_ctor_get(x_75, 4);
x_92 = lean_ctor_get(x_75, 5);
x_93 = lean_ctor_get(x_75, 6);
x_94 = lean_ctor_get(x_75, 7);
x_95 = lean_ctor_get(x_75, 8);
x_96 = lean_ctor_get(x_75, 9);
x_97 = lean_ctor_get(x_75, 10);
x_98 = lean_ctor_get(x_75, 11);
x_99 = lean_ctor_get(x_75, 12);
x_100 = lean_ctor_get(x_75, 13);
x_101 = lean_ctor_get_uint8(x_75, sizeof(void*)*19);
x_102 = lean_ctor_get(x_75, 14);
x_103 = lean_ctor_get(x_75, 15);
x_104 = lean_ctor_get(x_75, 16);
x_105 = lean_ctor_get(x_75, 17);
x_106 = lean_ctor_get(x_75, 18);
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
lean_dec(x_75);
x_107 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_58);
x_108 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_58, x_107, x_94, x_60);
x_109 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_109, 0, x_87);
lean_ctor_set(x_109, 1, x_88);
lean_ctor_set(x_109, 2, x_89);
lean_ctor_set(x_109, 3, x_90);
lean_ctor_set(x_109, 4, x_91);
lean_ctor_set(x_109, 5, x_92);
lean_ctor_set(x_109, 6, x_93);
lean_ctor_set(x_109, 7, x_108);
lean_ctor_set(x_109, 8, x_95);
lean_ctor_set(x_109, 9, x_96);
lean_ctor_set(x_109, 10, x_97);
lean_ctor_set(x_109, 11, x_98);
lean_ctor_set(x_109, 12, x_99);
lean_ctor_set(x_109, 13, x_100);
lean_ctor_set(x_109, 14, x_102);
lean_ctor_set(x_109, 15, x_103);
lean_ctor_set(x_109, 16, x_104);
lean_ctor_set(x_109, 17, x_105);
lean_ctor_set(x_109, 18, x_106);
lean_ctor_set_uint8(x_109, sizeof(void*)*19, x_101);
lean_ctor_set(x_74, 1, x_109);
x_110 = lean_st_ref_set(x_61, x_73, x_76);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_34 = x_58;
x_35 = x_60;
x_36 = x_61;
x_37 = x_111;
goto block_57;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_112 = lean_ctor_get(x_74, 0);
x_113 = lean_ctor_get(x_74, 2);
x_114 = lean_ctor_get(x_74, 3);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_74);
x_115 = lean_ctor_get(x_75, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_75, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_75, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_75, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_75, 4);
lean_inc(x_119);
x_120 = lean_ctor_get(x_75, 5);
lean_inc(x_120);
x_121 = lean_ctor_get(x_75, 6);
lean_inc(x_121);
x_122 = lean_ctor_get(x_75, 7);
lean_inc(x_122);
x_123 = lean_ctor_get(x_75, 8);
lean_inc(x_123);
x_124 = lean_ctor_get(x_75, 9);
lean_inc(x_124);
x_125 = lean_ctor_get(x_75, 10);
lean_inc(x_125);
x_126 = lean_ctor_get(x_75, 11);
lean_inc(x_126);
x_127 = lean_ctor_get(x_75, 12);
lean_inc(x_127);
x_128 = lean_ctor_get(x_75, 13);
lean_inc(x_128);
x_129 = lean_ctor_get_uint8(x_75, sizeof(void*)*19);
x_130 = lean_ctor_get(x_75, 14);
lean_inc(x_130);
x_131 = lean_ctor_get(x_75, 15);
lean_inc(x_131);
x_132 = lean_ctor_get(x_75, 16);
lean_inc(x_132);
x_133 = lean_ctor_get(x_75, 17);
lean_inc(x_133);
x_134 = lean_ctor_get(x_75, 18);
lean_inc(x_134);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 lean_ctor_release(x_75, 6);
 lean_ctor_release(x_75, 7);
 lean_ctor_release(x_75, 8);
 lean_ctor_release(x_75, 9);
 lean_ctor_release(x_75, 10);
 lean_ctor_release(x_75, 11);
 lean_ctor_release(x_75, 12);
 lean_ctor_release(x_75, 13);
 lean_ctor_release(x_75, 14);
 lean_ctor_release(x_75, 15);
 lean_ctor_release(x_75, 16);
 lean_ctor_release(x_75, 17);
 lean_ctor_release(x_75, 18);
 x_135 = x_75;
} else {
 lean_dec_ref(x_75);
 x_135 = lean_box(0);
}
x_136 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_58);
x_137 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_58, x_136, x_122, x_60);
if (lean_is_scalar(x_135)) {
 x_138 = lean_alloc_ctor(0, 19, 1);
} else {
 x_138 = x_135;
}
lean_ctor_set(x_138, 0, x_115);
lean_ctor_set(x_138, 1, x_116);
lean_ctor_set(x_138, 2, x_117);
lean_ctor_set(x_138, 3, x_118);
lean_ctor_set(x_138, 4, x_119);
lean_ctor_set(x_138, 5, x_120);
lean_ctor_set(x_138, 6, x_121);
lean_ctor_set(x_138, 7, x_137);
lean_ctor_set(x_138, 8, x_123);
lean_ctor_set(x_138, 9, x_124);
lean_ctor_set(x_138, 10, x_125);
lean_ctor_set(x_138, 11, x_126);
lean_ctor_set(x_138, 12, x_127);
lean_ctor_set(x_138, 13, x_128);
lean_ctor_set(x_138, 14, x_130);
lean_ctor_set(x_138, 15, x_131);
lean_ctor_set(x_138, 16, x_132);
lean_ctor_set(x_138, 17, x_133);
lean_ctor_set(x_138, 18, x_134);
lean_ctor_set_uint8(x_138, sizeof(void*)*19, x_129);
x_139 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_139, 0, x_112);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_139, 2, x_113);
lean_ctor_set(x_139, 3, x_114);
lean_ctor_set(x_73, 14, x_139);
x_140 = lean_st_ref_set(x_61, x_73, x_76);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_34 = x_58;
x_35 = x_60;
x_36 = x_61;
x_37 = x_141;
goto block_57;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_142 = lean_ctor_get(x_73, 0);
x_143 = lean_ctor_get(x_73, 1);
x_144 = lean_ctor_get(x_73, 2);
x_145 = lean_ctor_get(x_73, 3);
x_146 = lean_ctor_get(x_73, 4);
x_147 = lean_ctor_get(x_73, 5);
x_148 = lean_ctor_get(x_73, 6);
x_149 = lean_ctor_get(x_73, 7);
x_150 = lean_ctor_get_uint8(x_73, sizeof(void*)*16);
x_151 = lean_ctor_get(x_73, 8);
x_152 = lean_ctor_get(x_73, 9);
x_153 = lean_ctor_get(x_73, 10);
x_154 = lean_ctor_get(x_73, 11);
x_155 = lean_ctor_get(x_73, 12);
x_156 = lean_ctor_get(x_73, 13);
x_157 = lean_ctor_get(x_73, 15);
lean_inc(x_157);
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
lean_dec(x_73);
x_158 = lean_ctor_get(x_74, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_74, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_74, 3);
lean_inc(x_160);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_161 = x_74;
} else {
 lean_dec_ref(x_74);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_75, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_75, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_75, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_75, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_75, 4);
lean_inc(x_166);
x_167 = lean_ctor_get(x_75, 5);
lean_inc(x_167);
x_168 = lean_ctor_get(x_75, 6);
lean_inc(x_168);
x_169 = lean_ctor_get(x_75, 7);
lean_inc(x_169);
x_170 = lean_ctor_get(x_75, 8);
lean_inc(x_170);
x_171 = lean_ctor_get(x_75, 9);
lean_inc(x_171);
x_172 = lean_ctor_get(x_75, 10);
lean_inc(x_172);
x_173 = lean_ctor_get(x_75, 11);
lean_inc(x_173);
x_174 = lean_ctor_get(x_75, 12);
lean_inc(x_174);
x_175 = lean_ctor_get(x_75, 13);
lean_inc(x_175);
x_176 = lean_ctor_get_uint8(x_75, sizeof(void*)*19);
x_177 = lean_ctor_get(x_75, 14);
lean_inc(x_177);
x_178 = lean_ctor_get(x_75, 15);
lean_inc(x_178);
x_179 = lean_ctor_get(x_75, 16);
lean_inc(x_179);
x_180 = lean_ctor_get(x_75, 17);
lean_inc(x_180);
x_181 = lean_ctor_get(x_75, 18);
lean_inc(x_181);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 lean_ctor_release(x_75, 6);
 lean_ctor_release(x_75, 7);
 lean_ctor_release(x_75, 8);
 lean_ctor_release(x_75, 9);
 lean_ctor_release(x_75, 10);
 lean_ctor_release(x_75, 11);
 lean_ctor_release(x_75, 12);
 lean_ctor_release(x_75, 13);
 lean_ctor_release(x_75, 14);
 lean_ctor_release(x_75, 15);
 lean_ctor_release(x_75, 16);
 lean_ctor_release(x_75, 17);
 lean_ctor_release(x_75, 18);
 x_182 = x_75;
} else {
 lean_dec_ref(x_75);
 x_182 = lean_box(0);
}
x_183 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_58);
x_184 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_58, x_183, x_169, x_60);
if (lean_is_scalar(x_182)) {
 x_185 = lean_alloc_ctor(0, 19, 1);
} else {
 x_185 = x_182;
}
lean_ctor_set(x_185, 0, x_162);
lean_ctor_set(x_185, 1, x_163);
lean_ctor_set(x_185, 2, x_164);
lean_ctor_set(x_185, 3, x_165);
lean_ctor_set(x_185, 4, x_166);
lean_ctor_set(x_185, 5, x_167);
lean_ctor_set(x_185, 6, x_168);
lean_ctor_set(x_185, 7, x_184);
lean_ctor_set(x_185, 8, x_170);
lean_ctor_set(x_185, 9, x_171);
lean_ctor_set(x_185, 10, x_172);
lean_ctor_set(x_185, 11, x_173);
lean_ctor_set(x_185, 12, x_174);
lean_ctor_set(x_185, 13, x_175);
lean_ctor_set(x_185, 14, x_177);
lean_ctor_set(x_185, 15, x_178);
lean_ctor_set(x_185, 16, x_179);
lean_ctor_set(x_185, 17, x_180);
lean_ctor_set(x_185, 18, x_181);
lean_ctor_set_uint8(x_185, sizeof(void*)*19, x_176);
if (lean_is_scalar(x_161)) {
 x_186 = lean_alloc_ctor(0, 4, 0);
} else {
 x_186 = x_161;
}
lean_ctor_set(x_186, 0, x_158);
lean_ctor_set(x_186, 1, x_185);
lean_ctor_set(x_186, 2, x_159);
lean_ctor_set(x_186, 3, x_160);
x_187 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_187, 0, x_142);
lean_ctor_set(x_187, 1, x_143);
lean_ctor_set(x_187, 2, x_144);
lean_ctor_set(x_187, 3, x_145);
lean_ctor_set(x_187, 4, x_146);
lean_ctor_set(x_187, 5, x_147);
lean_ctor_set(x_187, 6, x_148);
lean_ctor_set(x_187, 7, x_149);
lean_ctor_set(x_187, 8, x_151);
lean_ctor_set(x_187, 9, x_152);
lean_ctor_set(x_187, 10, x_153);
lean_ctor_set(x_187, 11, x_154);
lean_ctor_set(x_187, 12, x_155);
lean_ctor_set(x_187, 13, x_156);
lean_ctor_set(x_187, 14, x_186);
lean_ctor_set(x_187, 15, x_157);
lean_ctor_set_uint8(x_187, sizeof(void*)*16, x_150);
x_188 = lean_st_ref_set(x_61, x_187, x_76);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_34 = x_58;
x_35 = x_60;
x_36 = x_61;
x_37 = x_189;
goto block_57;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_190 = lean_st_ref_take(x_61, x_69);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_191, 14);
lean_inc(x_192);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_190, 1);
lean_inc(x_194);
lean_dec(x_190);
x_195 = !lean_is_exclusive(x_191);
if (x_195 == 0)
{
lean_object* x_196; uint8_t x_197; 
x_196 = lean_ctor_get(x_191, 14);
lean_dec(x_196);
x_197 = !lean_is_exclusive(x_192);
if (x_197 == 0)
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_192, 1);
lean_dec(x_198);
x_199 = !lean_is_exclusive(x_193);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_193, 6);
x_201 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_58);
x_202 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_58, x_201, x_200, x_60);
lean_ctor_set(x_193, 6, x_202);
x_203 = lean_st_ref_set(x_61, x_191, x_194);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_34 = x_58;
x_35 = x_60;
x_36 = x_61;
x_37 = x_204;
goto block_57;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_205 = lean_ctor_get(x_193, 0);
x_206 = lean_ctor_get(x_193, 1);
x_207 = lean_ctor_get(x_193, 2);
x_208 = lean_ctor_get(x_193, 3);
x_209 = lean_ctor_get(x_193, 4);
x_210 = lean_ctor_get(x_193, 5);
x_211 = lean_ctor_get(x_193, 6);
x_212 = lean_ctor_get(x_193, 7);
x_213 = lean_ctor_get(x_193, 8);
x_214 = lean_ctor_get(x_193, 9);
x_215 = lean_ctor_get(x_193, 10);
x_216 = lean_ctor_get(x_193, 11);
x_217 = lean_ctor_get(x_193, 12);
x_218 = lean_ctor_get(x_193, 13);
x_219 = lean_ctor_get_uint8(x_193, sizeof(void*)*19);
x_220 = lean_ctor_get(x_193, 14);
x_221 = lean_ctor_get(x_193, 15);
x_222 = lean_ctor_get(x_193, 16);
x_223 = lean_ctor_get(x_193, 17);
x_224 = lean_ctor_get(x_193, 18);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_218);
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
lean_inc(x_205);
lean_dec(x_193);
x_225 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_58);
x_226 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_58, x_225, x_211, x_60);
x_227 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_227, 0, x_205);
lean_ctor_set(x_227, 1, x_206);
lean_ctor_set(x_227, 2, x_207);
lean_ctor_set(x_227, 3, x_208);
lean_ctor_set(x_227, 4, x_209);
lean_ctor_set(x_227, 5, x_210);
lean_ctor_set(x_227, 6, x_226);
lean_ctor_set(x_227, 7, x_212);
lean_ctor_set(x_227, 8, x_213);
lean_ctor_set(x_227, 9, x_214);
lean_ctor_set(x_227, 10, x_215);
lean_ctor_set(x_227, 11, x_216);
lean_ctor_set(x_227, 12, x_217);
lean_ctor_set(x_227, 13, x_218);
lean_ctor_set(x_227, 14, x_220);
lean_ctor_set(x_227, 15, x_221);
lean_ctor_set(x_227, 16, x_222);
lean_ctor_set(x_227, 17, x_223);
lean_ctor_set(x_227, 18, x_224);
lean_ctor_set_uint8(x_227, sizeof(void*)*19, x_219);
lean_ctor_set(x_192, 1, x_227);
x_228 = lean_st_ref_set(x_61, x_191, x_194);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
x_34 = x_58;
x_35 = x_60;
x_36 = x_61;
x_37 = x_229;
goto block_57;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_230 = lean_ctor_get(x_192, 0);
x_231 = lean_ctor_get(x_192, 2);
x_232 = lean_ctor_get(x_192, 3);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_192);
x_233 = lean_ctor_get(x_193, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_193, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_193, 2);
lean_inc(x_235);
x_236 = lean_ctor_get(x_193, 3);
lean_inc(x_236);
x_237 = lean_ctor_get(x_193, 4);
lean_inc(x_237);
x_238 = lean_ctor_get(x_193, 5);
lean_inc(x_238);
x_239 = lean_ctor_get(x_193, 6);
lean_inc(x_239);
x_240 = lean_ctor_get(x_193, 7);
lean_inc(x_240);
x_241 = lean_ctor_get(x_193, 8);
lean_inc(x_241);
x_242 = lean_ctor_get(x_193, 9);
lean_inc(x_242);
x_243 = lean_ctor_get(x_193, 10);
lean_inc(x_243);
x_244 = lean_ctor_get(x_193, 11);
lean_inc(x_244);
x_245 = lean_ctor_get(x_193, 12);
lean_inc(x_245);
x_246 = lean_ctor_get(x_193, 13);
lean_inc(x_246);
x_247 = lean_ctor_get_uint8(x_193, sizeof(void*)*19);
x_248 = lean_ctor_get(x_193, 14);
lean_inc(x_248);
x_249 = lean_ctor_get(x_193, 15);
lean_inc(x_249);
x_250 = lean_ctor_get(x_193, 16);
lean_inc(x_250);
x_251 = lean_ctor_get(x_193, 17);
lean_inc(x_251);
x_252 = lean_ctor_get(x_193, 18);
lean_inc(x_252);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 lean_ctor_release(x_193, 4);
 lean_ctor_release(x_193, 5);
 lean_ctor_release(x_193, 6);
 lean_ctor_release(x_193, 7);
 lean_ctor_release(x_193, 8);
 lean_ctor_release(x_193, 9);
 lean_ctor_release(x_193, 10);
 lean_ctor_release(x_193, 11);
 lean_ctor_release(x_193, 12);
 lean_ctor_release(x_193, 13);
 lean_ctor_release(x_193, 14);
 lean_ctor_release(x_193, 15);
 lean_ctor_release(x_193, 16);
 lean_ctor_release(x_193, 17);
 lean_ctor_release(x_193, 18);
 x_253 = x_193;
} else {
 lean_dec_ref(x_193);
 x_253 = lean_box(0);
}
x_254 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_58);
x_255 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_58, x_254, x_239, x_60);
if (lean_is_scalar(x_253)) {
 x_256 = lean_alloc_ctor(0, 19, 1);
} else {
 x_256 = x_253;
}
lean_ctor_set(x_256, 0, x_233);
lean_ctor_set(x_256, 1, x_234);
lean_ctor_set(x_256, 2, x_235);
lean_ctor_set(x_256, 3, x_236);
lean_ctor_set(x_256, 4, x_237);
lean_ctor_set(x_256, 5, x_238);
lean_ctor_set(x_256, 6, x_255);
lean_ctor_set(x_256, 7, x_240);
lean_ctor_set(x_256, 8, x_241);
lean_ctor_set(x_256, 9, x_242);
lean_ctor_set(x_256, 10, x_243);
lean_ctor_set(x_256, 11, x_244);
lean_ctor_set(x_256, 12, x_245);
lean_ctor_set(x_256, 13, x_246);
lean_ctor_set(x_256, 14, x_248);
lean_ctor_set(x_256, 15, x_249);
lean_ctor_set(x_256, 16, x_250);
lean_ctor_set(x_256, 17, x_251);
lean_ctor_set(x_256, 18, x_252);
lean_ctor_set_uint8(x_256, sizeof(void*)*19, x_247);
x_257 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_257, 0, x_230);
lean_ctor_set(x_257, 1, x_256);
lean_ctor_set(x_257, 2, x_231);
lean_ctor_set(x_257, 3, x_232);
lean_ctor_set(x_191, 14, x_257);
x_258 = lean_st_ref_set(x_61, x_191, x_194);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
lean_dec(x_258);
x_34 = x_58;
x_35 = x_60;
x_36 = x_61;
x_37 = x_259;
goto block_57;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_260 = lean_ctor_get(x_191, 0);
x_261 = lean_ctor_get(x_191, 1);
x_262 = lean_ctor_get(x_191, 2);
x_263 = lean_ctor_get(x_191, 3);
x_264 = lean_ctor_get(x_191, 4);
x_265 = lean_ctor_get(x_191, 5);
x_266 = lean_ctor_get(x_191, 6);
x_267 = lean_ctor_get(x_191, 7);
x_268 = lean_ctor_get_uint8(x_191, sizeof(void*)*16);
x_269 = lean_ctor_get(x_191, 8);
x_270 = lean_ctor_get(x_191, 9);
x_271 = lean_ctor_get(x_191, 10);
x_272 = lean_ctor_get(x_191, 11);
x_273 = lean_ctor_get(x_191, 12);
x_274 = lean_ctor_get(x_191, 13);
x_275 = lean_ctor_get(x_191, 15);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_191);
x_276 = lean_ctor_get(x_192, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_192, 2);
lean_inc(x_277);
x_278 = lean_ctor_get(x_192, 3);
lean_inc(x_278);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 x_279 = x_192;
} else {
 lean_dec_ref(x_192);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get(x_193, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_193, 1);
lean_inc(x_281);
x_282 = lean_ctor_get(x_193, 2);
lean_inc(x_282);
x_283 = lean_ctor_get(x_193, 3);
lean_inc(x_283);
x_284 = lean_ctor_get(x_193, 4);
lean_inc(x_284);
x_285 = lean_ctor_get(x_193, 5);
lean_inc(x_285);
x_286 = lean_ctor_get(x_193, 6);
lean_inc(x_286);
x_287 = lean_ctor_get(x_193, 7);
lean_inc(x_287);
x_288 = lean_ctor_get(x_193, 8);
lean_inc(x_288);
x_289 = lean_ctor_get(x_193, 9);
lean_inc(x_289);
x_290 = lean_ctor_get(x_193, 10);
lean_inc(x_290);
x_291 = lean_ctor_get(x_193, 11);
lean_inc(x_291);
x_292 = lean_ctor_get(x_193, 12);
lean_inc(x_292);
x_293 = lean_ctor_get(x_193, 13);
lean_inc(x_293);
x_294 = lean_ctor_get_uint8(x_193, sizeof(void*)*19);
x_295 = lean_ctor_get(x_193, 14);
lean_inc(x_295);
x_296 = lean_ctor_get(x_193, 15);
lean_inc(x_296);
x_297 = lean_ctor_get(x_193, 16);
lean_inc(x_297);
x_298 = lean_ctor_get(x_193, 17);
lean_inc(x_298);
x_299 = lean_ctor_get(x_193, 18);
lean_inc(x_299);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 lean_ctor_release(x_193, 4);
 lean_ctor_release(x_193, 5);
 lean_ctor_release(x_193, 6);
 lean_ctor_release(x_193, 7);
 lean_ctor_release(x_193, 8);
 lean_ctor_release(x_193, 9);
 lean_ctor_release(x_193, 10);
 lean_ctor_release(x_193, 11);
 lean_ctor_release(x_193, 12);
 lean_ctor_release(x_193, 13);
 lean_ctor_release(x_193, 14);
 lean_ctor_release(x_193, 15);
 lean_ctor_release(x_193, 16);
 lean_ctor_release(x_193, 17);
 lean_ctor_release(x_193, 18);
 x_300 = x_193;
} else {
 lean_dec_ref(x_193);
 x_300 = lean_box(0);
}
x_301 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___closed__0;
lean_inc(x_58);
x_302 = l_Lean_PersistentArray_modify___at___Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(x_58, x_301, x_286, x_60);
if (lean_is_scalar(x_300)) {
 x_303 = lean_alloc_ctor(0, 19, 1);
} else {
 x_303 = x_300;
}
lean_ctor_set(x_303, 0, x_280);
lean_ctor_set(x_303, 1, x_281);
lean_ctor_set(x_303, 2, x_282);
lean_ctor_set(x_303, 3, x_283);
lean_ctor_set(x_303, 4, x_284);
lean_ctor_set(x_303, 5, x_285);
lean_ctor_set(x_303, 6, x_302);
lean_ctor_set(x_303, 7, x_287);
lean_ctor_set(x_303, 8, x_288);
lean_ctor_set(x_303, 9, x_289);
lean_ctor_set(x_303, 10, x_290);
lean_ctor_set(x_303, 11, x_291);
lean_ctor_set(x_303, 12, x_292);
lean_ctor_set(x_303, 13, x_293);
lean_ctor_set(x_303, 14, x_295);
lean_ctor_set(x_303, 15, x_296);
lean_ctor_set(x_303, 16, x_297);
lean_ctor_set(x_303, 17, x_298);
lean_ctor_set(x_303, 18, x_299);
lean_ctor_set_uint8(x_303, sizeof(void*)*19, x_294);
if (lean_is_scalar(x_279)) {
 x_304 = lean_alloc_ctor(0, 4, 0);
} else {
 x_304 = x_279;
}
lean_ctor_set(x_304, 0, x_276);
lean_ctor_set(x_304, 1, x_303);
lean_ctor_set(x_304, 2, x_277);
lean_ctor_set(x_304, 3, x_278);
x_305 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_305, 0, x_260);
lean_ctor_set(x_305, 1, x_261);
lean_ctor_set(x_305, 2, x_262);
lean_ctor_set(x_305, 3, x_263);
lean_ctor_set(x_305, 4, x_264);
lean_ctor_set(x_305, 5, x_265);
lean_ctor_set(x_305, 6, x_266);
lean_ctor_set(x_305, 7, x_267);
lean_ctor_set(x_305, 8, x_269);
lean_ctor_set(x_305, 9, x_270);
lean_ctor_set(x_305, 10, x_271);
lean_ctor_set(x_305, 11, x_272);
lean_ctor_set(x_305, 12, x_273);
lean_ctor_set(x_305, 13, x_274);
lean_ctor_set(x_305, 14, x_304);
lean_ctor_set(x_305, 15, x_275);
lean_ctor_set_uint8(x_305, sizeof(void*)*16, x_268);
x_306 = lean_st_ref_set(x_61, x_305, x_194);
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
lean_dec(x_306);
x_34 = x_58;
x_35 = x_60;
x_36 = x_61;
x_37 = x_307;
goto block_57;
}
}
}
else
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
return x_68;
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
x_28 = lean_grind_cutsat_assert_le(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
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
x_33 = lean_grind_cutsat_assert_le(x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
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
x_37 = lean_grind_cutsat_assert_le(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_89; 
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
x_89 = l_Int_Linear_Expr_norm(x_37);
lean_dec(x_37);
if (x_2 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_91 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0;
x_92 = l_Int_Linear_Poly_mul(x_89, x_91);
x_93 = l_Int_Linear_Poly_addConst(x_92, x_90);
x_94 = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_22);
lean_ctor_set(x_94, 2, x_23);
lean_ctor_set(x_94, 3, x_35);
lean_ctor_set(x_94, 4, x_42);
lean_ctor_set(x_30, 1, x_94);
lean_ctor_set(x_30, 0, x_93);
x_44 = x_30;
x_45 = x_3;
x_46 = x_4;
x_47 = x_5;
x_48 = x_6;
x_49 = x_7;
x_50 = x_8;
x_51 = x_9;
x_52 = x_10;
goto block_88;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_22);
lean_ctor_set(x_95, 2, x_23);
lean_ctor_set(x_95, 3, x_35);
lean_ctor_set(x_95, 4, x_42);
lean_ctor_set(x_30, 1, x_95);
lean_ctor_set(x_30, 0, x_89);
x_44 = x_30;
x_45 = x_3;
x_46 = x_4;
x_47 = x_5;
x_48 = x_6;
x_49 = x_7;
x_50 = x_8;
x_51 = x_9;
x_52 = x_10;
goto block_88;
}
block_88:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0;
x_54 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_53, x_51, x_43);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_grind_cutsat_assert_le(x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_57);
return x_58;
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_54, 1);
x_61 = lean_ctor_get(x_54, 0);
lean_dec(x_61);
lean_inc(x_44);
x_62 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_44, x_45, x_60);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
lean_ctor_set_tag(x_62, 7);
lean_ctor_set(x_62, 1, x_64);
lean_ctor_set(x_62, 0, x_66);
lean_ctor_set_tag(x_54, 7);
lean_ctor_set(x_54, 1, x_66);
lean_ctor_set(x_54, 0, x_62);
x_67 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_53, x_54, x_49, x_50, x_51, x_52, x_65);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_grind_cutsat_assert_le(x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_68);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_62, 0);
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_62);
x_72 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set_tag(x_54, 7);
lean_ctor_set(x_54, 1, x_72);
lean_ctor_set(x_54, 0, x_73);
x_74 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_53, x_54, x_49, x_50, x_51, x_52, x_71);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_grind_cutsat_assert_le(x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_77 = lean_ctor_get(x_54, 1);
lean_inc(x_77);
lean_dec(x_54);
lean_inc(x_44);
x_78 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_44, x_45, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(7, 2, 0);
} else {
 x_83 = x_81;
 lean_ctor_set_tag(x_83, 7);
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_53, x_84, x_49, x_50, x_51, x_52, x_80);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_grind_cutsat_assert_le(x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_86);
return x_87;
}
}
}
}
else
{
uint8_t x_96; 
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
x_96 = !lean_is_exclusive(x_41);
if (x_96 == 0)
{
return x_41;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_41, 0);
x_98 = lean_ctor_get(x_41, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_41);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_37, 0);
x_101 = lean_ctor_get(x_37, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_37);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_102 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_100, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_133; lean_object* x_134; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_103);
lean_inc(x_35);
x_133 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_133, 0, x_35);
lean_ctor_set(x_133, 1, x_103);
x_134 = l_Int_Linear_Expr_norm(x_133);
lean_dec(x_133);
if (x_2 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_136 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0;
x_137 = l_Int_Linear_Poly_mul(x_134, x_136);
x_138 = l_Int_Linear_Poly_addConst(x_137, x_135);
x_139 = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(x_139, 0, x_1);
lean_ctor_set(x_139, 1, x_22);
lean_ctor_set(x_139, 2, x_23);
lean_ctor_set(x_139, 3, x_35);
lean_ctor_set(x_139, 4, x_103);
lean_ctor_set(x_30, 1, x_139);
lean_ctor_set(x_30, 0, x_138);
x_105 = x_30;
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = x_9;
x_113 = x_10;
goto block_132;
}
else
{
lean_object* x_140; 
x_140 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_140, 0, x_1);
lean_ctor_set(x_140, 1, x_22);
lean_ctor_set(x_140, 2, x_23);
lean_ctor_set(x_140, 3, x_35);
lean_ctor_set(x_140, 4, x_103);
lean_ctor_set(x_30, 1, x_140);
lean_ctor_set(x_30, 0, x_134);
x_105 = x_30;
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = x_9;
x_113 = x_10;
goto block_132;
}
block_132:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0;
x_115 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_114, x_112, x_104);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_grind_cutsat_assert_le(x_105, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_118);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_121 = x_115;
} else {
 lean_dec_ref(x_115);
 x_121 = lean_box(0);
}
lean_inc(x_105);
x_122 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_105, x_106, x_120);
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
x_126 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(7, 2, 0);
} else {
 x_127 = x_125;
 lean_ctor_set_tag(x_127, 7);
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_123);
if (lean_is_scalar(x_121)) {
 x_128 = lean_alloc_ctor(7, 2, 0);
} else {
 x_128 = x_121;
 lean_ctor_set_tag(x_128, 7);
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_114, x_128, x_110, x_111, x_112, x_113, x_124);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_grind_cutsat_assert_le(x_105, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_130);
return x_131;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
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
x_141 = lean_ctor_get(x_102, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_102, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_143 = x_102;
} else {
 lean_dec_ref(x_102);
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
else
{
uint8_t x_145; 
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
x_145 = !lean_is_exclusive(x_34);
if (x_145 == 0)
{
return x_34;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_34, 0);
x_147 = lean_ctor_get(x_34, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_34);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_30, 0);
x_150 = lean_ctor_get(x_30, 1);
lean_inc(x_150);
lean_inc(x_149);
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
x_151 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_149, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_23);
x_154 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_28, x_23, x_6, x_153);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_158 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_155, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_156);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_189; lean_object* x_190; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_159);
lean_inc(x_152);
if (lean_is_scalar(x_157)) {
 x_189 = lean_alloc_ctor(3, 2, 0);
} else {
 x_189 = x_157;
 lean_ctor_set_tag(x_189, 3);
}
lean_ctor_set(x_189, 0, x_152);
lean_ctor_set(x_189, 1, x_159);
x_190 = l_Int_Linear_Expr_norm(x_189);
lean_dec(x_189);
if (x_2 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_191 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__7_spec__7___lam__0___closed__0;
x_192 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0;
x_193 = l_Int_Linear_Poly_mul(x_190, x_192);
x_194 = l_Int_Linear_Poly_addConst(x_193, x_191);
x_195 = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(x_195, 0, x_1);
lean_ctor_set(x_195, 1, x_22);
lean_ctor_set(x_195, 2, x_23);
lean_ctor_set(x_195, 3, x_152);
lean_ctor_set(x_195, 4, x_159);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_161 = x_196;
x_162 = x_3;
x_163 = x_4;
x_164 = x_5;
x_165 = x_6;
x_166 = x_7;
x_167 = x_8;
x_168 = x_9;
x_169 = x_10;
goto block_188;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_197, 0, x_1);
lean_ctor_set(x_197, 1, x_22);
lean_ctor_set(x_197, 2, x_23);
lean_ctor_set(x_197, 3, x_152);
lean_ctor_set(x_197, 4, x_159);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_190);
lean_ctor_set(x_198, 1, x_197);
x_161 = x_198;
x_162 = x_3;
x_163 = x_4;
x_164 = x_5;
x_165 = x_6;
x_166 = x_7;
x_167 = x_8;
x_168 = x_9;
x_169 = x_10;
goto block_188;
}
block_188:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_170 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0;
x_171 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_170, x_168, x_160);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_unbox(x_172);
lean_dec(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_grind_cutsat_assert_le(x_161, x_162, x_163, x_164, x_165, x_166, x_167, x_168, x_169, x_174);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_177 = x_171;
} else {
 lean_dec_ref(x_171);
 x_177 = lean_box(0);
}
lean_inc(x_161);
x_178 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_161, x_162, x_176);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
x_182 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(7, 2, 0);
} else {
 x_183 = x_181;
 lean_ctor_set_tag(x_183, 7);
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_179);
if (lean_is_scalar(x_177)) {
 x_184 = lean_alloc_ctor(7, 2, 0);
} else {
 x_184 = x_177;
 lean_ctor_set_tag(x_184, 7);
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_185 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_170, x_184, x_166, x_167, x_168, x_169, x_180);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = lean_grind_cutsat_assert_le(x_161, x_162, x_163, x_164, x_165, x_166, x_167, x_168, x_169, x_186);
return x_187;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_157);
lean_dec(x_152);
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
x_199 = lean_ctor_get(x_158, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_158, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_201 = x_158;
} else {
 lean_dec_ref(x_158);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
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
x_203 = lean_ctor_get(x_151, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_151, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_205 = x_151;
} else {
 lean_dec_ref(x_151);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_207 = !lean_is_exclusive(x_12);
if (x_207 == 0)
{
return x_12;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_12, 0);
x_209 = lean_ctor_get(x_12, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_12);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__0___redArg(x_1, x_9, x_11);
return x_12;
}
}
static double _init_l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc(x_14);
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
lean_object* x_21; double x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__0;
x_23 = lean_box(0);
x_24 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__4;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_26);
x_27 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__1;
x_28 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_27);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_28);
lean_ctor_set(x_12, 0, x_8);
x_29 = l_Lean_PersistentArray_push___redArg(x_21, x_12);
lean_ctor_set(x_14, 0, x_29);
x_30 = lean_st_ref_set(x_6, x_13, x_16);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint64_t x_37; lean_object* x_38; double x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_37 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_38 = lean_ctor_get(x_14, 0);
lean_inc(x_38);
lean_dec(x_14);
x_39 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__0;
x_40 = lean_box(0);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__4;
x_42 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_float(x_42, sizeof(void*)*2, x_39);
lean_ctor_set_float(x_42, sizeof(void*)*2 + 8, x_39);
x_43 = lean_unbox(x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 16, x_43);
x_44 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__1;
x_45 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_10);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_45);
lean_ctor_set(x_12, 0, x_8);
x_46 = l_Lean_PersistentArray_push___redArg(x_38, x_12);
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_37);
lean_ctor_set(x_13, 4, x_47);
x_48 = lean_st_ref_set(x_6, x_13, x_16);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = lean_box(0);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; double x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_53 = lean_ctor_get(x_13, 0);
x_54 = lean_ctor_get(x_13, 1);
x_55 = lean_ctor_get(x_13, 2);
x_56 = lean_ctor_get(x_13, 3);
x_57 = lean_ctor_get(x_13, 5);
x_58 = lean_ctor_get(x_13, 6);
x_59 = lean_ctor_get(x_13, 7);
x_60 = lean_ctor_get(x_13, 8);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_13);
x_61 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_62 = lean_ctor_get(x_14, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_63 = x_14;
} else {
 lean_dec_ref(x_14);
 x_63 = lean_box(0);
}
x_64 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__0;
x_65 = lean_box(0);
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__4;
x_67 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_float(x_67, sizeof(void*)*2, x_64);
lean_ctor_set_float(x_67, sizeof(void*)*2 + 8, x_64);
x_68 = lean_unbox(x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*2 + 16, x_68);
x_69 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__1;
x_70 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_10);
lean_ctor_set(x_70, 2, x_69);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_70);
lean_ctor_set(x_12, 0, x_8);
x_71 = l_Lean_PersistentArray_push___redArg(x_62, x_12);
if (lean_is_scalar(x_63)) {
 x_72 = lean_alloc_ctor(0, 1, 8);
} else {
 x_72 = x_63;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_61);
x_73 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_73, 0, x_53);
lean_ctor_set(x_73, 1, x_54);
lean_ctor_set(x_73, 2, x_55);
lean_ctor_set(x_73, 3, x_56);
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_73, 5, x_57);
lean_ctor_set(x_73, 6, x_58);
lean_ctor_set(x_73, 7, x_59);
lean_ctor_set(x_73, 8, x_60);
x_74 = lean_st_ref_set(x_6, x_73, x_16);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint64_t x_89; lean_object* x_90; lean_object* x_91; double x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_79 = lean_ctor_get(x_12, 1);
lean_inc(x_79);
lean_dec(x_12);
x_80 = lean_ctor_get(x_13, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_13, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_13, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_13, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_13, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_13, 6);
lean_inc(x_85);
x_86 = lean_ctor_get(x_13, 7);
lean_inc(x_86);
x_87 = lean_ctor_get(x_13, 8);
lean_inc(x_87);
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
 x_88 = x_13;
} else {
 lean_dec_ref(x_13);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_90 = lean_ctor_get(x_14, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_91 = x_14;
} else {
 lean_dec_ref(x_14);
 x_91 = lean_box(0);
}
x_92 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__0;
x_93 = lean_box(0);
x_94 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__4;
x_95 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set_float(x_95, sizeof(void*)*2, x_92);
lean_ctor_set_float(x_95, sizeof(void*)*2 + 8, x_92);
x_96 = lean_unbox(x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*2 + 16, x_96);
x_97 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__1;
x_98 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_10);
lean_ctor_set(x_98, 2, x_97);
lean_inc(x_8);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_8);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_PersistentArray_push___redArg(x_90, x_99);
if (lean_is_scalar(x_91)) {
 x_101 = lean_alloc_ctor(0, 1, 8);
} else {
 x_101 = x_91;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set_uint64(x_101, sizeof(void*)*1, x_89);
if (lean_is_scalar(x_88)) {
 x_102 = lean_alloc_ctor(0, 9, 0);
} else {
 x_102 = x_88;
}
lean_ctor_set(x_102, 0, x_80);
lean_ctor_set(x_102, 1, x_81);
lean_ctor_set(x_102, 2, x_82);
lean_ctor_set(x_102, 3, x_83);
lean_ctor_set(x_102, 4, x_101);
lean_ctor_set(x_102, 5, x_84);
lean_ctor_set(x_102, 6, x_85);
lean_ctor_set(x_102, 7, x_86);
lean_ctor_set(x_102, 8, x_87);
x_103 = lean_st_ref_set(x_6, x_102, x_79);
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
x_106 = lean_box(0);
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
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
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
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
if (x_2 == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_3, 11);
lean_inc(x_148);
x_95 = x_148;
x_96 = x_3;
x_97 = x_4;
x_98 = x_5;
x_99 = x_6;
x_100 = x_7;
x_101 = x_8;
x_102 = x_9;
x_103 = x_10;
x_104 = x_11;
x_105 = x_12;
goto block_147;
}
else
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_3, 10);
lean_inc(x_149);
x_95 = x_149;
x_96 = x_3;
x_97 = x_4;
x_98 = x_5;
x_99 = x_6;
x_100 = x_7;
x_101 = x_8;
x_102 = x_9;
x_103 = x_10;
x_104 = x_11;
x_105 = x_12;
goto block_147;
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
block_94:
{
lean_object* x_32; 
lean_dec(x_20);
lean_inc(x_23);
lean_inc(x_26);
lean_inc(x_22);
lean_inc(x_17);
lean_inc(x_24);
lean_inc(x_27);
lean_inc(x_19);
lean_inc(x_28);
lean_inc(x_25);
x_32 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_30, x_25, x_28, x_19, x_27, x_24, x_17, x_22, x_26, x_23, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_23);
lean_inc(x_26);
lean_inc(x_22);
lean_inc(x_17);
lean_inc(x_24);
lean_inc(x_27);
lean_inc(x_19);
lean_inc(x_28);
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_31, x_25, x_28, x_19, x_27, x_24, x_17, x_22, x_26, x_23, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__0;
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__1;
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0;
x_41 = l_Lean_Name_mkStr4(x_38, x_39, x_40, x_21);
lean_inc(x_41);
x_42 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__0___redArg(x_41, x_26, x_37);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_36);
lean_inc(x_33);
lean_ctor_set_tag(x_42, 3);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 0, x_33);
x_46 = l_Int_Linear_Expr_norm(x_42);
lean_dec(x_42);
x_47 = lean_alloc_ctor(4, 4, 1);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_18);
lean_ctor_set(x_47, 2, x_33);
lean_ctor_set(x_47, 3, x_36);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_2);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_unbox(x_44);
lean_dec(x_44);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_41);
x_50 = lean_grind_cutsat_assert_le(x_48, x_28, x_19, x_27, x_24, x_17, x_22, x_26, x_23, x_45);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_inc(x_48);
x_51 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_48, x_28, x_45);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
x_55 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
lean_ctor_set_tag(x_51, 7);
lean_ctor_set(x_51, 1, x_53);
lean_ctor_set(x_51, 0, x_55);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg(x_41, x_56, x_17, x_22, x_26, x_23, x_54);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_grind_cutsat_assert_le(x_48, x_28, x_19, x_27, x_24, x_17, x_22, x_26, x_23, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_51, 0);
x_61 = lean_ctor_get(x_51, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_51);
x_62 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg(x_41, x_64, x_17, x_22, x_26, x_23, x_61);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_grind_cutsat_assert_le(x_48, x_28, x_19, x_27, x_24, x_17, x_22, x_26, x_23, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_68 = lean_ctor_get(x_42, 0);
x_69 = lean_ctor_get(x_42, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_42);
lean_inc(x_36);
lean_inc(x_33);
x_70 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_70, 0, x_33);
lean_ctor_set(x_70, 1, x_36);
x_71 = l_Int_Linear_Expr_norm(x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(4, 4, 1);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_18);
lean_ctor_set(x_72, 2, x_33);
lean_ctor_set(x_72, 3, x_36);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_2);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_unbox(x_68);
lean_dec(x_68);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_41);
x_75 = lean_grind_cutsat_assert_le(x_73, x_28, x_19, x_27, x_24, x_17, x_22, x_26, x_23, x_69);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_inc(x_73);
x_76 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(x_73, x_28, x_69);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___redArg___closed__5;
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(7, 2, 0);
} else {
 x_81 = x_79;
 lean_ctor_set_tag(x_81, 7);
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg(x_41, x_82, x_17, x_22, x_26, x_23, x_78);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_grind_cutsat_assert_le(x_73, x_28, x_19, x_27, x_24, x_17, x_22, x_26, x_23, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_35);
if (x_86 == 0)
{
return x_35;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_35, 0);
x_88 = lean_ctor_get(x_35, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_35);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_32);
if (x_90 == 0)
{
return x_32;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_32, 0);
x_92 = lean_ctor_get(x_32, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_32);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
block_147:
{
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_1);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_95, 0);
lean_inc(x_108);
lean_dec(x_95);
lean_inc(x_1);
x_109 = l_Lean_Expr_cleanupAnnotations(x_1);
x_110 = l_Lean_Expr_isApp(x_109);
if (x_110 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_1);
x_13 = x_105;
goto block_16;
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
x_112 = l_Lean_Expr_appFnCleanup___redArg(x_109);
x_113 = l_Lean_Expr_isApp(x_112);
if (x_113 == 0)
{
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_1);
x_13 = x_105;
goto block_16;
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
x_115 = l_Lean_Expr_appFnCleanup___redArg(x_112);
x_116 = l_Lean_Expr_isApp(x_115);
if (x_116 == 0)
{
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_111);
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_1);
x_13 = x_105;
goto block_16;
}
else
{
lean_object* x_117; uint8_t x_118; 
x_117 = l_Lean_Expr_appFnCleanup___redArg(x_115);
x_118 = l_Lean_Expr_isApp(x_117);
if (x_118 == 0)
{
lean_dec(x_117);
lean_dec(x_114);
lean_dec(x_111);
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_1);
x_13 = x_105;
goto block_16;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = l_Lean_Expr_appFnCleanup___redArg(x_117);
x_120 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1;
x_121 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2;
x_122 = l_Lean_Expr_isConstOf(x_119, x_121);
lean_dec(x_119);
if (x_122 == 0)
{
lean_dec(x_114);
lean_dec(x_111);
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_1);
x_13 = x_105;
goto block_16;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_inc(x_1);
x_123 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_97, x_105);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_114);
x_126 = l_Lean_Meta_Grind_Arith_Cutsat_toInt(x_114, x_96, x_97, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_111);
x_131 = l_Lean_Meta_Grind_Arith_Cutsat_toInt(x_111, x_96, x_97, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_128);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
lean_inc(x_134);
lean_inc(x_129);
x_136 = l_Lean_mkApp6(x_108, x_114, x_111, x_129, x_134, x_130, x_135);
if (x_2 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___closed__0;
x_138 = l_Lean_mkIntAdd(x_134, x_137);
x_17 = x_101;
x_18 = x_136;
x_19 = x_98;
x_20 = x_96;
x_21 = x_120;
x_22 = x_102;
x_23 = x_104;
x_24 = x_100;
x_25 = x_124;
x_26 = x_103;
x_27 = x_99;
x_28 = x_97;
x_29 = x_133;
x_30 = x_138;
x_31 = x_129;
goto block_94;
}
else
{
x_17 = x_101;
x_18 = x_136;
x_19 = x_98;
x_20 = x_96;
x_21 = x_120;
x_22 = x_102;
x_23 = x_104;
x_24 = x_100;
x_25 = x_124;
x_26 = x_103;
x_27 = x_99;
x_28 = x_97;
x_29 = x_133;
x_30 = x_129;
x_31 = x_134;
goto block_94;
}
}
else
{
uint8_t x_139; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_124);
lean_dec(x_114);
lean_dec(x_111);
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_131);
if (x_139 == 0)
{
return x_131;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_131, 0);
x_141 = lean_ctor_get(x_131, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_131);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_124);
lean_dec(x_114);
lean_dec(x_111);
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_126);
if (x_143 == 0)
{
return x_126;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_126, 0);
x_145 = lean_ctor_get(x_126, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_126);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin, lean_object*);
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
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__0 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__0();
l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__1 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe_spec__1___redArg___closed__1);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

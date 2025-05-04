// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
// Imports: Lean.Meta.Tactic.Simp.Arith.Int Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
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
lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__6;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__5;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__1;
lean_object* l_Lean_PersistentArray_set___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2579_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getForeignVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__4;
lean_object* lean_nat_to_int(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__2;
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(uint8_t, uint8_t);
lean_object* l_Int_OfNat_toIntDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
lean_object* l_Int_Linear_Expr_norm(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__1;
lean_object* l_Int_Linear_Poly_findVarToSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__1;
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__3;
lean_object* l_Int_Linear_Poly_norm(lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___closed__2;
lean_object* l_Int_OfNat_Expr_denoteAsIntExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2579____closed__1;
uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_reflBoolTrue;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
lean_object* l_Lean_PersistentArray_get_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_combine_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__2;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__6;
lean_object* l_Lean_Meta_Grind_isEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstDvdInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__4;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__3;
lean_object* l_Lean_Meta_Grind_getConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = l_Int_Linear_Poly_isSorted(x_3);
if (x_4 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Int_Linear_Poly_norm(x_3);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_1);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
x_5 = x_32;
goto block_29;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
x_5 = x_1;
goto block_29;
}
block_29:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_inc(x_7);
x_8 = l_Int_Linear_Poly_gcdCoeffs(x_6, x_7);
x_9 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1;
x_10 = lean_int_dec_lt(x_7, x_9);
x_11 = l_Int_Linear_Poly_getConst(x_6);
if (x_10 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_int_emod(x_11, x_8);
lean_dec(x_11);
x_13 = lean_int_dec_eq(x_12, x_9);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_5;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__2;
x_15 = lean_int_dec_eq(x_8, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_int_ediv(x_7, x_8);
lean_dec(x_7);
x_17 = l_Int_Linear_Poly_div(x_8, x_6);
lean_dec(x_8);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_5);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_5;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_int_neg(x_8);
lean_dec(x_8);
x_21 = lean_int_emod(x_11, x_20);
lean_dec(x_11);
x_22 = lean_int_dec_eq(x_21, x_9);
lean_dec(x_21);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
return x_5;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__2;
x_24 = lean_int_dec_eq(x_20, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_int_ediv(x_7, x_20);
lean_dec(x_7);
x_26 = l_Int_Linear_Poly_div(x_20, x_6);
lean_dec(x_20);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_5);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
return x_28;
}
else
{
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
return x_5;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_3);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cutsat", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_int_mul(x_1, x_17);
lean_dec(x_17);
x_19 = lean_nat_abs(x_18);
lean_dec(x_18);
x_20 = lean_nat_to_int(x_19);
x_21 = l_Int_Linear_Poly_mul(x_16, x_1);
x_22 = lean_int_neg(x_4);
x_23 = l_Int_Linear_Poly_mul(x_15, x_22);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(100000000u);
x_25 = l_Int_Linear_Poly_combine_x27(x_24, x_21, x_23);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_27 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
x_32 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___lambda__1(x_2, x_3, x_5, x_20, x_25, x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_30);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_27, 1);
x_35 = lean_ctor_get(x_27, 0);
lean_dec(x_35);
x_36 = l_Lean_Meta_Grind_Arith_Cutsat_getVar(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_34);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_3);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_39);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_5);
x_44 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_43);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
x_48 = l_Lean_MessageData_ofExpr(x_38);
x_49 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
lean_ctor_set_tag(x_44, 7);
lean_ctor_set(x_44, 1, x_48);
lean_ctor_set(x_44, 0, x_49);
x_50 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9;
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_50);
lean_ctor_set(x_40, 0, x_44);
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_42);
lean_ctor_set(x_36, 0, x_40);
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_50);
lean_ctor_set(x_27, 0, x_36);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_27);
lean_ctor_set(x_51, 1, x_46);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
x_53 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_26, x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_47);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___lambda__1(x_2, x_3, x_5, x_20, x_25, x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_55);
lean_dec(x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_57 = lean_ctor_get(x_44, 0);
x_58 = lean_ctor_get(x_44, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_44);
x_59 = l_Lean_MessageData_ofExpr(x_38);
x_60 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9;
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_62);
lean_ctor_set(x_40, 0, x_61);
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_42);
lean_ctor_set(x_36, 0, x_40);
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_62);
lean_ctor_set(x_27, 0, x_36);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_27);
lean_ctor_set(x_63, 1, x_57);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
x_65 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_26, x_64, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_58);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___lambda__1(x_2, x_3, x_5, x_20, x_25, x_66, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_67);
lean_dec(x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_69 = lean_ctor_get(x_40, 0);
x_70 = lean_ctor_get(x_40, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_40);
lean_inc(x_5);
x_71 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_70);
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
x_75 = l_Lean_MessageData_ofExpr(x_38);
x_76 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(7, 2, 0);
} else {
 x_77 = x_74;
 lean_ctor_set_tag(x_77, 7);
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_69);
lean_ctor_set(x_36, 0, x_79);
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_78);
lean_ctor_set(x_27, 0, x_36);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_27);
lean_ctor_set(x_80, 1, x_72);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
x_82 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_26, x_81, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_73);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___lambda__1(x_2, x_3, x_5, x_20, x_25, x_83, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_84);
lean_dec(x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_86 = lean_ctor_get(x_36, 0);
x_87 = lean_ctor_get(x_36, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_36);
lean_inc(x_3);
x_88 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_87);
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
lean_inc(x_5);
x_92 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_90);
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
x_96 = l_Lean_MessageData_ofExpr(x_86);
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(7, 2, 0);
} else {
 x_98 = x_95;
 lean_ctor_set_tag(x_98, 7);
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9;
if (lean_is_scalar(x_91)) {
 x_100 = lean_alloc_ctor(7, 2, 0);
} else {
 x_100 = x_91;
 lean_ctor_set_tag(x_100, 7);
}
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_89);
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_99);
lean_ctor_set(x_27, 0, x_101);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_27);
lean_ctor_set(x_102, 1, x_93);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_97);
x_104 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_26, x_103, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_94);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___lambda__1(x_2, x_3, x_5, x_20, x_25, x_105, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_106);
lean_dec(x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_108 = lean_ctor_get(x_27, 1);
lean_inc(x_108);
lean_dec(x_27);
x_109 = l_Lean_Meta_Grind_Arith_Cutsat_getVar(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
lean_inc(x_3);
x_113 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_111);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
lean_inc(x_5);
x_117 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_115);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
x_121 = l_Lean_MessageData_ofExpr(x_110);
x_122 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
if (lean_is_scalar(x_120)) {
 x_123 = lean_alloc_ctor(7, 2, 0);
} else {
 x_123 = x_120;
 lean_ctor_set_tag(x_123, 7);
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9;
if (lean_is_scalar(x_116)) {
 x_125 = lean_alloc_ctor(7, 2, 0);
} else {
 x_125 = x_116;
 lean_ctor_set_tag(x_125, 7);
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
if (lean_is_scalar(x_112)) {
 x_126 = lean_alloc_ctor(7, 2, 0);
} else {
 x_126 = x_112;
 lean_ctor_set_tag(x_126, 7);
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_114);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_118);
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_122);
x_130 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_26, x_129, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_119);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___lambda__1(x_2, x_3, x_5, x_20, x_25, x_131, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_132);
lean_dec(x_131);
return x_133;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__3;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__5;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__6;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 6);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 7);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 8);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 9);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 10);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_24 = lean_ctor_get(x_8, 11);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_26 = lean_ctor_get(x_8, 12);
lean_inc(x_26);
x_27 = lean_nat_dec_eq(x_15, x_16);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_8);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_ctor_get(x_8, 12);
lean_dec(x_29);
x_30 = lean_ctor_get(x_8, 11);
lean_dec(x_30);
x_31 = lean_ctor_get(x_8, 10);
lean_dec(x_31);
x_32 = lean_ctor_get(x_8, 9);
lean_dec(x_32);
x_33 = lean_ctor_get(x_8, 8);
lean_dec(x_33);
x_34 = lean_ctor_get(x_8, 7);
lean_dec(x_34);
x_35 = lean_ctor_get(x_8, 6);
lean_dec(x_35);
x_36 = lean_ctor_get(x_8, 5);
lean_dec(x_36);
x_37 = lean_ctor_get(x_8, 4);
lean_dec(x_37);
x_38 = lean_ctor_get(x_8, 3);
lean_dec(x_38);
x_39 = lean_ctor_get(x_8, 2);
lean_dec(x_39);
x_40 = lean_ctor_get(x_8, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_8, 0);
lean_dec(x_41);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_15, x_42);
lean_dec(x_15);
lean_ctor_set(x_8, 3, x_43);
x_44 = l_Int_Linear_Poly_findVarToSubst(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_8);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
lean_ctor_set(x_44, 0, x_1);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = l_Int_Linear_Poly_coeff(x_56, x_54);
lean_dec(x_56);
x_58 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_57, x_54, x_55, x_53, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
lean_dec(x_53);
lean_dec(x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_1 = x_59;
x_10 = x_60;
goto _start;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_8);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_15, x_62);
lean_dec(x_15);
x_64 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_64, 0, x_12);
lean_ctor_set(x_64, 1, x_13);
lean_ctor_set(x_64, 2, x_14);
lean_ctor_set(x_64, 3, x_63);
lean_ctor_set(x_64, 4, x_16);
lean_ctor_set(x_64, 5, x_17);
lean_ctor_set(x_64, 6, x_18);
lean_ctor_set(x_64, 7, x_19);
lean_ctor_set(x_64, 8, x_20);
lean_ctor_set(x_64, 9, x_21);
lean_ctor_set(x_64, 10, x_22);
lean_ctor_set(x_64, 11, x_24);
lean_ctor_set(x_64, 12, x_26);
lean_ctor_set_uint8(x_64, sizeof(void*)*13, x_23);
lean_ctor_set_uint8(x_64, sizeof(void*)*13 + 1, x_25);
x_65 = l_Int_Linear_Poly_findVarToSubst(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_64, x_9, x_10);
lean_dec(x_11);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
lean_dec(x_65);
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = l_Int_Linear_Poly_coeff(x_76, x_74);
lean_dec(x_76);
x_78 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_77, x_74, x_75, x_73, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_64, x_9, x_72);
lean_dec(x_73);
lean_dec(x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_1 = x_79;
x_8 = x_64;
x_10 = x_80;
goto _start;
}
}
}
else
{
lean_object* x_82; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_82 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Int_Linear_Poly_updateOccs(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_take(x_5, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 14);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
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
x_24 = lean_ctor_get(x_18, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_19, 5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = l_Lean_PersistentArray_set___rarg(x_26, x_3, x_27);
lean_ctor_set(x_19, 5, x_28);
x_29 = lean_st_ref_set(x_5, x_17, x_20);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
x_38 = lean_ctor_get(x_19, 2);
x_39 = lean_ctor_get(x_19, 3);
x_40 = lean_ctor_get(x_19, 4);
x_41 = lean_ctor_get(x_19, 5);
x_42 = lean_ctor_get(x_19, 6);
x_43 = lean_ctor_get(x_19, 7);
x_44 = lean_ctor_get(x_19, 8);
x_45 = lean_ctor_get(x_19, 9);
x_46 = lean_ctor_get(x_19, 10);
x_47 = lean_ctor_get(x_19, 11);
x_48 = lean_ctor_get(x_19, 12);
x_49 = lean_ctor_get(x_19, 13);
x_50 = lean_ctor_get_uint8(x_19, sizeof(void*)*17);
x_51 = lean_ctor_get(x_19, 14);
x_52 = lean_ctor_get(x_19, 15);
x_53 = lean_ctor_get(x_19, 16);
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
lean_dec(x_19);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_2);
x_55 = l_Lean_PersistentArray_set___rarg(x_41, x_3, x_54);
x_56 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_56, 0, x_36);
lean_ctor_set(x_56, 1, x_37);
lean_ctor_set(x_56, 2, x_38);
lean_ctor_set(x_56, 3, x_39);
lean_ctor_set(x_56, 4, x_40);
lean_ctor_set(x_56, 5, x_55);
lean_ctor_set(x_56, 6, x_42);
lean_ctor_set(x_56, 7, x_43);
lean_ctor_set(x_56, 8, x_44);
lean_ctor_set(x_56, 9, x_45);
lean_ctor_set(x_56, 10, x_46);
lean_ctor_set(x_56, 11, x_47);
lean_ctor_set(x_56, 12, x_48);
lean_ctor_set(x_56, 13, x_49);
lean_ctor_set(x_56, 14, x_51);
lean_ctor_set(x_56, 15, x_52);
lean_ctor_set(x_56, 16, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*17, x_50);
lean_ctor_set(x_18, 1, x_56);
x_57 = lean_st_ref_set(x_5, x_17, x_20);
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
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_62 = lean_ctor_get(x_18, 0);
x_63 = lean_ctor_get(x_18, 2);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_18);
x_64 = lean_ctor_get(x_19, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_19, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_19, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_19, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_19, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_19, 5);
lean_inc(x_69);
x_70 = lean_ctor_get(x_19, 6);
lean_inc(x_70);
x_71 = lean_ctor_get(x_19, 7);
lean_inc(x_71);
x_72 = lean_ctor_get(x_19, 8);
lean_inc(x_72);
x_73 = lean_ctor_get(x_19, 9);
lean_inc(x_73);
x_74 = lean_ctor_get(x_19, 10);
lean_inc(x_74);
x_75 = lean_ctor_get(x_19, 11);
lean_inc(x_75);
x_76 = lean_ctor_get(x_19, 12);
lean_inc(x_76);
x_77 = lean_ctor_get(x_19, 13);
lean_inc(x_77);
x_78 = lean_ctor_get_uint8(x_19, sizeof(void*)*17);
x_79 = lean_ctor_get(x_19, 14);
lean_inc(x_79);
x_80 = lean_ctor_get(x_19, 15);
lean_inc(x_80);
x_81 = lean_ctor_get(x_19, 16);
lean_inc(x_81);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 lean_ctor_release(x_19, 7);
 lean_ctor_release(x_19, 8);
 lean_ctor_release(x_19, 9);
 lean_ctor_release(x_19, 10);
 lean_ctor_release(x_19, 11);
 lean_ctor_release(x_19, 12);
 lean_ctor_release(x_19, 13);
 lean_ctor_release(x_19, 14);
 lean_ctor_release(x_19, 15);
 lean_ctor_release(x_19, 16);
 x_82 = x_19;
} else {
 lean_dec_ref(x_19);
 x_82 = lean_box(0);
}
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_2);
x_84 = l_Lean_PersistentArray_set___rarg(x_69, x_3, x_83);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 17, 1);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_64);
lean_ctor_set(x_85, 1, x_65);
lean_ctor_set(x_85, 2, x_66);
lean_ctor_set(x_85, 3, x_67);
lean_ctor_set(x_85, 4, x_68);
lean_ctor_set(x_85, 5, x_84);
lean_ctor_set(x_85, 6, x_70);
lean_ctor_set(x_85, 7, x_71);
lean_ctor_set(x_85, 8, x_72);
lean_ctor_set(x_85, 9, x_73);
lean_ctor_set(x_85, 10, x_74);
lean_ctor_set(x_85, 11, x_75);
lean_ctor_set(x_85, 12, x_76);
lean_ctor_set(x_85, 13, x_77);
lean_ctor_set(x_85, 14, x_79);
lean_ctor_set(x_85, 15, x_80);
lean_ctor_set(x_85, 16, x_81);
lean_ctor_set_uint8(x_85, sizeof(void*)*17, x_78);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_62);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_63);
lean_ctor_set(x_17, 14, x_86);
x_87 = lean_st_ref_set(x_5, x_17, x_20);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_box(0);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_92 = lean_ctor_get(x_17, 0);
x_93 = lean_ctor_get(x_17, 1);
x_94 = lean_ctor_get(x_17, 2);
x_95 = lean_ctor_get(x_17, 3);
x_96 = lean_ctor_get(x_17, 4);
x_97 = lean_ctor_get(x_17, 5);
x_98 = lean_ctor_get(x_17, 6);
x_99 = lean_ctor_get(x_17, 7);
x_100 = lean_ctor_get_uint8(x_17, sizeof(void*)*16);
x_101 = lean_ctor_get(x_17, 8);
x_102 = lean_ctor_get(x_17, 9);
x_103 = lean_ctor_get(x_17, 10);
x_104 = lean_ctor_get(x_17, 11);
x_105 = lean_ctor_get(x_17, 12);
x_106 = lean_ctor_get(x_17, 13);
x_107 = lean_ctor_get(x_17, 15);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_17);
x_108 = lean_ctor_get(x_18, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_18, 2);
lean_inc(x_109);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_110 = x_18;
} else {
 lean_dec_ref(x_18);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_19, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_19, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_19, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_19, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_19, 4);
lean_inc(x_115);
x_116 = lean_ctor_get(x_19, 5);
lean_inc(x_116);
x_117 = lean_ctor_get(x_19, 6);
lean_inc(x_117);
x_118 = lean_ctor_get(x_19, 7);
lean_inc(x_118);
x_119 = lean_ctor_get(x_19, 8);
lean_inc(x_119);
x_120 = lean_ctor_get(x_19, 9);
lean_inc(x_120);
x_121 = lean_ctor_get(x_19, 10);
lean_inc(x_121);
x_122 = lean_ctor_get(x_19, 11);
lean_inc(x_122);
x_123 = lean_ctor_get(x_19, 12);
lean_inc(x_123);
x_124 = lean_ctor_get(x_19, 13);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_19, sizeof(void*)*17);
x_126 = lean_ctor_get(x_19, 14);
lean_inc(x_126);
x_127 = lean_ctor_get(x_19, 15);
lean_inc(x_127);
x_128 = lean_ctor_get(x_19, 16);
lean_inc(x_128);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 lean_ctor_release(x_19, 7);
 lean_ctor_release(x_19, 8);
 lean_ctor_release(x_19, 9);
 lean_ctor_release(x_19, 10);
 lean_ctor_release(x_19, 11);
 lean_ctor_release(x_19, 12);
 lean_ctor_release(x_19, 13);
 lean_ctor_release(x_19, 14);
 lean_ctor_release(x_19, 15);
 lean_ctor_release(x_19, 16);
 x_129 = x_19;
} else {
 lean_dec_ref(x_19);
 x_129 = lean_box(0);
}
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_2);
x_131 = l_Lean_PersistentArray_set___rarg(x_116, x_3, x_130);
if (lean_is_scalar(x_129)) {
 x_132 = lean_alloc_ctor(0, 17, 1);
} else {
 x_132 = x_129;
}
lean_ctor_set(x_132, 0, x_111);
lean_ctor_set(x_132, 1, x_112);
lean_ctor_set(x_132, 2, x_113);
lean_ctor_set(x_132, 3, x_114);
lean_ctor_set(x_132, 4, x_115);
lean_ctor_set(x_132, 5, x_131);
lean_ctor_set(x_132, 6, x_117);
lean_ctor_set(x_132, 7, x_118);
lean_ctor_set(x_132, 8, x_119);
lean_ctor_set(x_132, 9, x_120);
lean_ctor_set(x_132, 10, x_121);
lean_ctor_set(x_132, 11, x_122);
lean_ctor_set(x_132, 12, x_123);
lean_ctor_set(x_132, 13, x_124);
lean_ctor_set(x_132, 14, x_126);
lean_ctor_set(x_132, 15, x_127);
lean_ctor_set(x_132, 16, x_128);
lean_ctor_set_uint8(x_132, sizeof(void*)*17, x_125);
if (lean_is_scalar(x_110)) {
 x_133 = lean_alloc_ctor(0, 3, 0);
} else {
 x_133 = x_110;
}
lean_ctor_set(x_133, 0, x_108);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_133, 2, x_109);
x_134 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_134, 0, x_92);
lean_ctor_set(x_134, 1, x_93);
lean_ctor_set(x_134, 2, x_94);
lean_ctor_set(x_134, 3, x_95);
lean_ctor_set(x_134, 4, x_96);
lean_ctor_set(x_134, 5, x_97);
lean_ctor_set(x_134, 6, x_98);
lean_ctor_set(x_134, 7, x_99);
lean_ctor_set(x_134, 8, x_101);
lean_ctor_set(x_134, 9, x_102);
lean_ctor_set(x_134, 10, x_103);
lean_ctor_set(x_134, 11, x_104);
lean_ctor_set(x_134, 12, x_105);
lean_ctor_set(x_134, 13, x_106);
lean_ctor_set(x_134, 14, x_133);
lean_ctor_set(x_134, 15, x_107);
lean_ctor_set_uint8(x_134, sizeof(void*)*16, x_100);
x_135 = lean_st_ref_set(x_5, x_134, x_20);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_137 = x_135;
} else {
 lean_dec_ref(x_135);
 x_137 = lean_box(0);
}
x_138 = lean_box(0);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
return x_139;
}
}
else
{
uint8_t x_140; 
lean_dec(x_2);
x_140 = !lean_is_exclusive(x_14);
if (x_140 == 0)
{
return x_14;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_14, 0);
x_142 = lean_ctor_get(x_14, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_14);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_61; lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; 
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_428 = lean_box(0);
x_429 = lean_ctor_get(x_18, 5);
lean_inc(x_429);
lean_dec(x_18);
x_430 = lean_ctor_get(x_429, 2);
lean_inc(x_430);
x_431 = lean_nat_dec_lt(x_3, x_430);
lean_dec(x_430);
if (x_431 == 0)
{
lean_object* x_432; 
lean_dec(x_429);
x_432 = l_outOfBounds___rarg(x_428);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; 
lean_dec(x_6);
x_433 = lean_box(0);
x_20 = x_433;
goto block_60;
}
else
{
lean_object* x_434; 
lean_dec(x_1);
x_434 = lean_ctor_get(x_432, 0);
lean_inc(x_434);
lean_dec(x_432);
x_61 = x_434;
goto block_427;
}
}
else
{
lean_object* x_435; 
x_435 = l_Lean_PersistentArray_get_x21___rarg(x_428, x_429, x_3);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; 
lean_dec(x_6);
x_436 = lean_box(0);
x_20 = x_436;
goto block_60;
}
else
{
lean_object* x_437; 
lean_dec(x_1);
x_437 = lean_ctor_get(x_435, 0);
lean_inc(x_437);
lean_dec(x_435);
x_61 = x_437;
goto block_427;
}
}
block_60:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_20);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__3;
x_22 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1(x_1, x_2, x_3, x_26, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_22, 1);
x_30 = lean_ctor_get(x_22, 0);
lean_dec(x_30);
lean_inc(x_2);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_29);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_33);
lean_ctor_set(x_31, 0, x_35);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_35);
lean_ctor_set(x_22, 0, x_31);
x_36 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_21, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1(x_1, x_2, x_3, x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_38);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_37);
lean_dec(x_3);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_42);
lean_ctor_set(x_22, 0, x_43);
x_44 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_21, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1(x_1, x_2, x_3, x_45, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_46);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_45);
lean_dec(x_3);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_dec(x_22);
lean_inc(x_2);
x_49 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(7, 2, 0);
} else {
 x_54 = x_52;
 lean_ctor_set_tag(x_54, 7);
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_21, x_55, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_51);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1(x_1, x_2, x_3, x_57, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_58);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_57);
lean_dec(x_3);
return x_59;
}
}
}
block_427:
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_63 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___rarg(x_61, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_63;
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_65 = lean_ctor_get(x_62, 0);
x_66 = lean_ctor_get(x_62, 2);
x_67 = lean_ctor_get(x_62, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
x_69 = lean_int_mul(x_4, x_68);
x_70 = lean_int_mul(x_65, x_5);
x_71 = l_Lean_Meta_Grind_Arith_gcdExt(x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_75 = lean_ctor_get(x_72, 0);
x_76 = lean_ctor_get(x_72, 1);
x_77 = lean_int_mul(x_75, x_68);
lean_dec(x_75);
lean_inc(x_6);
x_78 = l_Int_Linear_Poly_mul(x_6, x_77);
lean_dec(x_77);
x_79 = lean_int_mul(x_76, x_5);
lean_dec(x_76);
lean_inc(x_66);
x_80 = l_Int_Linear_Poly_mul(x_66, x_79);
lean_dec(x_79);
x_81 = lean_int_mul(x_5, x_68);
lean_dec(x_68);
x_82 = lean_unsigned_to_nat(100000000u);
x_83 = l_Int_Linear_Poly_combine_x27(x_82, x_78, x_80);
lean_inc(x_3);
lean_inc(x_73);
lean_ctor_set(x_62, 2, x_83);
lean_ctor_set(x_62, 1, x_3);
lean_ctor_set(x_62, 0, x_73);
lean_inc(x_61);
lean_inc(x_2);
lean_ctor_set_tag(x_72, 4);
lean_ctor_set(x_72, 1, x_61);
lean_ctor_set(x_72, 0, x_2);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_62);
lean_ctor_set(x_84, 2, x_72);
x_85 = lean_st_ref_take(x_8, x_19);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 14);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = !lean_is_exclusive(x_86);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_86, 14);
lean_dec(x_91);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_87, 1);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_88);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_95 = lean_ctor_get(x_88, 5);
x_96 = lean_box(0);
x_97 = l_Lean_PersistentArray_set___rarg(x_95, x_3, x_96);
lean_dec(x_3);
lean_ctor_set(x_88, 5, x_97);
x_98 = lean_st_ref_set(x_8, x_86, x_89);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_98, 1);
x_101 = lean_ctor_get(x_98, 0);
lean_dec(x_101);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_102 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_84, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l_Int_Linear_Poly_mul(x_6, x_65);
lean_dec(x_65);
x_105 = lean_int_neg(x_4);
x_106 = l_Int_Linear_Poly_mul(x_66, x_105);
lean_dec(x_105);
x_107 = l_Int_Linear_Poly_combine_x27(x_82, x_104, x_106);
lean_ctor_set_tag(x_98, 5);
lean_ctor_set(x_98, 1, x_61);
lean_ctor_set(x_98, 0, x_2);
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_73);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_108, 2, x_98);
x_109 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_108, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_103);
return x_109;
}
else
{
uint8_t x_110; 
lean_free_object(x_98);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_61);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_102);
if (x_110 == 0)
{
return x_102;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_102, 0);
x_112 = lean_ctor_get(x_102, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_102);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_98, 1);
lean_inc(x_114);
lean_dec(x_98);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_115 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_84, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_117 = l_Int_Linear_Poly_mul(x_6, x_65);
lean_dec(x_65);
x_118 = lean_int_neg(x_4);
x_119 = l_Int_Linear_Poly_mul(x_66, x_118);
lean_dec(x_118);
x_120 = l_Int_Linear_Poly_combine_x27(x_82, x_117, x_119);
x_121 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_121, 0, x_2);
lean_ctor_set(x_121, 1, x_61);
x_122 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_122, 0, x_73);
lean_ctor_set(x_122, 1, x_120);
lean_ctor_set(x_122, 2, x_121);
x_123 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_122, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_116);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_61);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_124 = lean_ctor_get(x_115, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_115, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_126 = x_115;
} else {
 lean_dec_ref(x_115);
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
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_128 = lean_ctor_get(x_88, 0);
x_129 = lean_ctor_get(x_88, 1);
x_130 = lean_ctor_get(x_88, 2);
x_131 = lean_ctor_get(x_88, 3);
x_132 = lean_ctor_get(x_88, 4);
x_133 = lean_ctor_get(x_88, 5);
x_134 = lean_ctor_get(x_88, 6);
x_135 = lean_ctor_get(x_88, 7);
x_136 = lean_ctor_get(x_88, 8);
x_137 = lean_ctor_get(x_88, 9);
x_138 = lean_ctor_get(x_88, 10);
x_139 = lean_ctor_get(x_88, 11);
x_140 = lean_ctor_get(x_88, 12);
x_141 = lean_ctor_get(x_88, 13);
x_142 = lean_ctor_get_uint8(x_88, sizeof(void*)*17);
x_143 = lean_ctor_get(x_88, 14);
x_144 = lean_ctor_get(x_88, 15);
x_145 = lean_ctor_get(x_88, 16);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
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
lean_dec(x_88);
x_146 = lean_box(0);
x_147 = l_Lean_PersistentArray_set___rarg(x_133, x_3, x_146);
lean_dec(x_3);
x_148 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_148, 0, x_128);
lean_ctor_set(x_148, 1, x_129);
lean_ctor_set(x_148, 2, x_130);
lean_ctor_set(x_148, 3, x_131);
lean_ctor_set(x_148, 4, x_132);
lean_ctor_set(x_148, 5, x_147);
lean_ctor_set(x_148, 6, x_134);
lean_ctor_set(x_148, 7, x_135);
lean_ctor_set(x_148, 8, x_136);
lean_ctor_set(x_148, 9, x_137);
lean_ctor_set(x_148, 10, x_138);
lean_ctor_set(x_148, 11, x_139);
lean_ctor_set(x_148, 12, x_140);
lean_ctor_set(x_148, 13, x_141);
lean_ctor_set(x_148, 14, x_143);
lean_ctor_set(x_148, 15, x_144);
lean_ctor_set(x_148, 16, x_145);
lean_ctor_set_uint8(x_148, sizeof(void*)*17, x_142);
lean_ctor_set(x_87, 1, x_148);
x_149 = lean_st_ref_set(x_8, x_86, x_89);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_152 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_84, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_150);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_154 = l_Int_Linear_Poly_mul(x_6, x_65);
lean_dec(x_65);
x_155 = lean_int_neg(x_4);
x_156 = l_Int_Linear_Poly_mul(x_66, x_155);
lean_dec(x_155);
x_157 = l_Int_Linear_Poly_combine_x27(x_82, x_154, x_156);
if (lean_is_scalar(x_151)) {
 x_158 = lean_alloc_ctor(5, 2, 0);
} else {
 x_158 = x_151;
 lean_ctor_set_tag(x_158, 5);
}
lean_ctor_set(x_158, 0, x_2);
lean_ctor_set(x_158, 1, x_61);
x_159 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_159, 0, x_73);
lean_ctor_set(x_159, 1, x_157);
lean_ctor_set(x_159, 2, x_158);
x_160 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_159, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_153);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_151);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_61);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_161 = lean_ctor_get(x_152, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_152, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_163 = x_152;
} else {
 lean_dec_ref(x_152);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_165 = lean_ctor_get(x_87, 0);
x_166 = lean_ctor_get(x_87, 2);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_87);
x_167 = lean_ctor_get(x_88, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_88, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_88, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_88, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_88, 4);
lean_inc(x_171);
x_172 = lean_ctor_get(x_88, 5);
lean_inc(x_172);
x_173 = lean_ctor_get(x_88, 6);
lean_inc(x_173);
x_174 = lean_ctor_get(x_88, 7);
lean_inc(x_174);
x_175 = lean_ctor_get(x_88, 8);
lean_inc(x_175);
x_176 = lean_ctor_get(x_88, 9);
lean_inc(x_176);
x_177 = lean_ctor_get(x_88, 10);
lean_inc(x_177);
x_178 = lean_ctor_get(x_88, 11);
lean_inc(x_178);
x_179 = lean_ctor_get(x_88, 12);
lean_inc(x_179);
x_180 = lean_ctor_get(x_88, 13);
lean_inc(x_180);
x_181 = lean_ctor_get_uint8(x_88, sizeof(void*)*17);
x_182 = lean_ctor_get(x_88, 14);
lean_inc(x_182);
x_183 = lean_ctor_get(x_88, 15);
lean_inc(x_183);
x_184 = lean_ctor_get(x_88, 16);
lean_inc(x_184);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 lean_ctor_release(x_88, 5);
 lean_ctor_release(x_88, 6);
 lean_ctor_release(x_88, 7);
 lean_ctor_release(x_88, 8);
 lean_ctor_release(x_88, 9);
 lean_ctor_release(x_88, 10);
 lean_ctor_release(x_88, 11);
 lean_ctor_release(x_88, 12);
 lean_ctor_release(x_88, 13);
 lean_ctor_release(x_88, 14);
 lean_ctor_release(x_88, 15);
 lean_ctor_release(x_88, 16);
 x_185 = x_88;
} else {
 lean_dec_ref(x_88);
 x_185 = lean_box(0);
}
x_186 = lean_box(0);
x_187 = l_Lean_PersistentArray_set___rarg(x_172, x_3, x_186);
lean_dec(x_3);
if (lean_is_scalar(x_185)) {
 x_188 = lean_alloc_ctor(0, 17, 1);
} else {
 x_188 = x_185;
}
lean_ctor_set(x_188, 0, x_167);
lean_ctor_set(x_188, 1, x_168);
lean_ctor_set(x_188, 2, x_169);
lean_ctor_set(x_188, 3, x_170);
lean_ctor_set(x_188, 4, x_171);
lean_ctor_set(x_188, 5, x_187);
lean_ctor_set(x_188, 6, x_173);
lean_ctor_set(x_188, 7, x_174);
lean_ctor_set(x_188, 8, x_175);
lean_ctor_set(x_188, 9, x_176);
lean_ctor_set(x_188, 10, x_177);
lean_ctor_set(x_188, 11, x_178);
lean_ctor_set(x_188, 12, x_179);
lean_ctor_set(x_188, 13, x_180);
lean_ctor_set(x_188, 14, x_182);
lean_ctor_set(x_188, 15, x_183);
lean_ctor_set(x_188, 16, x_184);
lean_ctor_set_uint8(x_188, sizeof(void*)*17, x_181);
x_189 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_189, 0, x_165);
lean_ctor_set(x_189, 1, x_188);
lean_ctor_set(x_189, 2, x_166);
lean_ctor_set(x_86, 14, x_189);
x_190 = lean_st_ref_set(x_8, x_86, x_89);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_192 = x_190;
} else {
 lean_dec_ref(x_190);
 x_192 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_193 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_84, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_191);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = l_Int_Linear_Poly_mul(x_6, x_65);
lean_dec(x_65);
x_196 = lean_int_neg(x_4);
x_197 = l_Int_Linear_Poly_mul(x_66, x_196);
lean_dec(x_196);
x_198 = l_Int_Linear_Poly_combine_x27(x_82, x_195, x_197);
if (lean_is_scalar(x_192)) {
 x_199 = lean_alloc_ctor(5, 2, 0);
} else {
 x_199 = x_192;
 lean_ctor_set_tag(x_199, 5);
}
lean_ctor_set(x_199, 0, x_2);
lean_ctor_set(x_199, 1, x_61);
x_200 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_200, 0, x_73);
lean_ctor_set(x_200, 1, x_198);
lean_ctor_set(x_200, 2, x_199);
x_201 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_200, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_194);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_192);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_61);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_202 = lean_ctor_get(x_193, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_193, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_204 = x_193;
} else {
 lean_dec_ref(x_193);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_206 = lean_ctor_get(x_86, 0);
x_207 = lean_ctor_get(x_86, 1);
x_208 = lean_ctor_get(x_86, 2);
x_209 = lean_ctor_get(x_86, 3);
x_210 = lean_ctor_get(x_86, 4);
x_211 = lean_ctor_get(x_86, 5);
x_212 = lean_ctor_get(x_86, 6);
x_213 = lean_ctor_get(x_86, 7);
x_214 = lean_ctor_get_uint8(x_86, sizeof(void*)*16);
x_215 = lean_ctor_get(x_86, 8);
x_216 = lean_ctor_get(x_86, 9);
x_217 = lean_ctor_get(x_86, 10);
x_218 = lean_ctor_get(x_86, 11);
x_219 = lean_ctor_get(x_86, 12);
x_220 = lean_ctor_get(x_86, 13);
x_221 = lean_ctor_get(x_86, 15);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_86);
x_222 = lean_ctor_get(x_87, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_87, 2);
lean_inc(x_223);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 x_224 = x_87;
} else {
 lean_dec_ref(x_87);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_88, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_88, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_88, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_88, 3);
lean_inc(x_228);
x_229 = lean_ctor_get(x_88, 4);
lean_inc(x_229);
x_230 = lean_ctor_get(x_88, 5);
lean_inc(x_230);
x_231 = lean_ctor_get(x_88, 6);
lean_inc(x_231);
x_232 = lean_ctor_get(x_88, 7);
lean_inc(x_232);
x_233 = lean_ctor_get(x_88, 8);
lean_inc(x_233);
x_234 = lean_ctor_get(x_88, 9);
lean_inc(x_234);
x_235 = lean_ctor_get(x_88, 10);
lean_inc(x_235);
x_236 = lean_ctor_get(x_88, 11);
lean_inc(x_236);
x_237 = lean_ctor_get(x_88, 12);
lean_inc(x_237);
x_238 = lean_ctor_get(x_88, 13);
lean_inc(x_238);
x_239 = lean_ctor_get_uint8(x_88, sizeof(void*)*17);
x_240 = lean_ctor_get(x_88, 14);
lean_inc(x_240);
x_241 = lean_ctor_get(x_88, 15);
lean_inc(x_241);
x_242 = lean_ctor_get(x_88, 16);
lean_inc(x_242);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 lean_ctor_release(x_88, 5);
 lean_ctor_release(x_88, 6);
 lean_ctor_release(x_88, 7);
 lean_ctor_release(x_88, 8);
 lean_ctor_release(x_88, 9);
 lean_ctor_release(x_88, 10);
 lean_ctor_release(x_88, 11);
 lean_ctor_release(x_88, 12);
 lean_ctor_release(x_88, 13);
 lean_ctor_release(x_88, 14);
 lean_ctor_release(x_88, 15);
 lean_ctor_release(x_88, 16);
 x_243 = x_88;
} else {
 lean_dec_ref(x_88);
 x_243 = lean_box(0);
}
x_244 = lean_box(0);
x_245 = l_Lean_PersistentArray_set___rarg(x_230, x_3, x_244);
lean_dec(x_3);
if (lean_is_scalar(x_243)) {
 x_246 = lean_alloc_ctor(0, 17, 1);
} else {
 x_246 = x_243;
}
lean_ctor_set(x_246, 0, x_225);
lean_ctor_set(x_246, 1, x_226);
lean_ctor_set(x_246, 2, x_227);
lean_ctor_set(x_246, 3, x_228);
lean_ctor_set(x_246, 4, x_229);
lean_ctor_set(x_246, 5, x_245);
lean_ctor_set(x_246, 6, x_231);
lean_ctor_set(x_246, 7, x_232);
lean_ctor_set(x_246, 8, x_233);
lean_ctor_set(x_246, 9, x_234);
lean_ctor_set(x_246, 10, x_235);
lean_ctor_set(x_246, 11, x_236);
lean_ctor_set(x_246, 12, x_237);
lean_ctor_set(x_246, 13, x_238);
lean_ctor_set(x_246, 14, x_240);
lean_ctor_set(x_246, 15, x_241);
lean_ctor_set(x_246, 16, x_242);
lean_ctor_set_uint8(x_246, sizeof(void*)*17, x_239);
if (lean_is_scalar(x_224)) {
 x_247 = lean_alloc_ctor(0, 3, 0);
} else {
 x_247 = x_224;
}
lean_ctor_set(x_247, 0, x_222);
lean_ctor_set(x_247, 1, x_246);
lean_ctor_set(x_247, 2, x_223);
x_248 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_248, 0, x_206);
lean_ctor_set(x_248, 1, x_207);
lean_ctor_set(x_248, 2, x_208);
lean_ctor_set(x_248, 3, x_209);
lean_ctor_set(x_248, 4, x_210);
lean_ctor_set(x_248, 5, x_211);
lean_ctor_set(x_248, 6, x_212);
lean_ctor_set(x_248, 7, x_213);
lean_ctor_set(x_248, 8, x_215);
lean_ctor_set(x_248, 9, x_216);
lean_ctor_set(x_248, 10, x_217);
lean_ctor_set(x_248, 11, x_218);
lean_ctor_set(x_248, 12, x_219);
lean_ctor_set(x_248, 13, x_220);
lean_ctor_set(x_248, 14, x_247);
lean_ctor_set(x_248, 15, x_221);
lean_ctor_set_uint8(x_248, sizeof(void*)*16, x_214);
x_249 = lean_st_ref_set(x_8, x_248, x_89);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_251 = x_249;
} else {
 lean_dec_ref(x_249);
 x_251 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_252 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_84, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_250);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_254 = l_Int_Linear_Poly_mul(x_6, x_65);
lean_dec(x_65);
x_255 = lean_int_neg(x_4);
x_256 = l_Int_Linear_Poly_mul(x_66, x_255);
lean_dec(x_255);
x_257 = l_Int_Linear_Poly_combine_x27(x_82, x_254, x_256);
if (lean_is_scalar(x_251)) {
 x_258 = lean_alloc_ctor(5, 2, 0);
} else {
 x_258 = x_251;
 lean_ctor_set_tag(x_258, 5);
}
lean_ctor_set(x_258, 0, x_2);
lean_ctor_set(x_258, 1, x_61);
x_259 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_259, 0, x_73);
lean_ctor_set(x_259, 1, x_257);
lean_ctor_set(x_259, 2, x_258);
x_260 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_259, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_253);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_251);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_61);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_261 = lean_ctor_get(x_252, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_252, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_263 = x_252;
} else {
 lean_dec_ref(x_252);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_265 = lean_ctor_get(x_72, 0);
x_266 = lean_ctor_get(x_72, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_72);
x_267 = lean_int_mul(x_265, x_68);
lean_dec(x_265);
lean_inc(x_6);
x_268 = l_Int_Linear_Poly_mul(x_6, x_267);
lean_dec(x_267);
x_269 = lean_int_mul(x_266, x_5);
lean_dec(x_266);
lean_inc(x_66);
x_270 = l_Int_Linear_Poly_mul(x_66, x_269);
lean_dec(x_269);
x_271 = lean_int_mul(x_5, x_68);
lean_dec(x_68);
x_272 = lean_unsigned_to_nat(100000000u);
x_273 = l_Int_Linear_Poly_combine_x27(x_272, x_268, x_270);
lean_inc(x_3);
lean_inc(x_73);
lean_ctor_set(x_62, 2, x_273);
lean_ctor_set(x_62, 1, x_3);
lean_ctor_set(x_62, 0, x_73);
lean_inc(x_61);
lean_inc(x_2);
x_274 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_274, 0, x_2);
lean_ctor_set(x_274, 1, x_61);
x_275 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_275, 0, x_271);
lean_ctor_set(x_275, 1, x_62);
lean_ctor_set(x_275, 2, x_274);
x_276 = lean_st_ref_take(x_8, x_19);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_277, 14);
lean_inc(x_278);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_276, 1);
lean_inc(x_280);
lean_dec(x_276);
x_281 = lean_ctor_get(x_277, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_277, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_277, 2);
lean_inc(x_283);
x_284 = lean_ctor_get(x_277, 3);
lean_inc(x_284);
x_285 = lean_ctor_get(x_277, 4);
lean_inc(x_285);
x_286 = lean_ctor_get(x_277, 5);
lean_inc(x_286);
x_287 = lean_ctor_get(x_277, 6);
lean_inc(x_287);
x_288 = lean_ctor_get(x_277, 7);
lean_inc(x_288);
x_289 = lean_ctor_get_uint8(x_277, sizeof(void*)*16);
x_290 = lean_ctor_get(x_277, 8);
lean_inc(x_290);
x_291 = lean_ctor_get(x_277, 9);
lean_inc(x_291);
x_292 = lean_ctor_get(x_277, 10);
lean_inc(x_292);
x_293 = lean_ctor_get(x_277, 11);
lean_inc(x_293);
x_294 = lean_ctor_get(x_277, 12);
lean_inc(x_294);
x_295 = lean_ctor_get(x_277, 13);
lean_inc(x_295);
x_296 = lean_ctor_get(x_277, 15);
lean_inc(x_296);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 lean_ctor_release(x_277, 2);
 lean_ctor_release(x_277, 3);
 lean_ctor_release(x_277, 4);
 lean_ctor_release(x_277, 5);
 lean_ctor_release(x_277, 6);
 lean_ctor_release(x_277, 7);
 lean_ctor_release(x_277, 8);
 lean_ctor_release(x_277, 9);
 lean_ctor_release(x_277, 10);
 lean_ctor_release(x_277, 11);
 lean_ctor_release(x_277, 12);
 lean_ctor_release(x_277, 13);
 lean_ctor_release(x_277, 14);
 lean_ctor_release(x_277, 15);
 x_297 = x_277;
} else {
 lean_dec_ref(x_277);
 x_297 = lean_box(0);
}
x_298 = lean_ctor_get(x_278, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_278, 2);
lean_inc(x_299);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 lean_ctor_release(x_278, 2);
 x_300 = x_278;
} else {
 lean_dec_ref(x_278);
 x_300 = lean_box(0);
}
x_301 = lean_ctor_get(x_279, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_279, 1);
lean_inc(x_302);
x_303 = lean_ctor_get(x_279, 2);
lean_inc(x_303);
x_304 = lean_ctor_get(x_279, 3);
lean_inc(x_304);
x_305 = lean_ctor_get(x_279, 4);
lean_inc(x_305);
x_306 = lean_ctor_get(x_279, 5);
lean_inc(x_306);
x_307 = lean_ctor_get(x_279, 6);
lean_inc(x_307);
x_308 = lean_ctor_get(x_279, 7);
lean_inc(x_308);
x_309 = lean_ctor_get(x_279, 8);
lean_inc(x_309);
x_310 = lean_ctor_get(x_279, 9);
lean_inc(x_310);
x_311 = lean_ctor_get(x_279, 10);
lean_inc(x_311);
x_312 = lean_ctor_get(x_279, 11);
lean_inc(x_312);
x_313 = lean_ctor_get(x_279, 12);
lean_inc(x_313);
x_314 = lean_ctor_get(x_279, 13);
lean_inc(x_314);
x_315 = lean_ctor_get_uint8(x_279, sizeof(void*)*17);
x_316 = lean_ctor_get(x_279, 14);
lean_inc(x_316);
x_317 = lean_ctor_get(x_279, 15);
lean_inc(x_317);
x_318 = lean_ctor_get(x_279, 16);
lean_inc(x_318);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 lean_ctor_release(x_279, 3);
 lean_ctor_release(x_279, 4);
 lean_ctor_release(x_279, 5);
 lean_ctor_release(x_279, 6);
 lean_ctor_release(x_279, 7);
 lean_ctor_release(x_279, 8);
 lean_ctor_release(x_279, 9);
 lean_ctor_release(x_279, 10);
 lean_ctor_release(x_279, 11);
 lean_ctor_release(x_279, 12);
 lean_ctor_release(x_279, 13);
 lean_ctor_release(x_279, 14);
 lean_ctor_release(x_279, 15);
 lean_ctor_release(x_279, 16);
 x_319 = x_279;
} else {
 lean_dec_ref(x_279);
 x_319 = lean_box(0);
}
x_320 = lean_box(0);
x_321 = l_Lean_PersistentArray_set___rarg(x_306, x_3, x_320);
lean_dec(x_3);
if (lean_is_scalar(x_319)) {
 x_322 = lean_alloc_ctor(0, 17, 1);
} else {
 x_322 = x_319;
}
lean_ctor_set(x_322, 0, x_301);
lean_ctor_set(x_322, 1, x_302);
lean_ctor_set(x_322, 2, x_303);
lean_ctor_set(x_322, 3, x_304);
lean_ctor_set(x_322, 4, x_305);
lean_ctor_set(x_322, 5, x_321);
lean_ctor_set(x_322, 6, x_307);
lean_ctor_set(x_322, 7, x_308);
lean_ctor_set(x_322, 8, x_309);
lean_ctor_set(x_322, 9, x_310);
lean_ctor_set(x_322, 10, x_311);
lean_ctor_set(x_322, 11, x_312);
lean_ctor_set(x_322, 12, x_313);
lean_ctor_set(x_322, 13, x_314);
lean_ctor_set(x_322, 14, x_316);
lean_ctor_set(x_322, 15, x_317);
lean_ctor_set(x_322, 16, x_318);
lean_ctor_set_uint8(x_322, sizeof(void*)*17, x_315);
if (lean_is_scalar(x_300)) {
 x_323 = lean_alloc_ctor(0, 3, 0);
} else {
 x_323 = x_300;
}
lean_ctor_set(x_323, 0, x_298);
lean_ctor_set(x_323, 1, x_322);
lean_ctor_set(x_323, 2, x_299);
if (lean_is_scalar(x_297)) {
 x_324 = lean_alloc_ctor(0, 16, 1);
} else {
 x_324 = x_297;
}
lean_ctor_set(x_324, 0, x_281);
lean_ctor_set(x_324, 1, x_282);
lean_ctor_set(x_324, 2, x_283);
lean_ctor_set(x_324, 3, x_284);
lean_ctor_set(x_324, 4, x_285);
lean_ctor_set(x_324, 5, x_286);
lean_ctor_set(x_324, 6, x_287);
lean_ctor_set(x_324, 7, x_288);
lean_ctor_set(x_324, 8, x_290);
lean_ctor_set(x_324, 9, x_291);
lean_ctor_set(x_324, 10, x_292);
lean_ctor_set(x_324, 11, x_293);
lean_ctor_set(x_324, 12, x_294);
lean_ctor_set(x_324, 13, x_295);
lean_ctor_set(x_324, 14, x_323);
lean_ctor_set(x_324, 15, x_296);
lean_ctor_set_uint8(x_324, sizeof(void*)*16, x_289);
x_325 = lean_st_ref_set(x_8, x_324, x_280);
x_326 = lean_ctor_get(x_325, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_327 = x_325;
} else {
 lean_dec_ref(x_325);
 x_327 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_328 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_275, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_326);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_330 = l_Int_Linear_Poly_mul(x_6, x_65);
lean_dec(x_65);
x_331 = lean_int_neg(x_4);
x_332 = l_Int_Linear_Poly_mul(x_66, x_331);
lean_dec(x_331);
x_333 = l_Int_Linear_Poly_combine_x27(x_272, x_330, x_332);
if (lean_is_scalar(x_327)) {
 x_334 = lean_alloc_ctor(5, 2, 0);
} else {
 x_334 = x_327;
 lean_ctor_set_tag(x_334, 5);
}
lean_ctor_set(x_334, 0, x_2);
lean_ctor_set(x_334, 1, x_61);
x_335 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_335, 0, x_73);
lean_ctor_set(x_335, 1, x_333);
lean_ctor_set(x_335, 2, x_334);
x_336 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_335, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_329);
return x_336;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_327);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_61);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_337 = lean_ctor_get(x_328, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_328, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_339 = x_328;
} else {
 lean_dec_ref(x_328);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(1, 2, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_338);
return x_340;
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_341 = lean_ctor_get(x_62, 0);
x_342 = lean_ctor_get(x_62, 2);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_62);
x_343 = lean_ctor_get(x_61, 0);
lean_inc(x_343);
x_344 = lean_int_mul(x_4, x_343);
x_345 = lean_int_mul(x_341, x_5);
x_346 = l_Lean_Meta_Grind_Arith_gcdExt(x_344, x_345);
lean_dec(x_345);
lean_dec(x_344);
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 0);
lean_inc(x_348);
lean_dec(x_346);
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_347, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_351 = x_347;
} else {
 lean_dec_ref(x_347);
 x_351 = lean_box(0);
}
x_352 = lean_int_mul(x_349, x_343);
lean_dec(x_349);
lean_inc(x_6);
x_353 = l_Int_Linear_Poly_mul(x_6, x_352);
lean_dec(x_352);
x_354 = lean_int_mul(x_350, x_5);
lean_dec(x_350);
lean_inc(x_342);
x_355 = l_Int_Linear_Poly_mul(x_342, x_354);
lean_dec(x_354);
x_356 = lean_int_mul(x_5, x_343);
lean_dec(x_343);
x_357 = lean_unsigned_to_nat(100000000u);
x_358 = l_Int_Linear_Poly_combine_x27(x_357, x_353, x_355);
lean_inc(x_3);
lean_inc(x_348);
x_359 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_359, 0, x_348);
lean_ctor_set(x_359, 1, x_3);
lean_ctor_set(x_359, 2, x_358);
lean_inc(x_61);
lean_inc(x_2);
if (lean_is_scalar(x_351)) {
 x_360 = lean_alloc_ctor(4, 2, 0);
} else {
 x_360 = x_351;
 lean_ctor_set_tag(x_360, 4);
}
lean_ctor_set(x_360, 0, x_2);
lean_ctor_set(x_360, 1, x_61);
x_361 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_361, 0, x_356);
lean_ctor_set(x_361, 1, x_359);
lean_ctor_set(x_361, 2, x_360);
x_362 = lean_st_ref_take(x_8, x_19);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_363, 14);
lean_inc(x_364);
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
x_366 = lean_ctor_get(x_362, 1);
lean_inc(x_366);
lean_dec(x_362);
x_367 = lean_ctor_get(x_363, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_363, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_363, 2);
lean_inc(x_369);
x_370 = lean_ctor_get(x_363, 3);
lean_inc(x_370);
x_371 = lean_ctor_get(x_363, 4);
lean_inc(x_371);
x_372 = lean_ctor_get(x_363, 5);
lean_inc(x_372);
x_373 = lean_ctor_get(x_363, 6);
lean_inc(x_373);
x_374 = lean_ctor_get(x_363, 7);
lean_inc(x_374);
x_375 = lean_ctor_get_uint8(x_363, sizeof(void*)*16);
x_376 = lean_ctor_get(x_363, 8);
lean_inc(x_376);
x_377 = lean_ctor_get(x_363, 9);
lean_inc(x_377);
x_378 = lean_ctor_get(x_363, 10);
lean_inc(x_378);
x_379 = lean_ctor_get(x_363, 11);
lean_inc(x_379);
x_380 = lean_ctor_get(x_363, 12);
lean_inc(x_380);
x_381 = lean_ctor_get(x_363, 13);
lean_inc(x_381);
x_382 = lean_ctor_get(x_363, 15);
lean_inc(x_382);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 lean_ctor_release(x_363, 2);
 lean_ctor_release(x_363, 3);
 lean_ctor_release(x_363, 4);
 lean_ctor_release(x_363, 5);
 lean_ctor_release(x_363, 6);
 lean_ctor_release(x_363, 7);
 lean_ctor_release(x_363, 8);
 lean_ctor_release(x_363, 9);
 lean_ctor_release(x_363, 10);
 lean_ctor_release(x_363, 11);
 lean_ctor_release(x_363, 12);
 lean_ctor_release(x_363, 13);
 lean_ctor_release(x_363, 14);
 lean_ctor_release(x_363, 15);
 x_383 = x_363;
} else {
 lean_dec_ref(x_363);
 x_383 = lean_box(0);
}
x_384 = lean_ctor_get(x_364, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_364, 2);
lean_inc(x_385);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 lean_ctor_release(x_364, 2);
 x_386 = x_364;
} else {
 lean_dec_ref(x_364);
 x_386 = lean_box(0);
}
x_387 = lean_ctor_get(x_365, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_365, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_365, 2);
lean_inc(x_389);
x_390 = lean_ctor_get(x_365, 3);
lean_inc(x_390);
x_391 = lean_ctor_get(x_365, 4);
lean_inc(x_391);
x_392 = lean_ctor_get(x_365, 5);
lean_inc(x_392);
x_393 = lean_ctor_get(x_365, 6);
lean_inc(x_393);
x_394 = lean_ctor_get(x_365, 7);
lean_inc(x_394);
x_395 = lean_ctor_get(x_365, 8);
lean_inc(x_395);
x_396 = lean_ctor_get(x_365, 9);
lean_inc(x_396);
x_397 = lean_ctor_get(x_365, 10);
lean_inc(x_397);
x_398 = lean_ctor_get(x_365, 11);
lean_inc(x_398);
x_399 = lean_ctor_get(x_365, 12);
lean_inc(x_399);
x_400 = lean_ctor_get(x_365, 13);
lean_inc(x_400);
x_401 = lean_ctor_get_uint8(x_365, sizeof(void*)*17);
x_402 = lean_ctor_get(x_365, 14);
lean_inc(x_402);
x_403 = lean_ctor_get(x_365, 15);
lean_inc(x_403);
x_404 = lean_ctor_get(x_365, 16);
lean_inc(x_404);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 lean_ctor_release(x_365, 2);
 lean_ctor_release(x_365, 3);
 lean_ctor_release(x_365, 4);
 lean_ctor_release(x_365, 5);
 lean_ctor_release(x_365, 6);
 lean_ctor_release(x_365, 7);
 lean_ctor_release(x_365, 8);
 lean_ctor_release(x_365, 9);
 lean_ctor_release(x_365, 10);
 lean_ctor_release(x_365, 11);
 lean_ctor_release(x_365, 12);
 lean_ctor_release(x_365, 13);
 lean_ctor_release(x_365, 14);
 lean_ctor_release(x_365, 15);
 lean_ctor_release(x_365, 16);
 x_405 = x_365;
} else {
 lean_dec_ref(x_365);
 x_405 = lean_box(0);
}
x_406 = lean_box(0);
x_407 = l_Lean_PersistentArray_set___rarg(x_392, x_3, x_406);
lean_dec(x_3);
if (lean_is_scalar(x_405)) {
 x_408 = lean_alloc_ctor(0, 17, 1);
} else {
 x_408 = x_405;
}
lean_ctor_set(x_408, 0, x_387);
lean_ctor_set(x_408, 1, x_388);
lean_ctor_set(x_408, 2, x_389);
lean_ctor_set(x_408, 3, x_390);
lean_ctor_set(x_408, 4, x_391);
lean_ctor_set(x_408, 5, x_407);
lean_ctor_set(x_408, 6, x_393);
lean_ctor_set(x_408, 7, x_394);
lean_ctor_set(x_408, 8, x_395);
lean_ctor_set(x_408, 9, x_396);
lean_ctor_set(x_408, 10, x_397);
lean_ctor_set(x_408, 11, x_398);
lean_ctor_set(x_408, 12, x_399);
lean_ctor_set(x_408, 13, x_400);
lean_ctor_set(x_408, 14, x_402);
lean_ctor_set(x_408, 15, x_403);
lean_ctor_set(x_408, 16, x_404);
lean_ctor_set_uint8(x_408, sizeof(void*)*17, x_401);
if (lean_is_scalar(x_386)) {
 x_409 = lean_alloc_ctor(0, 3, 0);
} else {
 x_409 = x_386;
}
lean_ctor_set(x_409, 0, x_384);
lean_ctor_set(x_409, 1, x_408);
lean_ctor_set(x_409, 2, x_385);
if (lean_is_scalar(x_383)) {
 x_410 = lean_alloc_ctor(0, 16, 1);
} else {
 x_410 = x_383;
}
lean_ctor_set(x_410, 0, x_367);
lean_ctor_set(x_410, 1, x_368);
lean_ctor_set(x_410, 2, x_369);
lean_ctor_set(x_410, 3, x_370);
lean_ctor_set(x_410, 4, x_371);
lean_ctor_set(x_410, 5, x_372);
lean_ctor_set(x_410, 6, x_373);
lean_ctor_set(x_410, 7, x_374);
lean_ctor_set(x_410, 8, x_376);
lean_ctor_set(x_410, 9, x_377);
lean_ctor_set(x_410, 10, x_378);
lean_ctor_set(x_410, 11, x_379);
lean_ctor_set(x_410, 12, x_380);
lean_ctor_set(x_410, 13, x_381);
lean_ctor_set(x_410, 14, x_409);
lean_ctor_set(x_410, 15, x_382);
lean_ctor_set_uint8(x_410, sizeof(void*)*16, x_375);
x_411 = lean_st_ref_set(x_8, x_410, x_366);
x_412 = lean_ctor_get(x_411, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_413 = x_411;
} else {
 lean_dec_ref(x_411);
 x_413 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_414 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_361, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_412);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
lean_dec(x_414);
x_416 = l_Int_Linear_Poly_mul(x_6, x_341);
lean_dec(x_341);
x_417 = lean_int_neg(x_4);
x_418 = l_Int_Linear_Poly_mul(x_342, x_417);
lean_dec(x_417);
x_419 = l_Int_Linear_Poly_combine_x27(x_357, x_416, x_418);
if (lean_is_scalar(x_413)) {
 x_420 = lean_alloc_ctor(5, 2, 0);
} else {
 x_420 = x_413;
 lean_ctor_set_tag(x_420, 5);
}
lean_ctor_set(x_420, 0, x_2);
lean_ctor_set(x_420, 1, x_61);
x_421 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_421, 0, x_348);
lean_ctor_set(x_421, 1, x_419);
lean_ctor_set(x_421, 2, x_420);
x_422 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_421, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_415);
return x_422;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_413);
lean_dec(x_348);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_61);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_423 = lean_ctor_get(x_414, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_414, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_425 = x_414;
} else {
 lean_dec_ref(x_414);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_423);
lean_ctor_set(x_426, 1, x_424);
return x_426;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_12);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_inc(x_1);
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 0;
x_22 = lean_unbox(x_19);
lean_dec(x_19);
x_23 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_22, x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2(x_12, x_1, x_15, x_14, x_17, x_16, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_17);
lean_dec(x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2(x_12, x_1, x_15, x_14, x_17, x_16, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_14);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__2;
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__3;
x_21 = lean_unbox(x_18);
lean_dec(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_16);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_apply_10(x_20, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_26);
lean_ctor_set(x_24, 0, x_28);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_24);
x_29 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_apply_10(x_20, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_35);
lean_ctor_set(x_16, 0, x_36);
x_37 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_apply_10(x_20, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__3;
x_44 = lean_unbox(x_41);
lean_dec(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_apply_10(x_43, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(7, 2, 0);
} else {
 x_52 = x_50;
 lean_ctor_set_tag(x_52, 7);
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_15, x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_apply_10(x_43, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_56);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_9);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = l_Int_Linear_Poly_isUnsatDvd(x_16, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5(x_14, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___closed__2;
x_22 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__6(x_14, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_22, 1);
x_30 = lean_ctor_get(x_22, 0);
lean_dec(x_30);
lean_inc(x_14);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_33);
lean_ctor_set(x_31, 0, x_35);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_35);
lean_ctor_set(x_22, 0, x_31);
x_36 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_21, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__6(x_14, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_37);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_42);
lean_ctor_set(x_22, 0, x_43);
x_44 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_21, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__6(x_14, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
lean_dec(x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_dec(x_22);
lean_inc(x_14);
x_49 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(7, 2, 0);
} else {
 x_54 = x_52;
 lean_ctor_set_tag(x_54, 7);
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_21, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_51);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__6(x_14, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
lean_dec(x_57);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_13);
if (x_60 == 0)
{
return x_13;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_13, 0);
x_62 = lean_ctor_get(x_13, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_13);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__1;
x_13 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
lean_inc(x_1);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_24);
lean_ctor_set(x_22, 0, x_26);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_26);
lean_ctor_set(x_13, 0, x_22);
x_27 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7(x_1, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
lean_dec(x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_33);
lean_ctor_set(x_13, 0, x_34);
x_35 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7(x_1, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
lean_dec(x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_dec(x_13);
lean_inc(x_1);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(7, 2, 0);
} else {
 x_45 = x_43;
 lean_ctor_set_tag(x_45, 7);
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7(x_1, x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
lean_dec(x_48);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 8);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 9);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 10);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_23 = lean_ctor_get(x_8, 11);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_25 = lean_ctor_get(x_8, 12);
lean_inc(x_25);
x_26 = lean_nat_dec_eq(x_14, x_15);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_8, 12);
lean_dec(x_28);
x_29 = lean_ctor_get(x_8, 11);
lean_dec(x_29);
x_30 = lean_ctor_get(x_8, 10);
lean_dec(x_30);
x_31 = lean_ctor_get(x_8, 9);
lean_dec(x_31);
x_32 = lean_ctor_get(x_8, 8);
lean_dec(x_32);
x_33 = lean_ctor_get(x_8, 7);
lean_dec(x_33);
x_34 = lean_ctor_get(x_8, 6);
lean_dec(x_34);
x_35 = lean_ctor_get(x_8, 5);
lean_dec(x_35);
x_36 = lean_ctor_get(x_8, 4);
lean_dec(x_36);
x_37 = lean_ctor_get(x_8, 3);
lean_dec(x_37);
x_38 = lean_ctor_get(x_8, 2);
lean_dec(x_38);
x_39 = lean_ctor_get(x_8, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_8, 0);
lean_dec(x_40);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_14, x_41);
lean_dec(x_14);
lean_ctor_set(x_8, 3, x_42);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_43 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_box(0);
x_48 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8(x_1, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_46);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_43);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_43, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_43, 0, x_51);
return x_43;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_43);
if (x_55 == 0)
{
return x_43;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_43, 0);
x_57 = lean_ctor_get(x_43, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_43);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_8);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_14, x_59);
lean_dec(x_14);
x_61 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_61, 0, x_11);
lean_ctor_set(x_61, 1, x_12);
lean_ctor_set(x_61, 2, x_13);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_15);
lean_ctor_set(x_61, 5, x_16);
lean_ctor_set(x_61, 6, x_17);
lean_ctor_set(x_61, 7, x_18);
lean_ctor_set(x_61, 8, x_19);
lean_ctor_set(x_61, 9, x_20);
lean_ctor_set(x_61, 10, x_21);
lean_ctor_set(x_61, 11, x_23);
lean_ctor_set(x_61, 12, x_25);
lean_ctor_set_uint8(x_61, sizeof(void*)*13, x_22);
lean_ctor_set_uint8(x_61, sizeof(void*)*13 + 1, x_24);
lean_inc(x_9);
lean_inc(x_61);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_62 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(x_2, x_3, x_4, x_5, x_6, x_7, x_61, x_9, x_10);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_box(0);
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8(x_1, x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_61, x_9, x_65);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_61);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_69 = x_62;
} else {
 lean_dec_ref(x_62);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_61);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_74 = x_62;
} else {
 lean_dec_ref(x_62);
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
lean_object* x_76; 
lean_dec(x_25);
lean_dec(x_23);
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
lean_dec(x_1);
x_76 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___spec__1(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_76;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("non-linear divisibility constraint found", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_not_dvd", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__3;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__4;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_14 = l_Lean_Meta_getIntValue_x3f(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Grind_getConfig___rarg(x_7, x_8, x_9, x_10, x_11, x_12, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*7 + 10);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = l_Lean_indentExpr(x_2);
x_28 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__2;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Meta_Grind_reportIssue(x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_dec(x_14);
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_15, 0);
lean_inc(x_2);
x_42 = l_Lean_Meta_Grind_isEqTrue(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_free_object(x_15);
lean_dec(x_41);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
lean_inc(x_2);
x_46 = l_Lean_Meta_Grind_isEqFalse(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
uint8_t x_49; 
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
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_46, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_46, 0, x_51);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_56 = l_Lean_Meta_Grind_mkEqFalseProof(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Meta_mkOfEqFalseCore(x_2, x_57);
x_60 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__7;
x_61 = l_Lean_reflBoolTrue;
x_62 = l_Lean_mkApp4(x_60, x_1, x_3, x_61, x_59);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Lean_Meta_Grind_pushNewFact(x_62, x_63, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_58);
return x_64;
}
else
{
uint8_t x_65; 
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
x_65 = !lean_is_exclusive(x_56);
if (x_65 == 0)
{
return x_56;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_56, 0);
x_67 = lean_ctor_get(x_56, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_56);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
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
x_69 = !lean_is_exclusive(x_46);
if (x_69 == 0)
{
return x_46;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_46, 0);
x_71 = lean_ctor_get(x_46, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_46);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_1);
x_73 = lean_ctor_get(x_42, 1);
lean_inc(x_73);
lean_dec(x_42);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_74 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_2);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_41);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 2, x_15);
x_78 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_77, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_76);
return x_78;
}
else
{
uint8_t x_79; 
lean_free_object(x_15);
lean_dec(x_41);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_74);
if (x_79 == 0)
{
return x_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_74, 0);
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_74);
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
lean_free_object(x_15);
lean_dec(x_41);
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
x_83 = !lean_is_exclusive(x_42);
if (x_83 == 0)
{
return x_42;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_42, 0);
x_85 = lean_ctor_get(x_42, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_42);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_15, 0);
lean_inc(x_87);
lean_dec(x_15);
lean_inc(x_2);
x_88 = l_Lean_Meta_Grind_isEqTrue(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_87);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
lean_inc(x_2);
x_92 = l_Lean_Meta_Grind_isEqFalse(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
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
x_97 = lean_box(0);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
lean_dec(x_92);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_100 = l_Lean_Meta_Grind_mkEqFalseProof(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Meta_mkOfEqFalseCore(x_2, x_101);
x_104 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__7;
x_105 = l_Lean_reflBoolTrue;
x_106 = l_Lean_mkApp4(x_104, x_1, x_3, x_105, x_103);
x_107 = lean_unsigned_to_nat(0u);
x_108 = l_Lean_Meta_Grind_pushNewFact(x_106, x_107, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_102);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
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
x_109 = lean_ctor_get(x_100, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_100, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_111 = x_100;
} else {
 lean_dec_ref(x_100);
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
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
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
x_113 = lean_ctor_get(x_92, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_92, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_115 = x_92;
} else {
 lean_dec_ref(x_92);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_1);
x_117 = lean_ctor_get(x_88, 1);
lean_inc(x_117);
lean_dec(x_88);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_118 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_2);
x_122 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_122, 0, x_87);
lean_ctor_set(x_122, 1, x_119);
lean_ctor_set(x_122, 2, x_121);
x_123 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_122, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_120);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_87);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_124 = lean_ctor_get(x_118, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_118, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_126 = x_118;
} else {
 lean_dec_ref(x_118);
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
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_87);
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
x_128 = lean_ctor_get(x_88, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_88, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_130 = x_88;
} else {
 lean_dec_ref(x_88);
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
}
}
else
{
uint8_t x_132; 
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
x_132 = !lean_is_exclusive(x_14);
if (x_132 == 0)
{
return x_14;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_14, 0);
x_134 = lean_ctor_get(x_14, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_14);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Meta_isInstDvdInt(x_2, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1(x_3, x_1, x_4, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_1, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_13);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Expr_appArg(x_15, lean_box(0));
x_19 = l_Lean_Expr_appFnCleanup(x_15, lean_box(0));
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
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
x_21 = lean_box(0);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Expr_appArg(x_19, lean_box(0));
x_23 = l_Lean_Expr_appFnCleanup(x_19, lean_box(0));
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_dec(x_22);
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
x_25 = lean_box(0);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l_Lean_Expr_appArg(x_23, lean_box(0));
x_27 = l_Lean_Expr_appFnCleanup(x_23, lean_box(0));
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
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
x_29 = lean_box(0);
lean_ctor_set(x_11, 0, x_29);
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Expr_appFnCleanup(x_27, lean_box(0));
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
x_32 = l_Lean_Expr_isConstOf(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_26);
lean_dec(x_22);
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
x_33 = lean_box(0);
lean_ctor_set(x_11, 0, x_33);
return x_11;
}
else
{
lean_object* x_34; 
lean_free_object(x_11);
x_34 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__2(x_1, x_26, x_22, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_34;
}
}
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_11, 0);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_11);
x_37 = l_Lean_Expr_cleanupAnnotations(x_35);
x_38 = l_Lean_Expr_isApp(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Lean_Expr_appArg(x_37, lean_box(0));
x_42 = l_Lean_Expr_appFnCleanup(x_37, lean_box(0));
x_43 = l_Lean_Expr_isApp(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = l_Lean_Expr_appArg(x_42, lean_box(0));
x_47 = l_Lean_Expr_appFnCleanup(x_42, lean_box(0));
x_48 = l_Lean_Expr_isApp(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_36);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = l_Lean_Expr_appArg(x_47, lean_box(0));
x_52 = l_Lean_Expr_appFnCleanup(x_47, lean_box(0));
x_53 = l_Lean_Expr_isApp(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_36);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_Expr_appFnCleanup(x_52, lean_box(0));
x_57 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
x_58 = l_Lean_Expr_isConstOf(x_56, x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_36);
return x_60;
}
else
{
lean_object* x_61; 
x_61 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__2(x_1, x_51, x_46, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
return x_61;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_pos_of_not_dvd", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_inc(x_1);
x_13 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_14);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__4;
x_18 = l_Lean_mkApp3(x_17, x_2, x_3, x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Meta_Grind_pushNewFact(x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_20;
}
else
{
uint8_t x_21; 
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
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Int_OfNat_toIntDvd_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_Meta_Grind_getGeneration(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_getForeignVars(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_22);
x_30 = l_Int_OfNat_Expr_denoteAsIntExpr(x_28, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_33 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_31, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Int_Linear_Expr_norm(x_34);
lean_inc(x_1);
x_37 = l_Lean_Meta_Grind_isEqTrue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_22);
lean_dec(x_21);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
lean_inc(x_1);
x_41 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_1, x_6, x_7, x_8, x_9, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = l_Lean_Expr_cleanupAnnotations(x_43);
x_46 = l_Lean_Expr_isApp(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_45);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_box(0);
lean_ctor_set(x_41, 0, x_47);
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = l_Lean_Expr_appArg(x_45, lean_box(0));
x_49 = l_Lean_Expr_appFnCleanup(x_45, lean_box(0));
x_50 = l_Lean_Expr_isApp(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_49);
lean_dec(x_48);
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
lean_ctor_set(x_41, 0, x_51);
return x_41;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = l_Lean_Expr_appArg(x_49, lean_box(0));
x_53 = l_Lean_Expr_appFnCleanup(x_49, lean_box(0));
x_54 = l_Lean_Expr_isApp(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_box(0);
lean_ctor_set(x_41, 0, x_55);
return x_41;
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Expr_appFnCleanup(x_53, lean_box(0));
x_57 = l_Lean_Expr_isApp(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_56);
lean_dec(x_52);
lean_dec(x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_box(0);
lean_ctor_set(x_41, 0, x_58);
return x_41;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = l_Lean_Expr_appFnCleanup(x_56, lean_box(0));
x_60 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
x_61 = l_Lean_Expr_isConstOf(x_59, x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_52);
lean_dec(x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_box(0);
lean_ctor_set(x_41, 0, x_62);
return x_41;
}
else
{
lean_object* x_63; 
lean_free_object(x_41);
x_63 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1(x_1, x_52, x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
return x_63;
}
}
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_41, 0);
x_65 = lean_ctor_get(x_41, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_41);
x_66 = l_Lean_Expr_cleanupAnnotations(x_64);
x_67 = l_Lean_Expr_isApp(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_66);
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
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = l_Lean_Expr_appArg(x_66, lean_box(0));
x_71 = l_Lean_Expr_appFnCleanup(x_66, lean_box(0));
x_72 = l_Lean_Expr_isApp(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_65);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = l_Lean_Expr_appArg(x_71, lean_box(0));
x_76 = l_Lean_Expr_appFnCleanup(x_71, lean_box(0));
x_77 = l_Lean_Expr_isApp(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_70);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_65);
return x_79;
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = l_Lean_Expr_appFnCleanup(x_76, lean_box(0));
x_81 = l_Lean_Expr_isApp(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_80);
lean_dec(x_75);
lean_dec(x_70);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_65);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = l_Lean_Expr_appFnCleanup(x_80, lean_box(0));
x_85 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
x_86 = l_Lean_Expr_isConstOf(x_84, x_85);
lean_dec(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_75);
lean_dec(x_70);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_65);
return x_88;
}
else
{
lean_object* x_89; 
x_89 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1(x_1, x_75, x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_65);
return x_89;
}
}
}
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_37, 1);
lean_inc(x_90);
lean_dec(x_37);
lean_inc(x_21);
x_91 = lean_nat_to_int(x_21);
x_92 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_21);
lean_ctor_set(x_92, 2, x_22);
lean_ctor_set(x_92, 3, x_34);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_36);
lean_ctor_set(x_93, 2, x_92);
x_94 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_93, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_90);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_37);
if (x_95 == 0)
{
return x_37;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_37, 0);
x_97 = lean_ctor_get(x_37, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_37);
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
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_33);
if (x_99 == 0)
{
return x_33;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_33, 0);
x_101 = lean_ctor_get(x_33, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_33);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_11);
if (x_103 == 0)
{
return x_11;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_11, 0);
x_105 = lean_ctor_get(x_11, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_11);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___lambda__1___closed__1;
x_13 = l_Lean_Expr_isConstOf(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_1, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_13);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_appFnCleanup(x_15, lean_box(0));
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
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
x_20 = lean_box(0);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Expr_appFnCleanup(x_18, lean_box(0));
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Expr_appFnCleanup(x_21, lean_box(0));
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
lean_ctor_set(x_11, 0, x_26);
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = l_Lean_Expr_appArg(x_24, lean_box(0));
x_28 = l_Lean_Expr_appFnCleanup(x_24, lean_box(0));
x_29 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
x_30 = l_Lean_Expr_isConstOf(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(0);
lean_ctor_set(x_11, 0, x_31);
return x_11;
}
else
{
lean_object* x_32; 
lean_free_object(x_11);
x_32 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___lambda__1(x_1, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_27);
return x_32;
}
}
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = l_Lean_Expr_cleanupAnnotations(x_33);
x_36 = l_Lean_Expr_isApp(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Expr_appFnCleanup(x_35, lean_box(0));
x_40 = l_Lean_Expr_isApp(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Expr_appFnCleanup(x_39, lean_box(0));
x_44 = l_Lean_Expr_isApp(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_34);
return x_46;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = l_Lean_Expr_appFnCleanup(x_43, lean_box(0));
x_48 = l_Lean_Expr_isApp(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_47);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_34);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = l_Lean_Expr_appArg(x_47, lean_box(0));
x_52 = l_Lean_Expr_appFnCleanup(x_47, lean_box(0));
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
x_54 = l_Lean_Expr_isConstOf(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_34);
return x_56;
}
else
{
lean_object* x_57; 
x_57 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___lambda__1(x_1, x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
lean_dec(x_51);
return x_57;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2579____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2579_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
x_3 = 0;
x_4 = l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2579____closed__1;
x_5 = l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin, lean_object* w) {
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
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__2);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__3);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__4);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__5);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___lambda__1___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___lambda__1___closed__1);
l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2579____closed__1 = _init_l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2579____closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2579____closed__1);
if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2579_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

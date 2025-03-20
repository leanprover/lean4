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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__8;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__3;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_gcdExt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__1;
lean_object* l_Lean_PersistentArray_set___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_3088____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__2;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__1;
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___boxed(lean_object**);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__2;
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__11___closed__1;
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__2;
uint8_t l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(uint8_t, uint8_t);
lean_object* l_Int_OfNat_toIntDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___closed__1;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
lean_object* l_Int_Linear_Expr_norm(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10___closed__1;
lean_object* l_Int_Linear_Poly_findVarToSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_3088_(lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__9;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10___closed__2;
lean_object* l_Int_Linear_Poly_norm(lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Int_OfNat_Expr_denoteAsIntExpr(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__4;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__4;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__3;
lean_object* l_Lean_Meta_Grind_getConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_1 = lean_mk_string_unchecked("cutsat", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
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
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4;
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
x_49 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
lean_ctor_set_tag(x_44, 7);
lean_ctor_set(x_44, 1, x_48);
lean_ctor_set(x_44, 0, x_49);
x_50 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8;
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
x_60 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8;
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
x_76 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(7, 2, 0);
} else {
 x_77 = x_74;
 lean_ctor_set_tag(x_77, 7);
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8;
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
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(7, 2, 0);
} else {
 x_98 = x_95;
 lean_ctor_set_tag(x_98, 7);
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8;
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
x_122 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_120)) {
 x_123 = lean_alloc_ctor(7, 2, 0);
} else {
 x_123 = x_120;
 lean_ctor_set_tag(x_123, 7);
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; 
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
x_23 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_24 = lean_ctor_get(x_8, 11);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
x_26 = lean_nat_dec_eq(x_15, x_16);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_8, 11);
lean_dec(x_28);
x_29 = lean_ctor_get(x_8, 10);
lean_dec(x_29);
x_30 = lean_ctor_get(x_8, 9);
lean_dec(x_30);
x_31 = lean_ctor_get(x_8, 8);
lean_dec(x_31);
x_32 = lean_ctor_get(x_8, 7);
lean_dec(x_32);
x_33 = lean_ctor_get(x_8, 6);
lean_dec(x_33);
x_34 = lean_ctor_get(x_8, 5);
lean_dec(x_34);
x_35 = lean_ctor_get(x_8, 4);
lean_dec(x_35);
x_36 = lean_ctor_get(x_8, 3);
lean_dec(x_36);
x_37 = lean_ctor_get(x_8, 2);
lean_dec(x_37);
x_38 = lean_ctor_get(x_8, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_8, 0);
lean_dec(x_39);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_15, x_40);
lean_dec(x_15);
lean_ctor_set(x_8, 3, x_41);
x_42 = l_Int_Linear_Poly_findVarToSubst(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec(x_8);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_42, 0);
lean_dec(x_45);
lean_ctor_set(x_42, 0, x_1);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_dec(x_42);
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = l_Int_Linear_Poly_coeff(x_54, x_52);
lean_dec(x_54);
x_56 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_55, x_52, x_53, x_51, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
lean_dec(x_51);
lean_dec(x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_1 = x_57;
x_10 = x_58;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_8);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_15, x_60);
lean_dec(x_15);
x_62 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_62, 0, x_12);
lean_ctor_set(x_62, 1, x_13);
lean_ctor_set(x_62, 2, x_14);
lean_ctor_set(x_62, 3, x_61);
lean_ctor_set(x_62, 4, x_16);
lean_ctor_set(x_62, 5, x_17);
lean_ctor_set(x_62, 6, x_18);
lean_ctor_set(x_62, 7, x_19);
lean_ctor_set(x_62, 8, x_20);
lean_ctor_set(x_62, 9, x_21);
lean_ctor_set(x_62, 10, x_22);
lean_ctor_set(x_62, 11, x_24);
lean_ctor_set_uint8(x_62, sizeof(void*)*12, x_23);
lean_ctor_set_uint8(x_62, sizeof(void*)*12 + 1, x_25);
x_63 = l_Int_Linear_Poly_findVarToSubst(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_62, x_9, x_10);
lean_dec(x_11);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_dec(x_63);
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = l_Int_Linear_Poly_coeff(x_74, x_72);
lean_dec(x_74);
x_76 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_75, x_72, x_73, x_71, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_62, x_9, x_70);
lean_dec(x_71);
lean_dec(x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_1 = x_77;
x_8 = x_62;
x_10 = x_78;
goto _start;
}
}
}
else
{
lean_object* x_80; 
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
x_80 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___spec__1(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_80;
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
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_18 = lean_ctor_get(x_17, 13);
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
x_22 = lean_ctor_get(x_17, 13);
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
x_26 = lean_ctor_get(x_19, 4);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = l_Lean_PersistentArray_set___rarg(x_26, x_3, x_27);
lean_ctor_set(x_19, 4, x_28);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
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
x_49 = lean_ctor_get_uint8(x_19, sizeof(void*)*16);
x_50 = lean_ctor_get(x_19, 13);
x_51 = lean_ctor_get(x_19, 14);
x_52 = lean_ctor_get(x_19, 15);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
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
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_2);
x_54 = l_Lean_PersistentArray_set___rarg(x_40, x_3, x_53);
x_55 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_55, 0, x_36);
lean_ctor_set(x_55, 1, x_37);
lean_ctor_set(x_55, 2, x_38);
lean_ctor_set(x_55, 3, x_39);
lean_ctor_set(x_55, 4, x_54);
lean_ctor_set(x_55, 5, x_41);
lean_ctor_set(x_55, 6, x_42);
lean_ctor_set(x_55, 7, x_43);
lean_ctor_set(x_55, 8, x_44);
lean_ctor_set(x_55, 9, x_45);
lean_ctor_set(x_55, 10, x_46);
lean_ctor_set(x_55, 11, x_47);
lean_ctor_set(x_55, 12, x_48);
lean_ctor_set(x_55, 13, x_50);
lean_ctor_set(x_55, 14, x_51);
lean_ctor_set(x_55, 15, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*16, x_49);
lean_ctor_set(x_18, 1, x_55);
x_56 = lean_st_ref_set(x_5, x_17, x_20);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_61 = lean_ctor_get(x_18, 0);
lean_inc(x_61);
lean_dec(x_18);
x_62 = lean_ctor_get(x_19, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_19, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_19, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_19, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_19, 5);
lean_inc(x_67);
x_68 = lean_ctor_get(x_19, 6);
lean_inc(x_68);
x_69 = lean_ctor_get(x_19, 7);
lean_inc(x_69);
x_70 = lean_ctor_get(x_19, 8);
lean_inc(x_70);
x_71 = lean_ctor_get(x_19, 9);
lean_inc(x_71);
x_72 = lean_ctor_get(x_19, 10);
lean_inc(x_72);
x_73 = lean_ctor_get(x_19, 11);
lean_inc(x_73);
x_74 = lean_ctor_get(x_19, 12);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_19, sizeof(void*)*16);
x_76 = lean_ctor_get(x_19, 13);
lean_inc(x_76);
x_77 = lean_ctor_get(x_19, 14);
lean_inc(x_77);
x_78 = lean_ctor_get(x_19, 15);
lean_inc(x_78);
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
 x_79 = x_19;
} else {
 lean_dec_ref(x_19);
 x_79 = lean_box(0);
}
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_2);
x_81 = l_Lean_PersistentArray_set___rarg(x_66, x_3, x_80);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 16, 1);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_62);
lean_ctor_set(x_82, 1, x_63);
lean_ctor_set(x_82, 2, x_64);
lean_ctor_set(x_82, 3, x_65);
lean_ctor_set(x_82, 4, x_81);
lean_ctor_set(x_82, 5, x_67);
lean_ctor_set(x_82, 6, x_68);
lean_ctor_set(x_82, 7, x_69);
lean_ctor_set(x_82, 8, x_70);
lean_ctor_set(x_82, 9, x_71);
lean_ctor_set(x_82, 10, x_72);
lean_ctor_set(x_82, 11, x_73);
lean_ctor_set(x_82, 12, x_74);
lean_ctor_set(x_82, 13, x_76);
lean_ctor_set(x_82, 14, x_77);
lean_ctor_set(x_82, 15, x_78);
lean_ctor_set_uint8(x_82, sizeof(void*)*16, x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_61);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_17, 13, x_83);
x_84 = lean_st_ref_set(x_5, x_17, x_20);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_89 = lean_ctor_get(x_17, 0);
x_90 = lean_ctor_get(x_17, 1);
x_91 = lean_ctor_get(x_17, 2);
x_92 = lean_ctor_get(x_17, 3);
x_93 = lean_ctor_get(x_17, 4);
x_94 = lean_ctor_get(x_17, 5);
x_95 = lean_ctor_get(x_17, 6);
x_96 = lean_ctor_get_uint8(x_17, sizeof(void*)*15);
x_97 = lean_ctor_get(x_17, 7);
x_98 = lean_ctor_get(x_17, 8);
x_99 = lean_ctor_get(x_17, 9);
x_100 = lean_ctor_get(x_17, 10);
x_101 = lean_ctor_get(x_17, 11);
x_102 = lean_ctor_get(x_17, 12);
x_103 = lean_ctor_get(x_17, 14);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_17);
x_104 = lean_ctor_get(x_18, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_105 = x_18;
} else {
 lean_dec_ref(x_18);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_19, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_19, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_19, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_19, 3);
lean_inc(x_109);
x_110 = lean_ctor_get(x_19, 4);
lean_inc(x_110);
x_111 = lean_ctor_get(x_19, 5);
lean_inc(x_111);
x_112 = lean_ctor_get(x_19, 6);
lean_inc(x_112);
x_113 = lean_ctor_get(x_19, 7);
lean_inc(x_113);
x_114 = lean_ctor_get(x_19, 8);
lean_inc(x_114);
x_115 = lean_ctor_get(x_19, 9);
lean_inc(x_115);
x_116 = lean_ctor_get(x_19, 10);
lean_inc(x_116);
x_117 = lean_ctor_get(x_19, 11);
lean_inc(x_117);
x_118 = lean_ctor_get(x_19, 12);
lean_inc(x_118);
x_119 = lean_ctor_get_uint8(x_19, sizeof(void*)*16);
x_120 = lean_ctor_get(x_19, 13);
lean_inc(x_120);
x_121 = lean_ctor_get(x_19, 14);
lean_inc(x_121);
x_122 = lean_ctor_get(x_19, 15);
lean_inc(x_122);
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
 x_123 = x_19;
} else {
 lean_dec_ref(x_19);
 x_123 = lean_box(0);
}
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_2);
x_125 = l_Lean_PersistentArray_set___rarg(x_110, x_3, x_124);
if (lean_is_scalar(x_123)) {
 x_126 = lean_alloc_ctor(0, 16, 1);
} else {
 x_126 = x_123;
}
lean_ctor_set(x_126, 0, x_106);
lean_ctor_set(x_126, 1, x_107);
lean_ctor_set(x_126, 2, x_108);
lean_ctor_set(x_126, 3, x_109);
lean_ctor_set(x_126, 4, x_125);
lean_ctor_set(x_126, 5, x_111);
lean_ctor_set(x_126, 6, x_112);
lean_ctor_set(x_126, 7, x_113);
lean_ctor_set(x_126, 8, x_114);
lean_ctor_set(x_126, 9, x_115);
lean_ctor_set(x_126, 10, x_116);
lean_ctor_set(x_126, 11, x_117);
lean_ctor_set(x_126, 12, x_118);
lean_ctor_set(x_126, 13, x_120);
lean_ctor_set(x_126, 14, x_121);
lean_ctor_set(x_126, 15, x_122);
lean_ctor_set_uint8(x_126, sizeof(void*)*16, x_119);
if (lean_is_scalar(x_105)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_105;
}
lean_ctor_set(x_127, 0, x_104);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_128, 0, x_89);
lean_ctor_set(x_128, 1, x_90);
lean_ctor_set(x_128, 2, x_91);
lean_ctor_set(x_128, 3, x_92);
lean_ctor_set(x_128, 4, x_93);
lean_ctor_set(x_128, 5, x_94);
lean_ctor_set(x_128, 6, x_95);
lean_ctor_set(x_128, 7, x_97);
lean_ctor_set(x_128, 8, x_98);
lean_ctor_set(x_128, 9, x_99);
lean_ctor_set(x_128, 10, x_100);
lean_ctor_set(x_128, 11, x_101);
lean_ctor_set(x_128, 12, x_102);
lean_ctor_set(x_128, 13, x_127);
lean_ctor_set(x_128, 14, x_103);
lean_ctor_set_uint8(x_128, sizeof(void*)*15, x_96);
x_129 = lean_st_ref_set(x_5, x_128, x_20);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
x_132 = lean_box(0);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
return x_133;
}
}
else
{
uint8_t x_134; 
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_14);
if (x_134 == 0)
{
return x_14;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_14, 0);
x_136 = lean_ctor_get(x_14, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_14);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("solve", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elim", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__2;
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_st_ref_take(x_11, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 13);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_21, 13);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_22, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_23, 4);
x_31 = lean_box(0);
x_32 = l_Lean_PersistentArray_set___rarg(x_30, x_1, x_31);
lean_ctor_set(x_23, 4, x_32);
x_33 = lean_st_ref_set(x_11, x_21, x_24);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_2, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Int_Linear_Poly_mul(x_3, x_4);
x_40 = lean_int_neg(x_5);
x_41 = l_Int_Linear_Poly_mul(x_6, x_40);
lean_dec(x_40);
x_42 = lean_unsigned_to_nat(100000000u);
x_43 = l_Int_Linear_Poly_combine_x27(x_42, x_39, x_41);
lean_ctor_set_tag(x_33, 5);
lean_ctor_set(x_33, 1, x_8);
lean_ctor_set(x_33, 0, x_7);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_33);
x_45 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__4;
x_46 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_45, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_38);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_44, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_49);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_46, 1);
x_53 = lean_ctor_get(x_46, 0);
lean_dec(x_53);
lean_inc(x_44);
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_44, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_52);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
x_58 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
lean_ctor_set_tag(x_54, 7);
lean_ctor_set(x_54, 1, x_56);
lean_ctor_set(x_54, 0, x_58);
lean_ctor_set_tag(x_46, 7);
lean_ctor_set(x_46, 1, x_58);
lean_ctor_set(x_46, 0, x_54);
x_59 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_45, x_46, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_57);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_44, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_60);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_54, 0);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_54);
x_64 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set_tag(x_46, 7);
lean_ctor_set(x_46, 1, x_64);
lean_ctor_set(x_46, 0, x_65);
x_66 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_45, x_46, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_63);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_44, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_46, 1);
lean_inc(x_69);
lean_dec(x_46);
lean_inc(x_44);
x_70 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_44, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_69);
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
x_74 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(7, 2, 0);
} else {
 x_75 = x_73;
 lean_ctor_set_tag(x_75, 7);
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_45, x_76, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_72);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_44, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_free_object(x_33);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
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
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_33, 1);
lean_inc(x_84);
lean_dec(x_33);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_85 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_2, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Int_Linear_Poly_mul(x_3, x_4);
x_88 = lean_int_neg(x_5);
x_89 = l_Int_Linear_Poly_mul(x_6, x_88);
lean_dec(x_88);
x_90 = lean_unsigned_to_nat(100000000u);
x_91 = l_Int_Linear_Poly_combine_x27(x_90, x_87, x_89);
x_92 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_92, 0, x_7);
lean_ctor_set(x_92, 1, x_8);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_9);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_92);
x_94 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__4;
x_95 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_94, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_86);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_93, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_98);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_101 = x_95;
} else {
 lean_dec_ref(x_95);
 x_101 = lean_box(0);
}
lean_inc(x_93);
x_102 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_93, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_100);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(7, 2, 0);
} else {
 x_107 = x_105;
 lean_ctor_set_tag(x_107, 7);
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_103);
if (lean_is_scalar(x_101)) {
 x_108 = lean_alloc_ctor(7, 2, 0);
} else {
 x_108 = x_101;
 lean_ctor_set_tag(x_108, 7);
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_94, x_108, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_104);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_93, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_110);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_112 = lean_ctor_get(x_85, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_85, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_114 = x_85;
} else {
 lean_dec_ref(x_85);
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
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_116 = lean_ctor_get(x_23, 0);
x_117 = lean_ctor_get(x_23, 1);
x_118 = lean_ctor_get(x_23, 2);
x_119 = lean_ctor_get(x_23, 3);
x_120 = lean_ctor_get(x_23, 4);
x_121 = lean_ctor_get(x_23, 5);
x_122 = lean_ctor_get(x_23, 6);
x_123 = lean_ctor_get(x_23, 7);
x_124 = lean_ctor_get(x_23, 8);
x_125 = lean_ctor_get(x_23, 9);
x_126 = lean_ctor_get(x_23, 10);
x_127 = lean_ctor_get(x_23, 11);
x_128 = lean_ctor_get(x_23, 12);
x_129 = lean_ctor_get_uint8(x_23, sizeof(void*)*16);
x_130 = lean_ctor_get(x_23, 13);
x_131 = lean_ctor_get(x_23, 14);
x_132 = lean_ctor_get(x_23, 15);
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
lean_dec(x_23);
x_133 = lean_box(0);
x_134 = l_Lean_PersistentArray_set___rarg(x_120, x_1, x_133);
x_135 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_135, 0, x_116);
lean_ctor_set(x_135, 1, x_117);
lean_ctor_set(x_135, 2, x_118);
lean_ctor_set(x_135, 3, x_119);
lean_ctor_set(x_135, 4, x_134);
lean_ctor_set(x_135, 5, x_121);
lean_ctor_set(x_135, 6, x_122);
lean_ctor_set(x_135, 7, x_123);
lean_ctor_set(x_135, 8, x_124);
lean_ctor_set(x_135, 9, x_125);
lean_ctor_set(x_135, 10, x_126);
lean_ctor_set(x_135, 11, x_127);
lean_ctor_set(x_135, 12, x_128);
lean_ctor_set(x_135, 13, x_130);
lean_ctor_set(x_135, 14, x_131);
lean_ctor_set(x_135, 15, x_132);
lean_ctor_set_uint8(x_135, sizeof(void*)*16, x_129);
lean_ctor_set(x_22, 1, x_135);
x_136 = lean_st_ref_set(x_11, x_21, x_24);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_139 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_2, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_137);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = l_Int_Linear_Poly_mul(x_3, x_4);
x_142 = lean_int_neg(x_5);
x_143 = l_Int_Linear_Poly_mul(x_6, x_142);
lean_dec(x_142);
x_144 = lean_unsigned_to_nat(100000000u);
x_145 = l_Int_Linear_Poly_combine_x27(x_144, x_141, x_143);
if (lean_is_scalar(x_138)) {
 x_146 = lean_alloc_ctor(5, 2, 0);
} else {
 x_146 = x_138;
 lean_ctor_set_tag(x_146, 5);
}
lean_ctor_set(x_146, 0, x_7);
lean_ctor_set(x_146, 1, x_8);
x_147 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_147, 0, x_9);
lean_ctor_set(x_147, 1, x_145);
lean_ctor_set(x_147, 2, x_146);
x_148 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__4;
x_149 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_148, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_140);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_unbox(x_150);
lean_dec(x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_147, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_152);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_154 = lean_ctor_get(x_149, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_155 = x_149;
} else {
 lean_dec_ref(x_149);
 x_155 = lean_box(0);
}
lean_inc(x_147);
x_156 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_147, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_154);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(7, 2, 0);
} else {
 x_161 = x_159;
 lean_ctor_set_tag(x_161, 7);
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_157);
if (lean_is_scalar(x_155)) {
 x_162 = lean_alloc_ctor(7, 2, 0);
} else {
 x_162 = x_155;
 lean_ctor_set_tag(x_162, 7);
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_148, x_162, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_158);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_147, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_164);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_138);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_166 = lean_ctor_get(x_139, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_139, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_168 = x_139;
} else {
 lean_dec_ref(x_139);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_170 = lean_ctor_get(x_22, 0);
lean_inc(x_170);
lean_dec(x_22);
x_171 = lean_ctor_get(x_23, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_23, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_23, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_23, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_23, 4);
lean_inc(x_175);
x_176 = lean_ctor_get(x_23, 5);
lean_inc(x_176);
x_177 = lean_ctor_get(x_23, 6);
lean_inc(x_177);
x_178 = lean_ctor_get(x_23, 7);
lean_inc(x_178);
x_179 = lean_ctor_get(x_23, 8);
lean_inc(x_179);
x_180 = lean_ctor_get(x_23, 9);
lean_inc(x_180);
x_181 = lean_ctor_get(x_23, 10);
lean_inc(x_181);
x_182 = lean_ctor_get(x_23, 11);
lean_inc(x_182);
x_183 = lean_ctor_get(x_23, 12);
lean_inc(x_183);
x_184 = lean_ctor_get_uint8(x_23, sizeof(void*)*16);
x_185 = lean_ctor_get(x_23, 13);
lean_inc(x_185);
x_186 = lean_ctor_get(x_23, 14);
lean_inc(x_186);
x_187 = lean_ctor_get(x_23, 15);
lean_inc(x_187);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 lean_ctor_release(x_23, 5);
 lean_ctor_release(x_23, 6);
 lean_ctor_release(x_23, 7);
 lean_ctor_release(x_23, 8);
 lean_ctor_release(x_23, 9);
 lean_ctor_release(x_23, 10);
 lean_ctor_release(x_23, 11);
 lean_ctor_release(x_23, 12);
 lean_ctor_release(x_23, 13);
 lean_ctor_release(x_23, 14);
 lean_ctor_release(x_23, 15);
 x_188 = x_23;
} else {
 lean_dec_ref(x_23);
 x_188 = lean_box(0);
}
x_189 = lean_box(0);
x_190 = l_Lean_PersistentArray_set___rarg(x_175, x_1, x_189);
if (lean_is_scalar(x_188)) {
 x_191 = lean_alloc_ctor(0, 16, 1);
} else {
 x_191 = x_188;
}
lean_ctor_set(x_191, 0, x_171);
lean_ctor_set(x_191, 1, x_172);
lean_ctor_set(x_191, 2, x_173);
lean_ctor_set(x_191, 3, x_174);
lean_ctor_set(x_191, 4, x_190);
lean_ctor_set(x_191, 5, x_176);
lean_ctor_set(x_191, 6, x_177);
lean_ctor_set(x_191, 7, x_178);
lean_ctor_set(x_191, 8, x_179);
lean_ctor_set(x_191, 9, x_180);
lean_ctor_set(x_191, 10, x_181);
lean_ctor_set(x_191, 11, x_182);
lean_ctor_set(x_191, 12, x_183);
lean_ctor_set(x_191, 13, x_185);
lean_ctor_set(x_191, 14, x_186);
lean_ctor_set(x_191, 15, x_187);
lean_ctor_set_uint8(x_191, sizeof(void*)*16, x_184);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_170);
lean_ctor_set(x_192, 1, x_191);
lean_ctor_set(x_21, 13, x_192);
x_193 = lean_st_ref_set(x_11, x_21, x_24);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_195 = x_193;
} else {
 lean_dec_ref(x_193);
 x_195 = lean_box(0);
}
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_196 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_2, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_194);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_198 = l_Int_Linear_Poly_mul(x_3, x_4);
x_199 = lean_int_neg(x_5);
x_200 = l_Int_Linear_Poly_mul(x_6, x_199);
lean_dec(x_199);
x_201 = lean_unsigned_to_nat(100000000u);
x_202 = l_Int_Linear_Poly_combine_x27(x_201, x_198, x_200);
if (lean_is_scalar(x_195)) {
 x_203 = lean_alloc_ctor(5, 2, 0);
} else {
 x_203 = x_195;
 lean_ctor_set_tag(x_203, 5);
}
lean_ctor_set(x_203, 0, x_7);
lean_ctor_set(x_203, 1, x_8);
x_204 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_204, 0, x_9);
lean_ctor_set(x_204, 1, x_202);
lean_ctor_set(x_204, 2, x_203);
x_205 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__4;
x_206 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_205, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_197);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_unbox(x_207);
lean_dec(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
lean_dec(x_206);
x_210 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_204, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_209);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_211 = lean_ctor_get(x_206, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_212 = x_206;
} else {
 lean_dec_ref(x_206);
 x_212 = lean_box(0);
}
lean_inc(x_204);
x_213 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_204, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_211);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_216 = x_213;
} else {
 lean_dec_ref(x_213);
 x_216 = lean_box(0);
}
x_217 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_216)) {
 x_218 = lean_alloc_ctor(7, 2, 0);
} else {
 x_218 = x_216;
 lean_ctor_set_tag(x_218, 7);
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_214);
if (lean_is_scalar(x_212)) {
 x_219 = lean_alloc_ctor(7, 2, 0);
} else {
 x_219 = x_212;
 lean_ctor_set_tag(x_219, 7);
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
x_220 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_205, x_219, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_215);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_204, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_221);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_195);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_223 = lean_ctor_get(x_196, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_196, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_225 = x_196;
} else {
 lean_dec_ref(x_196);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_227 = lean_ctor_get(x_21, 0);
x_228 = lean_ctor_get(x_21, 1);
x_229 = lean_ctor_get(x_21, 2);
x_230 = lean_ctor_get(x_21, 3);
x_231 = lean_ctor_get(x_21, 4);
x_232 = lean_ctor_get(x_21, 5);
x_233 = lean_ctor_get(x_21, 6);
x_234 = lean_ctor_get_uint8(x_21, sizeof(void*)*15);
x_235 = lean_ctor_get(x_21, 7);
x_236 = lean_ctor_get(x_21, 8);
x_237 = lean_ctor_get(x_21, 9);
x_238 = lean_ctor_get(x_21, 10);
x_239 = lean_ctor_get(x_21, 11);
x_240 = lean_ctor_get(x_21, 12);
x_241 = lean_ctor_get(x_21, 14);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_21);
x_242 = lean_ctor_get(x_22, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_243 = x_22;
} else {
 lean_dec_ref(x_22);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_23, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_23, 1);
lean_inc(x_245);
x_246 = lean_ctor_get(x_23, 2);
lean_inc(x_246);
x_247 = lean_ctor_get(x_23, 3);
lean_inc(x_247);
x_248 = lean_ctor_get(x_23, 4);
lean_inc(x_248);
x_249 = lean_ctor_get(x_23, 5);
lean_inc(x_249);
x_250 = lean_ctor_get(x_23, 6);
lean_inc(x_250);
x_251 = lean_ctor_get(x_23, 7);
lean_inc(x_251);
x_252 = lean_ctor_get(x_23, 8);
lean_inc(x_252);
x_253 = lean_ctor_get(x_23, 9);
lean_inc(x_253);
x_254 = lean_ctor_get(x_23, 10);
lean_inc(x_254);
x_255 = lean_ctor_get(x_23, 11);
lean_inc(x_255);
x_256 = lean_ctor_get(x_23, 12);
lean_inc(x_256);
x_257 = lean_ctor_get_uint8(x_23, sizeof(void*)*16);
x_258 = lean_ctor_get(x_23, 13);
lean_inc(x_258);
x_259 = lean_ctor_get(x_23, 14);
lean_inc(x_259);
x_260 = lean_ctor_get(x_23, 15);
lean_inc(x_260);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 lean_ctor_release(x_23, 5);
 lean_ctor_release(x_23, 6);
 lean_ctor_release(x_23, 7);
 lean_ctor_release(x_23, 8);
 lean_ctor_release(x_23, 9);
 lean_ctor_release(x_23, 10);
 lean_ctor_release(x_23, 11);
 lean_ctor_release(x_23, 12);
 lean_ctor_release(x_23, 13);
 lean_ctor_release(x_23, 14);
 lean_ctor_release(x_23, 15);
 x_261 = x_23;
} else {
 lean_dec_ref(x_23);
 x_261 = lean_box(0);
}
x_262 = lean_box(0);
x_263 = l_Lean_PersistentArray_set___rarg(x_248, x_1, x_262);
if (lean_is_scalar(x_261)) {
 x_264 = lean_alloc_ctor(0, 16, 1);
} else {
 x_264 = x_261;
}
lean_ctor_set(x_264, 0, x_244);
lean_ctor_set(x_264, 1, x_245);
lean_ctor_set(x_264, 2, x_246);
lean_ctor_set(x_264, 3, x_247);
lean_ctor_set(x_264, 4, x_263);
lean_ctor_set(x_264, 5, x_249);
lean_ctor_set(x_264, 6, x_250);
lean_ctor_set(x_264, 7, x_251);
lean_ctor_set(x_264, 8, x_252);
lean_ctor_set(x_264, 9, x_253);
lean_ctor_set(x_264, 10, x_254);
lean_ctor_set(x_264, 11, x_255);
lean_ctor_set(x_264, 12, x_256);
lean_ctor_set(x_264, 13, x_258);
lean_ctor_set(x_264, 14, x_259);
lean_ctor_set(x_264, 15, x_260);
lean_ctor_set_uint8(x_264, sizeof(void*)*16, x_257);
if (lean_is_scalar(x_243)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_243;
}
lean_ctor_set(x_265, 0, x_242);
lean_ctor_set(x_265, 1, x_264);
x_266 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_266, 0, x_227);
lean_ctor_set(x_266, 1, x_228);
lean_ctor_set(x_266, 2, x_229);
lean_ctor_set(x_266, 3, x_230);
lean_ctor_set(x_266, 4, x_231);
lean_ctor_set(x_266, 5, x_232);
lean_ctor_set(x_266, 6, x_233);
lean_ctor_set(x_266, 7, x_235);
lean_ctor_set(x_266, 8, x_236);
lean_ctor_set(x_266, 9, x_237);
lean_ctor_set(x_266, 10, x_238);
lean_ctor_set(x_266, 11, x_239);
lean_ctor_set(x_266, 12, x_240);
lean_ctor_set(x_266, 13, x_265);
lean_ctor_set(x_266, 14, x_241);
lean_ctor_set_uint8(x_266, sizeof(void*)*15, x_234);
x_267 = lean_st_ref_set(x_11, x_266, x_24);
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_269 = x_267;
} else {
 lean_dec_ref(x_267);
 x_269 = lean_box(0);
}
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_270 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_2, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_268);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
lean_dec(x_270);
x_272 = l_Int_Linear_Poly_mul(x_3, x_4);
x_273 = lean_int_neg(x_5);
x_274 = l_Int_Linear_Poly_mul(x_6, x_273);
lean_dec(x_273);
x_275 = lean_unsigned_to_nat(100000000u);
x_276 = l_Int_Linear_Poly_combine_x27(x_275, x_272, x_274);
if (lean_is_scalar(x_269)) {
 x_277 = lean_alloc_ctor(5, 2, 0);
} else {
 x_277 = x_269;
 lean_ctor_set_tag(x_277, 5);
}
lean_ctor_set(x_277, 0, x_7);
lean_ctor_set(x_277, 1, x_8);
x_278 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_278, 0, x_9);
lean_ctor_set(x_278, 1, x_276);
lean_ctor_set(x_278, 2, x_277);
x_279 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__4;
x_280 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_279, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_271);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_unbox(x_281);
lean_dec(x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_dec(x_280);
x_284 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_278, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_283);
return x_284;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_285 = lean_ctor_get(x_280, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_286 = x_280;
} else {
 lean_dec_ref(x_280);
 x_286 = lean_box(0);
}
lean_inc(x_278);
x_287 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_278, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_285);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_290 = x_287;
} else {
 lean_dec_ref(x_287);
 x_290 = lean_box(0);
}
x_291 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_290)) {
 x_292 = lean_alloc_ctor(7, 2, 0);
} else {
 x_292 = x_290;
 lean_ctor_set_tag(x_292, 7);
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_288);
if (lean_is_scalar(x_286)) {
 x_293 = lean_alloc_ctor(7, 2, 0);
} else {
 x_293 = x_286;
 lean_ctor_set_tag(x_293, 7);
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
x_294 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_279, x_293, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_289);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_278, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_295);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_269);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_297 = lean_ctor_get(x_270, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_270, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_299 = x_270;
} else {
 lean_dec_ref(x_270);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("combine", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__2;
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___rarg(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 2);
x_22 = lean_ctor_get(x_17, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_int_mul(x_2, x_23);
x_25 = lean_int_mul(x_20, x_3);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_gcdExt(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
x_32 = lean_int_mul(x_30, x_23);
lean_dec(x_30);
lean_inc(x_4);
x_33 = l_Int_Linear_Poly_mul(x_4, x_32);
lean_dec(x_32);
x_34 = lean_int_mul(x_31, x_3);
lean_dec(x_31);
lean_inc(x_21);
x_35 = l_Int_Linear_Poly_mul(x_21, x_34);
lean_dec(x_34);
x_36 = lean_int_mul(x_3, x_23);
lean_dec(x_23);
x_37 = lean_unsigned_to_nat(100000000u);
x_38 = l_Int_Linear_Poly_combine_x27(x_37, x_33, x_35);
lean_inc(x_5);
lean_inc(x_28);
lean_ctor_set(x_17, 2, x_38);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 0, x_28);
lean_inc(x_1);
lean_inc(x_6);
lean_ctor_set_tag(x_27, 4);
lean_ctor_set(x_27, 1, x_1);
lean_ctor_set(x_27, 0, x_6);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_17);
lean_ctor_set(x_39, 2, x_27);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___closed__2;
x_41 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_40, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_box(0);
x_46 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(x_5, x_39, x_4, x_20, x_2, x_21, x_6, x_1, x_28, x_45, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_44);
lean_dec(x_20);
lean_dec(x_5);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_41);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_41, 1);
x_49 = lean_ctor_get(x_41, 0);
lean_dec(x_49);
lean_inc(x_39);
x_50 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_39, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_48);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
lean_ctor_set_tag(x_50, 7);
lean_ctor_set(x_50, 1, x_52);
lean_ctor_set(x_50, 0, x_54);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_54);
lean_ctor_set(x_41, 0, x_50);
x_55 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_40, x_41, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_53);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(x_5, x_39, x_4, x_20, x_2, x_21, x_6, x_1, x_28, x_56, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_57);
lean_dec(x_56);
lean_dec(x_20);
lean_dec(x_5);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_50, 0);
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_50);
x_61 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_61);
lean_ctor_set(x_41, 0, x_62);
x_63 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_40, x_41, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_60);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(x_5, x_39, x_4, x_20, x_2, x_21, x_6, x_1, x_28, x_64, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_65);
lean_dec(x_64);
lean_dec(x_20);
lean_dec(x_5);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_67 = lean_ctor_get(x_41, 1);
lean_inc(x_67);
lean_dec(x_41);
lean_inc(x_39);
x_68 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_39, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(7, 2, 0);
} else {
 x_73 = x_71;
 lean_ctor_set_tag(x_73, 7);
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_40, x_74, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_70);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(x_5, x_39, x_4, x_20, x_2, x_21, x_6, x_1, x_28, x_76, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_77);
lean_dec(x_76);
lean_dec(x_20);
lean_dec(x_5);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_79 = lean_ctor_get(x_27, 0);
x_80 = lean_ctor_get(x_27, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_27);
x_81 = lean_int_mul(x_79, x_23);
lean_dec(x_79);
lean_inc(x_4);
x_82 = l_Int_Linear_Poly_mul(x_4, x_81);
lean_dec(x_81);
x_83 = lean_int_mul(x_80, x_3);
lean_dec(x_80);
lean_inc(x_21);
x_84 = l_Int_Linear_Poly_mul(x_21, x_83);
lean_dec(x_83);
x_85 = lean_int_mul(x_3, x_23);
lean_dec(x_23);
x_86 = lean_unsigned_to_nat(100000000u);
x_87 = l_Int_Linear_Poly_combine_x27(x_86, x_82, x_84);
lean_inc(x_5);
lean_inc(x_28);
lean_ctor_set(x_17, 2, x_87);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 0, x_28);
lean_inc(x_1);
lean_inc(x_6);
x_88 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_88, 0, x_6);
lean_ctor_set(x_88, 1, x_1);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_17);
lean_ctor_set(x_89, 2, x_88);
x_90 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___closed__2;
x_91 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_90, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_box(0);
x_96 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(x_5, x_89, x_4, x_20, x_2, x_21, x_6, x_1, x_28, x_95, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_94);
lean_dec(x_20);
lean_dec(x_5);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_98 = x_91;
} else {
 lean_dec_ref(x_91);
 x_98 = lean_box(0);
}
lean_inc(x_89);
x_99 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_89, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_97);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
x_103 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(7, 2, 0);
} else {
 x_104 = x_102;
 lean_ctor_set_tag(x_104, 7);
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_100);
if (lean_is_scalar(x_98)) {
 x_105 = lean_alloc_ctor(7, 2, 0);
} else {
 x_105 = x_98;
 lean_ctor_set_tag(x_105, 7);
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_90, x_105, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_101);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(x_5, x_89, x_4, x_20, x_2, x_21, x_6, x_1, x_28, x_107, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_108);
lean_dec(x_107);
lean_dec(x_20);
lean_dec(x_5);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_110 = lean_ctor_get(x_17, 0);
x_111 = lean_ctor_get(x_17, 2);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_17);
x_112 = lean_ctor_get(x_1, 0);
lean_inc(x_112);
x_113 = lean_int_mul(x_2, x_112);
x_114 = lean_int_mul(x_110, x_3);
x_115 = l_Lean_Meta_Grind_Arith_Cutsat_gcdExt(x_113, x_114);
lean_dec(x_114);
lean_dec(x_113);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_120 = x_116;
} else {
 lean_dec_ref(x_116);
 x_120 = lean_box(0);
}
x_121 = lean_int_mul(x_118, x_112);
lean_dec(x_118);
lean_inc(x_4);
x_122 = l_Int_Linear_Poly_mul(x_4, x_121);
lean_dec(x_121);
x_123 = lean_int_mul(x_119, x_3);
lean_dec(x_119);
lean_inc(x_111);
x_124 = l_Int_Linear_Poly_mul(x_111, x_123);
lean_dec(x_123);
x_125 = lean_int_mul(x_3, x_112);
lean_dec(x_112);
x_126 = lean_unsigned_to_nat(100000000u);
x_127 = l_Int_Linear_Poly_combine_x27(x_126, x_122, x_124);
lean_inc(x_5);
lean_inc(x_117);
x_128 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_128, 0, x_117);
lean_ctor_set(x_128, 1, x_5);
lean_ctor_set(x_128, 2, x_127);
lean_inc(x_1);
lean_inc(x_6);
if (lean_is_scalar(x_120)) {
 x_129 = lean_alloc_ctor(4, 2, 0);
} else {
 x_129 = x_120;
 lean_ctor_set_tag(x_129, 4);
}
lean_ctor_set(x_129, 0, x_6);
lean_ctor_set(x_129, 1, x_1);
x_130 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_128);
lean_ctor_set(x_130, 2, x_129);
x_131 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___closed__2;
x_132 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_131, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
x_136 = lean_box(0);
x_137 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(x_5, x_130, x_4, x_110, x_2, x_111, x_6, x_1, x_117, x_136, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_135);
lean_dec(x_110);
lean_dec(x_5);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_139 = x_132;
} else {
 lean_dec_ref(x_132);
 x_139 = lean_box(0);
}
lean_inc(x_130);
x_140 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_130, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_138);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
x_144 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(7, 2, 0);
} else {
 x_145 = x_143;
 lean_ctor_set_tag(x_145, 7);
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_141);
if (lean_is_scalar(x_139)) {
 x_146 = lean_alloc_ctor(7, 2, 0);
} else {
 x_146 = x_139;
 lean_ctor_set_tag(x_146, 7);
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_131, x_146, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_142);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(x_5, x_130, x_4, x_110, x_2, x_111, x_6, x_1, x_117, x_148, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_149);
lean_dec(x_148);
lean_dec(x_110);
lean_dec(x_5);
return x_150;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("update", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_62; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
x_133 = lean_box(0);
x_134 = lean_ctor_get(x_18, 4);
lean_inc(x_134);
lean_dec(x_18);
x_135 = lean_ctor_get(x_134, 2);
lean_inc(x_135);
x_136 = lean_nat_dec_lt(x_3, x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
lean_dec(x_134);
x_137 = l_outOfBounds___rarg(x_133);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
lean_dec(x_20);
lean_dec(x_6);
x_138 = lean_box(0);
x_21 = x_138;
goto block_61;
}
else
{
lean_object* x_139; 
lean_dec(x_1);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_62 = x_139;
goto block_132;
}
}
else
{
lean_object* x_140; 
x_140 = l_Lean_PersistentArray_get_x21___rarg(x_133, x_134, x_3);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
lean_dec(x_20);
lean_dec(x_6);
x_141 = lean_box(0);
x_21 = x_141;
goto block_61;
}
else
{
lean_object* x_142; 
lean_dec(x_1);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec(x_140);
x_62 = x_142;
goto block_132;
}
}
block_61:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_21);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__2;
x_23 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1(x_1, x_2, x_3, x_27, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_23, 1);
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
lean_inc(x_2);
x_32 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_30);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_34);
lean_ctor_set(x_32, 0, x_36);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_36);
lean_ctor_set(x_23, 0, x_32);
x_37 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_22, x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1(x_1, x_2, x_3, x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_39);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_38);
lean_dec(x_3);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_43);
lean_ctor_set(x_23, 0, x_44);
x_45 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_22, x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1(x_1, x_2, x_3, x_46, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_47);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_46);
lean_dec(x_3);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_23, 1);
lean_inc(x_49);
lean_dec(x_23);
lean_inc(x_2);
x_50 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(7, 2, 0);
} else {
 x_55 = x_53;
 lean_ctor_set_tag(x_55, 7);
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_22, x_56, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_52);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__1(x_1, x_2, x_3, x_58, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_59);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_58);
lean_dec(x_3);
return x_60;
}
}
}
block_132:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__3;
x_64 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_63, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_20);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_box(0);
x_69 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4(x_62, x_4, x_5, x_6, x_3, x_2, x_68, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_67);
return x_69;
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_64);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_64, 1);
x_72 = lean_ctor_get(x_64, 0);
lean_dec(x_72);
lean_inc(x_2);
x_73 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_71);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_62);
x_77 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_62, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_76);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
x_81 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
lean_ctor_set_tag(x_77, 7);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 0, x_81);
x_82 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8;
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_82);
lean_ctor_set(x_73, 0, x_77);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_79);
lean_ctor_set(x_64, 0, x_73);
if (lean_is_scalar(x_20)) {
 x_83 = lean_alloc_ctor(7, 2, 0);
} else {
 x_83 = x_20;
 lean_ctor_set_tag(x_83, 7);
}
lean_ctor_set(x_83, 0, x_64);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_63, x_83, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_80);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4(x_62, x_4, x_5, x_6, x_3, x_2, x_85, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_86);
lean_dec(x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_88 = lean_ctor_get(x_77, 0);
x_89 = lean_ctor_get(x_77, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_77);
x_90 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_75);
x_92 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8;
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_92);
lean_ctor_set(x_73, 0, x_91);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_88);
lean_ctor_set(x_64, 0, x_73);
if (lean_is_scalar(x_20)) {
 x_93 = lean_alloc_ctor(7, 2, 0);
} else {
 x_93 = x_20;
 lean_ctor_set_tag(x_93, 7);
}
lean_ctor_set(x_93, 0, x_64);
lean_ctor_set(x_93, 1, x_90);
x_94 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_63, x_93, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_89);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4(x_62, x_4, x_5, x_6, x_3, x_2, x_95, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_96);
lean_dec(x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_98 = lean_ctor_get(x_73, 0);
x_99 = lean_ctor_get(x_73, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_73);
lean_inc(x_62);
x_100 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_62, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_99);
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
x_104 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(7, 2, 0);
} else {
 x_105 = x_103;
 lean_ctor_set_tag(x_105, 7);
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_98);
x_106 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8;
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_101);
lean_ctor_set(x_64, 0, x_107);
if (lean_is_scalar(x_20)) {
 x_108 = lean_alloc_ctor(7, 2, 0);
} else {
 x_108 = x_20;
 lean_ctor_set_tag(x_108, 7);
}
lean_ctor_set(x_108, 0, x_64);
lean_ctor_set(x_108, 1, x_104);
x_109 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_63, x_108, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_102);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4(x_62, x_4, x_5, x_6, x_3, x_2, x_110, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_111);
lean_dec(x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_113 = lean_ctor_get(x_64, 1);
lean_inc(x_113);
lean_dec(x_64);
lean_inc(x_2);
x_114 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
lean_inc(x_62);
x_118 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_62, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_116);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(7, 2, 0);
} else {
 x_123 = x_121;
 lean_ctor_set_tag(x_123, 7);
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_115);
x_124 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8;
if (lean_is_scalar(x_117)) {
 x_125 = lean_alloc_ctor(7, 2, 0);
} else {
 x_125 = x_117;
 lean_ctor_set_tag(x_125, 7);
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_119);
if (lean_is_scalar(x_20)) {
 x_127 = lean_alloc_ctor(7, 2, 0);
} else {
 x_127 = x_20;
 lean_ctor_set_tag(x_127, 7);
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_122);
x_128 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_63, x_127, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_120);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4(x_62, x_4, x_5, x_6, x_3, x_2, x_129, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_130);
lean_dec(x_129);
return x_131;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5(x_12, x_1, x_15, x_14, x_17, x_16, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
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
x_29 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5(x_12, x_1, x_15, x_14, x_17, x_16, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_14);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__6(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__2;
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__3;
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
x_28 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
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
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
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
x_43 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__3;
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
x_51 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8(x_14, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10___closed__2;
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
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__9(x_14, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
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
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
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
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__9(x_14, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
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
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
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
x_47 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__9(x_14, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
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
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
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
x_59 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__9(x_14, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__11___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__11___closed__1;
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
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
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
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
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
x_30 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10(x_1, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
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
x_33 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
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
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10(x_1, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
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
x_44 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
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
x_50 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10(x_1, x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
lean_dec(x_48);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
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
x_22 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_23 = lean_ctor_get(x_8, 11);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
x_25 = lean_nat_dec_eq(x_14, x_15);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_27 = lean_ctor_get(x_8, 11);
lean_dec(x_27);
x_28 = lean_ctor_get(x_8, 10);
lean_dec(x_28);
x_29 = lean_ctor_get(x_8, 9);
lean_dec(x_29);
x_30 = lean_ctor_get(x_8, 8);
lean_dec(x_30);
x_31 = lean_ctor_get(x_8, 7);
lean_dec(x_31);
x_32 = lean_ctor_get(x_8, 6);
lean_dec(x_32);
x_33 = lean_ctor_get(x_8, 5);
lean_dec(x_33);
x_34 = lean_ctor_get(x_8, 4);
lean_dec(x_34);
x_35 = lean_ctor_get(x_8, 3);
lean_dec(x_35);
x_36 = lean_ctor_get(x_8, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_8, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_8, 0);
lean_dec(x_38);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_14, x_39);
lean_dec(x_14);
lean_ctor_set(x_8, 3, x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_box(0);
x_46 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__11(x_1, x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_41);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_41, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_41, 0, x_49);
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_8);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_14, x_57);
lean_dec(x_14);
x_59 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_59, 0, x_11);
lean_ctor_set(x_59, 1, x_12);
lean_ctor_set(x_59, 2, x_13);
lean_ctor_set(x_59, 3, x_58);
lean_ctor_set(x_59, 4, x_15);
lean_ctor_set(x_59, 5, x_16);
lean_ctor_set(x_59, 6, x_17);
lean_ctor_set(x_59, 7, x_18);
lean_ctor_set(x_59, 8, x_19);
lean_ctor_set(x_59, 9, x_20);
lean_ctor_set(x_59, 10, x_21);
lean_ctor_set(x_59, 11, x_23);
lean_ctor_set_uint8(x_59, sizeof(void*)*12, x_22);
lean_ctor_set_uint8(x_59, sizeof(void*)*12 + 1, x_24);
lean_inc(x_9);
lean_inc(x_59);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_60 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(x_2, x_3, x_4, x_5, x_6, x_7, x_59, x_9, x_10);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_box(0);
x_65 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__11(x_1, x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_59, x_9, x_63);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_59);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_68 = lean_box(0);
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
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_59);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_ctor_get(x_60, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_60, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_72 = x_60;
} else {
 lean_dec_ref(x_60);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; 
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
x_74 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___spec__1(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_74;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___boxed(lean_object** _args) {
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
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__8;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
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
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 6);
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
x_30 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
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
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
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
x_78 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__9;
x_79 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_78, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_76);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_77, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_82);
return x_83;
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_79, 1);
x_86 = lean_ctor_get(x_79, 0);
lean_dec(x_86);
lean_inc(x_77);
x_87 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_77, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_85);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_ctor_get(x_87, 1);
x_91 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
lean_ctor_set_tag(x_87, 7);
lean_ctor_set(x_87, 1, x_89);
lean_ctor_set(x_87, 0, x_91);
lean_ctor_set_tag(x_79, 7);
lean_ctor_set(x_79, 1, x_91);
lean_ctor_set(x_79, 0, x_87);
x_92 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_78, x_79, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_90);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_77, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_93);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_87, 0);
x_96 = lean_ctor_get(x_87, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_87);
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set_tag(x_79, 7);
lean_ctor_set(x_79, 1, x_97);
lean_ctor_set(x_79, 0, x_98);
x_99 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_78, x_79, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_96);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_77, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_100);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_102 = lean_ctor_get(x_79, 1);
lean_inc(x_102);
lean_dec(x_79);
lean_inc(x_77);
x_103 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_77, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_102);
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
x_107 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(7, 2, 0);
} else {
 x_108 = x_106;
 lean_ctor_set_tag(x_108, 7);
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_104);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_78, x_109, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_105);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_77, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
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
x_113 = !lean_is_exclusive(x_74);
if (x_113 == 0)
{
return x_74;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_74, 0);
x_115 = lean_ctor_get(x_74, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_74);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
else
{
uint8_t x_117; 
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
x_117 = !lean_is_exclusive(x_42);
if (x_117 == 0)
{
return x_42;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_42, 0);
x_119 = lean_ctor_get(x_42, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_42);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_15, 0);
lean_inc(x_121);
lean_dec(x_15);
lean_inc(x_2);
x_122 = l_Lean_Meta_Grind_isEqTrue(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_unbox(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_121);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
lean_inc(x_2);
x_126 = l_Lean_Meta_Grind_isEqFalse(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
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
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_130 = x_126;
} else {
 lean_dec_ref(x_126);
 x_130 = lean_box(0);
}
x_131 = lean_box(0);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_126, 1);
lean_inc(x_133);
lean_dec(x_126);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_134 = l_Lean_Meta_Grind_mkEqFalseProof(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_Meta_mkOfEqFalseCore(x_2, x_135);
x_138 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__7;
x_139 = l_Lean_reflBoolTrue;
x_140 = l_Lean_mkApp4(x_138, x_1, x_3, x_139, x_137);
x_141 = lean_unsigned_to_nat(0u);
x_142 = l_Lean_Meta_Grind_pushNewFact(x_140, x_141, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_136);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
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
x_143 = lean_ctor_get(x_134, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_134, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_145 = x_134;
} else {
 lean_dec_ref(x_134);
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
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
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
x_147 = lean_ctor_get(x_126, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_126, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_149 = x_126;
} else {
 lean_dec_ref(x_126);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_1);
x_151 = lean_ctor_get(x_122, 1);
lean_inc(x_151);
lean_dec(x_122);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_152 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_2);
x_156 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_156, 0, x_121);
lean_ctor_set(x_156, 1, x_153);
lean_ctor_set(x_156, 2, x_155);
x_157 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__9;
x_158 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_157, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_154);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_unbox(x_159);
lean_dec(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_dec(x_158);
x_162 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_156, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_161);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_163 = lean_ctor_get(x_158, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_164 = x_158;
} else {
 lean_dec_ref(x_158);
 x_164 = lean_box(0);
}
lean_inc(x_156);
x_165 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_156, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_163);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
x_169 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(7, 2, 0);
} else {
 x_170 = x_168;
 lean_ctor_set_tag(x_170, 7);
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_166);
if (lean_is_scalar(x_164)) {
 x_171 = lean_alloc_ctor(7, 2, 0);
} else {
 x_171 = x_164;
 lean_ctor_set_tag(x_171, 7);
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_157, x_171, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_167);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_174 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_156, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_173);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_121);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_175 = lean_ctor_get(x_152, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_152, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_177 = x_152;
} else {
 lean_dec_ref(x_152);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_121);
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
x_179 = lean_ctor_get(x_122, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_122, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_181 = x_122;
} else {
 lean_dec_ref(x_122);
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
}
else
{
uint8_t x_183; 
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
x_183 = !lean_is_exclusive(x_14);
if (x_183 == 0)
{
return x_14;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_14, 0);
x_185 = lean_ctor_get(x_14, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_14);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__1;
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
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
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
x_57 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_Meta_Grind_getGeneration(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_23);
x_28 = l_Int_OfNat_Expr_denoteAsIntExpr(x_24, x_23);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_29 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_28, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Int_Linear_Expr_norm(x_30);
lean_inc(x_1);
x_33 = l_Lean_Meta_Grind_isEqTrue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
lean_inc(x_1);
x_37 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_1, x_6, x_7, x_8, x_9, x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = l_Lean_Expr_cleanupAnnotations(x_39);
x_42 = l_Lean_Expr_isApp(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
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
x_43 = lean_box(0);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = l_Lean_Expr_appArg(x_41, lean_box(0));
x_45 = l_Lean_Expr_appFnCleanup(x_41, lean_box(0));
x_46 = l_Lean_Expr_isApp(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_45);
lean_dec(x_44);
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
lean_ctor_set(x_37, 0, x_47);
return x_37;
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
lean_dec(x_44);
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
lean_ctor_set(x_37, 0, x_51);
return x_37;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Expr_appFnCleanup(x_49, lean_box(0));
x_53 = l_Lean_Expr_isApp(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_52);
lean_dec(x_48);
lean_dec(x_44);
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
lean_ctor_set(x_37, 0, x_54);
return x_37;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = l_Lean_Expr_appFnCleanup(x_52, lean_box(0));
x_56 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_57 = l_Lean_Expr_isConstOf(x_55, x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_48);
lean_dec(x_44);
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
lean_ctor_set(x_37, 0, x_58);
return x_37;
}
else
{
lean_object* x_59; 
lean_free_object(x_37);
x_59 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1(x_1, x_48, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
return x_59;
}
}
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_37, 0);
x_61 = lean_ctor_get(x_37, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_37);
x_62 = l_Lean_Expr_cleanupAnnotations(x_60);
x_63 = l_Lean_Expr_isApp(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_62);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = l_Lean_Expr_appArg(x_62, lean_box(0));
x_67 = l_Lean_Expr_appFnCleanup(x_62, lean_box(0));
x_68 = l_Lean_Expr_isApp(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
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
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_61);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = l_Lean_Expr_appArg(x_67, lean_box(0));
x_72 = l_Lean_Expr_appFnCleanup(x_67, lean_box(0));
x_73 = l_Lean_Expr_isApp(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_72);
lean_dec(x_71);
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
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_61);
return x_75;
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = l_Lean_Expr_appFnCleanup(x_72, lean_box(0));
x_77 = l_Lean_Expr_isApp(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
lean_dec(x_71);
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
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_61);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = l_Lean_Expr_appFnCleanup(x_76, lean_box(0));
x_81 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_82 = l_Lean_Expr_isConstOf(x_80, x_81);
lean_dec(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_71);
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
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_61);
return x_84;
}
else
{
lean_object* x_85; 
x_85 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___lambda__1(x_1, x_71, x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_61);
return x_85;
}
}
}
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_33, 1);
lean_inc(x_86);
lean_dec(x_33);
lean_inc(x_22);
x_87 = lean_nat_to_int(x_22);
x_88 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_24);
lean_ctor_set(x_88, 2, x_22);
lean_ctor_set(x_88, 3, x_23);
lean_ctor_set(x_88, 4, x_30);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_32);
lean_ctor_set(x_89, 2, x_88);
x_90 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_86);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_33);
if (x_91 == 0)
{
return x_33;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_33, 0);
x_93 = lean_ctor_get(x_33, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_33);
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
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_29);
if (x_95 == 0)
{
return x_29;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_29, 0);
x_97 = lean_ctor_get(x_29, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_29);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_11);
if (x_99 == 0)
{
return x_11;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_11, 0);
x_101 = lean_ctor_get(x_11, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_11);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
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
x_29 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
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
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
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
static lean_object* _init_l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_3088____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_3088_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_3 = 0;
x_4 = l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_3088____closed__1;
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
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__3___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__4___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__5___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__8___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__10___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__11___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__11___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lambda__11___closed__1);
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
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__8 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__8);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__9 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___lambda__1___closed__9);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2);
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
l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_3088____closed__1 = _init_l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_3088____closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_3088____closed__1);
if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_3088_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

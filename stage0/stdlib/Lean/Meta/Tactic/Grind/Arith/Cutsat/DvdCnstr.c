// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Simp.Arith.Int Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing Lean.Meta.NatInstTesters
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
lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1830001947____hygCtx___hyg_8_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static double l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstDvdInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8;
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__6;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Int_Linear_Poly_combine(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6;
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
lean_object* l_Int_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstDvdNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5;
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
x_33 = l_Int_Linear_Poly_isSorted(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_32);
x_34 = l_Int_Linear_Poly_norm(x_32);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_1);
lean_inc_ref(x_34);
lean_inc(x_31);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
x_23 = x_36;
x_24 = x_31;
x_25 = x_34;
goto block_30;
}
else
{
lean_inc_ref(x_32);
x_23 = x_1;
x_24 = x_31;
x_25 = x_32;
goto block_30;
}
block_11:
{
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_int_ediv(x_2, x_4);
lean_dec(x_2);
x_8 = l_Int_Linear_Poly_div(x_4, x_3);
lean_dec(x_4);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_5);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
block_22:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Int_Linear_Poly_getConst(x_14);
x_18 = lean_int_emod(x_17, x_16);
lean_dec(x_17);
x_19 = lean_int_dec_eq(x_18, x_12);
lean_dec(x_12);
lean_dec(x_18);
if (x_19 == 0)
{
x_2 = x_13;
x_3 = x_14;
x_4 = x_16;
x_5 = x_15;
x_6 = x_19;
goto block_11;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0;
x_21 = lean_int_dec_eq(x_16, x_20);
if (x_21 == 0)
{
x_2 = x_13;
x_3 = x_14;
x_4 = x_16;
x_5 = x_15;
x_6 = x_19;
goto block_11;
}
else
{
lean_dec(x_16);
lean_dec_ref(x_14);
lean_dec(x_13);
return x_15;
}
}
}
block_30:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_24);
x_26 = l_Int_Linear_Poly_gcdCoeffs(x_25, x_24);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1;
x_28 = lean_int_dec_lt(x_24, x_27);
if (x_28 == 0)
{
x_12 = x_27;
x_13 = x_24;
x_14 = x_25;
x_15 = x_23;
x_16 = x_26;
goto block_22;
}
else
{
lean_object* x_29; 
x_29 = lean_int_neg(x_26);
lean_dec(x_26);
x_12 = x_27;
x_13 = x_24;
x_14 = x_25;
x_15 = x_23;
x_16 = x_29;
goto block_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_1, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static double _init_l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_22 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
x_23 = 0;
x_24 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_23);
x_26 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
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
x_38 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
x_39 = 0;
x_40 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1;
x_41 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_float(x_41, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_41, sizeof(void*)*2 + 8, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_39);
x_42 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
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
x_62 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
x_63 = 0;
x_64 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1;
x_65 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_float(x_65, sizeof(void*)*2, x_62);
lean_ctor_set_float(x_65, sizeof(void*)*2 + 8, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 16, x_63);
x_66 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
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
x_89 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
x_90 = 0;
x_91 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1;
x_92 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_float(x_92, sizeof(void*)*2, x_89);
lean_ctor_set_float(x_92, sizeof(void*)*2 + 8, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*2 + 16, x_90);
x_93 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_35; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4;
x_16 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_15, x_12, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
x_23 = lean_int_mul(x_1, x_21);
x_24 = lean_nat_abs(x_23);
lean_dec(x_23);
x_25 = lean_nat_to_int(x_24);
lean_inc_ref(x_22);
x_26 = l_Int_Linear_Poly_mul(x_22, x_1);
x_27 = lean_int_neg(x_4);
lean_inc_ref(x_20);
x_28 = l_Int_Linear_Poly_mul(x_20, x_27);
lean_dec(x_27);
x_29 = l_Int_Linear_Poly_combine(x_26, x_28);
x_35 = lean_unbox(x_17);
lean_dec(x_17);
if (x_35 == 0)
{
x_30 = x_18;
goto block_34;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(x_2, x_6, x_12, x_18);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
lean_inc_ref(x_3);
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_3, x_6, x_12, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
lean_inc_ref(x_5);
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_5, x_6, x_12, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_46 = l_Lean_MessageData_ofExpr(x_37);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_40);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
x_54 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_15, x_53, x_10, x_11, x_12, x_13, x_44);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec_ref(x_54);
x_30 = x_55;
goto block_34;
}
else
{
uint8_t x_56; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec_ref(x_29);
lean_dec(x_25);
lean_dec(x_19);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_42);
if (x_56 == 0)
{
return x_42;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_42, 0);
x_58 = lean_ctor_get(x_42, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_42);
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
lean_dec(x_37);
lean_dec_ref(x_29);
lean_dec(x_25);
lean_dec(x_19);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_39);
if (x_60 == 0)
{
return x_39;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_39, 0);
x_62 = lean_ctor_get(x_39, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_39);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec_ref(x_29);
lean_dec(x_25);
lean_dec(x_19);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_36);
if (x_64 == 0)
{
return x_36;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_36, 0);
x_66 = lean_ctor_get(x_36, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_36);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
block_34:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_5);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_31);
if (lean_is_scalar(x_19)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_19;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepthErrorMessage;
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__6;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_2, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 2);
x_15 = lean_ctor_get(x_8, 3);
x_16 = lean_ctor_get(x_8, 4);
x_17 = lean_ctor_get(x_8, 5);
x_18 = lean_ctor_get(x_8, 6);
x_19 = lean_ctor_get(x_8, 7);
x_20 = lean_ctor_get(x_8, 8);
x_21 = lean_ctor_get(x_8, 9);
x_22 = lean_ctor_get(x_8, 10);
x_23 = lean_ctor_get(x_8, 11);
x_24 = lean_ctor_get(x_8, 12);
x_25 = lean_ctor_get(x_8, 13);
x_26 = lean_nat_dec_eq(x_15, x_16);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_15, x_28);
lean_dec(x_15);
lean_ctor_set(x_8, 3, x_29);
x_30 = l_Int_Linear_Poly_findVarToSubst___redArg(x_27, x_2, x_8, x_10);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec_ref(x_8);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec_ref(x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_dec_ref(x_30);
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_ctor_get(x_38, 0);
x_43 = l_Int_Linear_Poly_coeff(x_42, x_41);
x_44 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_43, x_41, x_38, x_40, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
lean_dec(x_40);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_1 = x_45;
x_10 = x_46;
goto _start;
}
else
{
lean_dec_ref(x_8);
return x_44;
}
}
}
else
{
uint8_t x_48; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
return x_30;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_30, 0);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_30);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; 
lean_free_object(x_8);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_1);
x_52 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_17, x_10);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; 
x_53 = lean_ctor_get(x_8, 0);
x_54 = lean_ctor_get(x_8, 1);
x_55 = lean_ctor_get(x_8, 2);
x_56 = lean_ctor_get(x_8, 3);
x_57 = lean_ctor_get(x_8, 4);
x_58 = lean_ctor_get(x_8, 5);
x_59 = lean_ctor_get(x_8, 6);
x_60 = lean_ctor_get(x_8, 7);
x_61 = lean_ctor_get(x_8, 8);
x_62 = lean_ctor_get(x_8, 9);
x_63 = lean_ctor_get(x_8, 10);
x_64 = lean_ctor_get(x_8, 11);
x_65 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_66 = lean_ctor_get(x_8, 12);
x_67 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_68 = lean_ctor_get(x_8, 13);
lean_inc(x_68);
lean_inc(x_66);
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
lean_dec(x_8);
x_69 = lean_nat_dec_eq(x_56, x_57);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_1, 1);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_56, x_71);
lean_dec(x_56);
x_73 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_73, 0, x_53);
lean_ctor_set(x_73, 1, x_54);
lean_ctor_set(x_73, 2, x_55);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set(x_73, 4, x_57);
lean_ctor_set(x_73, 5, x_58);
lean_ctor_set(x_73, 6, x_59);
lean_ctor_set(x_73, 7, x_60);
lean_ctor_set(x_73, 8, x_61);
lean_ctor_set(x_73, 9, x_62);
lean_ctor_set(x_73, 10, x_63);
lean_ctor_set(x_73, 11, x_64);
lean_ctor_set(x_73, 12, x_66);
lean_ctor_set(x_73, 13, x_68);
lean_ctor_set_uint8(x_73, sizeof(void*)*14, x_65);
lean_ctor_set_uint8(x_73, sizeof(void*)*14 + 1, x_67);
x_74 = l_Int_Linear_Poly_findVarToSubst___redArg(x_70, x_2, x_73, x_10);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_73);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec_ref(x_75);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_74, 1);
lean_inc(x_82);
lean_dec_ref(x_74);
x_83 = lean_ctor_get(x_79, 0);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_ctor_get(x_81, 0);
x_86 = l_Int_Linear_Poly_coeff(x_85, x_84);
x_87 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_86, x_84, x_81, x_83, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_73, x_9, x_82);
lean_dec(x_83);
lean_dec(x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec_ref(x_87);
x_1 = x_88;
x_8 = x_73;
x_10 = x_89;
goto _start;
}
else
{
lean_dec_ref(x_73);
return x_87;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_73);
lean_dec_ref(x_1);
x_91 = lean_ctor_get(x_74, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_74, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_93 = x_74;
} else {
 lean_dec_ref(x_74);
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
lean_object* x_95; 
lean_dec_ref(x_68);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_1);
x_95 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_58, x_10);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 6);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_PersistentArray_set___redArg(x_5, x_2, x_6);
lean_ctor_set(x_3, 6, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_12 = lean_ctor_get(x_3, 4);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_3, 6);
x_15 = lean_ctor_get(x_3, 7);
x_16 = lean_ctor_get(x_3, 8);
x_17 = lean_ctor_get(x_3, 9);
x_18 = lean_ctor_get(x_3, 10);
x_19 = lean_ctor_get(x_3, 11);
x_20 = lean_ctor_get(x_3, 12);
x_21 = lean_ctor_get(x_3, 13);
x_22 = lean_ctor_get(x_3, 14);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*23);
x_24 = lean_ctor_get(x_3, 15);
x_25 = lean_ctor_get(x_3, 16);
x_26 = lean_ctor_get(x_3, 17);
x_27 = lean_ctor_get(x_3, 18);
x_28 = lean_ctor_get(x_3, 19);
x_29 = lean_ctor_get(x_3, 20);
x_30 = lean_ctor_get(x_3, 21);
x_31 = lean_ctor_get_uint8(x_3, sizeof(void*)*23 + 1);
x_32 = lean_ctor_get(x_3, 22);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_1);
x_34 = l_Lean_PersistentArray_set___redArg(x_14, x_2, x_33);
x_35 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_9);
lean_ctor_set(x_35, 2, x_10);
lean_ctor_set(x_35, 3, x_11);
lean_ctor_set(x_35, 4, x_12);
lean_ctor_set(x_35, 5, x_13);
lean_ctor_set(x_35, 6, x_34);
lean_ctor_set(x_35, 7, x_15);
lean_ctor_set(x_35, 8, x_16);
lean_ctor_set(x_35, 9, x_17);
lean_ctor_set(x_35, 10, x_18);
lean_ctor_set(x_35, 11, x_19);
lean_ctor_set(x_35, 12, x_20);
lean_ctor_set(x_35, 13, x_21);
lean_ctor_set(x_35, 14, x_22);
lean_ctor_set(x_35, 15, x_24);
lean_ctor_set(x_35, 16, x_25);
lean_ctor_set(x_35, 17, x_26);
lean_ctor_set(x_35, 18, x_27);
lean_ctor_set(x_35, 19, x_28);
lean_ctor_set(x_35, 20, x_29);
lean_ctor_set(x_35, 21, x_30);
lean_ctor_set(x_35, 22, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*23, x_23);
lean_ctor_set_uint8(x_35, sizeof(void*)*23 + 1, x_31);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 6);
x_5 = lean_box(0);
x_6 = l_Lean_PersistentArray_set___redArg(x_4, x_1, x_5);
lean_ctor_set(x_2, 6, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*23);
x_23 = lean_ctor_get(x_2, 15);
x_24 = lean_ctor_get(x_2, 16);
x_25 = lean_ctor_get(x_2, 17);
x_26 = lean_ctor_get(x_2, 18);
x_27 = lean_ctor_get(x_2, 19);
x_28 = lean_ctor_get(x_2, 20);
x_29 = lean_ctor_get(x_2, 21);
x_30 = lean_ctor_get_uint8(x_2, sizeof(void*)*23 + 1);
x_31 = lean_ctor_get(x_2, 22);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = l_Lean_PersistentArray_set___redArg(x_13, x_1, x_32);
x_34 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set(x_34, 2, x_9);
lean_ctor_set(x_34, 3, x_10);
lean_ctor_set(x_34, 4, x_11);
lean_ctor_set(x_34, 5, x_12);
lean_ctor_set(x_34, 6, x_33);
lean_ctor_set(x_34, 7, x_14);
lean_ctor_set(x_34, 8, x_15);
lean_ctor_set(x_34, 9, x_16);
lean_ctor_set(x_34, 10, x_17);
lean_ctor_set(x_34, 11, x_18);
lean_ctor_set(x_34, 12, x_19);
lean_ctor_set(x_34, 13, x_20);
lean_ctor_set(x_34, 14, x_21);
lean_ctor_set(x_34, 15, x_23);
lean_ctor_set(x_34, 16, x_24);
lean_ctor_set(x_34, 17, x_25);
lean_ctor_set(x_34, 18, x_26);
lean_ctor_set(x_34, 19, x_27);
lean_ctor_set(x_34, 20, x_28);
lean_ctor_set(x_34, 21, x_29);
lean_ctor_set(x_34, 22, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*23, x_22);
lean_ctor_set_uint8(x_34, sizeof(void*)*23 + 1, x_30);
return x_34;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_43; uint8_t x_47; 
x_47 = !lean_is_exclusive(x_8);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_48 = lean_ctor_get(x_8, 0);
x_49 = lean_ctor_get(x_8, 1);
x_50 = lean_ctor_get(x_8, 2);
x_51 = lean_ctor_get(x_8, 3);
x_52 = lean_ctor_get(x_8, 4);
x_53 = lean_ctor_get(x_8, 5);
x_54 = lean_ctor_get(x_8, 6);
x_55 = lean_ctor_get(x_8, 7);
x_56 = lean_ctor_get(x_8, 8);
x_57 = lean_ctor_get(x_8, 9);
x_58 = lean_ctor_get(x_8, 10);
x_59 = lean_ctor_get(x_8, 11);
x_60 = lean_ctor_get(x_8, 12);
x_61 = lean_ctor_get(x_8, 13);
x_62 = lean_nat_dec_eq(x_51, x_52);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_51, x_63);
lean_dec(x_51);
lean_ctor_set(x_8, 3, x_64);
x_65 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_8, x_10);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_365; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec_ref(x_65);
x_225 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
x_226 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_225, x_8, x_68);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_229 = x_226;
} else {
 lean_dec_ref(x_226);
 x_229 = lean_box(0);
}
x_230 = lean_box(0);
x_365 = lean_unbox(x_227);
lean_dec(x_227);
if (x_365 == 0)
{
x_261 = x_2;
x_262 = x_3;
x_263 = x_4;
x_264 = x_5;
x_265 = x_6;
x_266 = x_7;
x_267 = x_8;
x_268 = x_9;
x_269 = x_228;
goto block_364;
}
else
{
lean_object* x_366; 
lean_inc_ref(x_1);
x_366 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_8, x_228);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec_ref(x_366);
x_369 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_370 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_367);
x_371 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_369);
x_372 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_225, x_371, x_6, x_7, x_8, x_9, x_368);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
lean_dec_ref(x_372);
x_261 = x_2;
x_262 = x_3;
x_263 = x_4;
x_264 = x_5;
x_265 = x_6;
x_266 = x_7;
x_267 = x_8;
x_268 = x_9;
x_269 = x_373;
goto block_364;
}
else
{
uint8_t x_374; 
lean_dec(x_229);
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_374 = !lean_is_exclusive(x_366);
if (x_374 == 0)
{
return x_366;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_366, 0);
x_376 = lean_ctor_get(x_366, 1);
lean_inc(x_376);
lean_inc(x_375);
lean_dec(x_366);
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
return x_377;
}
}
}
block_224:
{
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_85);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_74);
lean_dec(x_70);
lean_dec_ref(x_69);
x_87 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_88 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_87, x_78, x_82);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec_ref(x_72);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec_ref(x_88);
x_30 = x_75;
x_31 = x_84;
x_32 = x_71;
x_33 = x_73;
x_34 = x_83;
x_35 = x_78;
x_36 = x_81;
x_37 = x_91;
goto block_42;
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_88, 1);
x_94 = lean_ctor_get(x_88, 0);
lean_dec(x_94);
x_95 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_72, x_71, x_78, x_93);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_88, 7);
lean_ctor_set(x_88, 1, x_96);
lean_ctor_set(x_88, 0, x_98);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_88);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_87, x_99, x_73, x_83, x_78, x_81, x_97);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec_ref(x_100);
x_30 = x_75;
x_31 = x_84;
x_32 = x_71;
x_33 = x_73;
x_34 = x_83;
x_35 = x_78;
x_36 = x_81;
x_37 = x_101;
goto block_42;
}
else
{
uint8_t x_102; 
lean_free_object(x_88);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec_ref(x_78);
lean_dec_ref(x_75);
lean_dec_ref(x_73);
lean_dec(x_71);
x_102 = !lean_is_exclusive(x_95);
if (x_102 == 0)
{
return x_95;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_95, 0);
x_104 = lean_ctor_get(x_95, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_95);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_88, 1);
lean_inc(x_106);
lean_dec(x_88);
x_107 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_72, x_71, x_78, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec_ref(x_107);
x_110 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_87, x_112, x_73, x_83, x_78, x_81, x_109);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec_ref(x_113);
x_30 = x_75;
x_31 = x_84;
x_32 = x_71;
x_33 = x_73;
x_34 = x_83;
x_35 = x_78;
x_36 = x_81;
x_37 = x_114;
goto block_42;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec_ref(x_78);
lean_dec_ref(x_75);
lean_dec_ref(x_73);
lean_dec(x_71);
x_115 = lean_ctor_get(x_107, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_107, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_117 = x_107;
} else {
 lean_dec_ref(x_107);
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
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec_ref(x_84);
lean_dec_ref(x_75);
x_119 = lean_ctor_get(x_86, 0);
lean_inc(x_119);
lean_dec_ref(x_86);
x_120 = lean_ctor_get(x_119, 1);
lean_inc_ref(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
lean_dec_ref(x_120);
lean_dec(x_85);
lean_dec_ref(x_79);
lean_dec(x_76);
lean_dec_ref(x_72);
lean_dec(x_70);
lean_dec_ref(x_69);
x_121 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_119, x_71, x_77, x_74, x_80, x_73, x_83, x_78, x_81, x_82);
lean_dec(x_81);
lean_dec_ref(x_78);
lean_dec(x_83);
lean_dec_ref(x_73);
lean_dec(x_80);
lean_dec_ref(x_74);
lean_dec(x_77);
lean_dec(x_71);
return x_121;
}
else
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_123 = lean_ctor_get(x_119, 0);
x_124 = lean_ctor_get(x_120, 0);
x_125 = lean_ctor_get(x_120, 2);
x_126 = lean_ctor_get(x_120, 1);
lean_dec(x_126);
x_127 = lean_int_mul(x_76, x_123);
x_128 = lean_int_mul(x_124, x_70);
x_129 = l_Lean_Meta_Grind_Arith_gcdExt(x_127, x_128);
lean_dec(x_128);
lean_dec(x_127);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec_ref(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_135 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_134, x_69, x_71, x_82);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_137 = lean_ctor_get(x_135, 1);
x_138 = lean_ctor_get(x_135, 0);
lean_dec(x_138);
x_139 = lean_int_mul(x_132, x_123);
lean_dec(x_132);
lean_inc_ref(x_79);
x_140 = l_Int_Linear_Poly_mul(x_79, x_139);
lean_dec(x_139);
x_141 = lean_int_mul(x_133, x_70);
lean_dec(x_133);
lean_inc_ref(x_125);
x_142 = l_Int_Linear_Poly_mul(x_125, x_141);
lean_dec(x_141);
x_143 = lean_int_mul(x_70, x_123);
lean_dec(x_70);
x_144 = l_Int_Linear_Poly_combine(x_140, x_142);
lean_inc(x_131);
lean_ctor_set(x_120, 2, x_144);
lean_ctor_set(x_120, 1, x_85);
lean_ctor_set(x_120, 0, x_131);
lean_inc(x_119);
lean_inc_ref(x_72);
lean_ctor_set_tag(x_135, 4);
lean_ctor_set(x_135, 1, x_119);
lean_ctor_set(x_135, 0, x_72);
x_145 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_120);
lean_ctor_set(x_145, 2, x_135);
lean_inc(x_81);
lean_inc_ref(x_78);
lean_inc(x_83);
lean_inc_ref(x_73);
lean_inc(x_80);
lean_inc_ref(x_74);
lean_inc(x_77);
lean_inc(x_71);
x_146 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_145, x_71, x_77, x_74, x_80, x_73, x_83, x_78, x_81, x_137);
if (lean_obj_tag(x_146) == 0)
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_148 = lean_ctor_get(x_146, 1);
x_149 = lean_ctor_get(x_146, 0);
lean_dec(x_149);
x_150 = l_Int_Linear_Poly_mul(x_79, x_124);
lean_dec(x_124);
x_151 = lean_int_neg(x_76);
lean_dec(x_76);
x_152 = l_Int_Linear_Poly_mul(x_125, x_151);
lean_dec(x_151);
x_153 = l_Int_Linear_Poly_combine(x_150, x_152);
lean_inc(x_119);
lean_ctor_set_tag(x_146, 5);
lean_ctor_set(x_146, 1, x_119);
lean_ctor_set(x_146, 0, x_72);
x_154 = !lean_is_exclusive(x_119);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_119, 2);
lean_dec(x_155);
x_156 = lean_ctor_get(x_119, 1);
lean_dec(x_156);
x_157 = lean_ctor_get(x_119, 0);
lean_dec(x_157);
lean_ctor_set(x_119, 2, x_146);
lean_ctor_set(x_119, 1, x_153);
lean_ctor_set(x_119, 0, x_131);
x_1 = x_119;
x_2 = x_71;
x_3 = x_77;
x_4 = x_74;
x_5 = x_80;
x_6 = x_73;
x_7 = x_83;
x_8 = x_78;
x_9 = x_81;
x_10 = x_148;
goto _start;
}
else
{
lean_object* x_159; 
lean_dec(x_119);
x_159 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_159, 0, x_131);
lean_ctor_set(x_159, 1, x_153);
lean_ctor_set(x_159, 2, x_146);
x_1 = x_159;
x_2 = x_71;
x_3 = x_77;
x_4 = x_74;
x_5 = x_80;
x_6 = x_73;
x_7 = x_83;
x_8 = x_78;
x_9 = x_81;
x_10 = x_148;
goto _start;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_161 = lean_ctor_get(x_146, 1);
lean_inc(x_161);
lean_dec(x_146);
x_162 = l_Int_Linear_Poly_mul(x_79, x_124);
lean_dec(x_124);
x_163 = lean_int_neg(x_76);
lean_dec(x_76);
x_164 = l_Int_Linear_Poly_mul(x_125, x_163);
lean_dec(x_163);
x_165 = l_Int_Linear_Poly_combine(x_162, x_164);
lean_inc(x_119);
x_166 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_166, 0, x_72);
lean_ctor_set(x_166, 1, x_119);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 x_167 = x_119;
} else {
 lean_dec_ref(x_119);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 3, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_131);
lean_ctor_set(x_168, 1, x_165);
lean_ctor_set(x_168, 2, x_166);
x_1 = x_168;
x_2 = x_71;
x_3 = x_77;
x_4 = x_74;
x_5 = x_80;
x_6 = x_73;
x_7 = x_83;
x_8 = x_78;
x_9 = x_81;
x_10 = x_161;
goto _start;
}
}
else
{
lean_dec(x_131);
lean_dec_ref(x_125);
lean_dec(x_124);
lean_dec(x_119);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
return x_146;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_170 = lean_ctor_get(x_135, 1);
lean_inc(x_170);
lean_dec(x_135);
x_171 = lean_int_mul(x_132, x_123);
lean_dec(x_132);
lean_inc_ref(x_79);
x_172 = l_Int_Linear_Poly_mul(x_79, x_171);
lean_dec(x_171);
x_173 = lean_int_mul(x_133, x_70);
lean_dec(x_133);
lean_inc_ref(x_125);
x_174 = l_Int_Linear_Poly_mul(x_125, x_173);
lean_dec(x_173);
x_175 = lean_int_mul(x_70, x_123);
lean_dec(x_70);
x_176 = l_Int_Linear_Poly_combine(x_172, x_174);
lean_inc(x_131);
lean_ctor_set(x_120, 2, x_176);
lean_ctor_set(x_120, 1, x_85);
lean_ctor_set(x_120, 0, x_131);
lean_inc(x_119);
lean_inc_ref(x_72);
x_177 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_177, 0, x_72);
lean_ctor_set(x_177, 1, x_119);
x_178 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_120);
lean_ctor_set(x_178, 2, x_177);
lean_inc(x_81);
lean_inc_ref(x_78);
lean_inc(x_83);
lean_inc_ref(x_73);
lean_inc(x_80);
lean_inc_ref(x_74);
lean_inc(x_77);
lean_inc(x_71);
x_179 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_178, x_71, x_77, x_74, x_80, x_73, x_83, x_78, x_81, x_170);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
x_182 = l_Int_Linear_Poly_mul(x_79, x_124);
lean_dec(x_124);
x_183 = lean_int_neg(x_76);
lean_dec(x_76);
x_184 = l_Int_Linear_Poly_mul(x_125, x_183);
lean_dec(x_183);
x_185 = l_Int_Linear_Poly_combine(x_182, x_184);
lean_inc(x_119);
if (lean_is_scalar(x_181)) {
 x_186 = lean_alloc_ctor(5, 2, 0);
} else {
 x_186 = x_181;
 lean_ctor_set_tag(x_186, 5);
}
lean_ctor_set(x_186, 0, x_72);
lean_ctor_set(x_186, 1, x_119);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 x_187 = x_119;
} else {
 lean_dec_ref(x_119);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(0, 3, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_131);
lean_ctor_set(x_188, 1, x_185);
lean_ctor_set(x_188, 2, x_186);
x_1 = x_188;
x_2 = x_71;
x_3 = x_77;
x_4 = x_74;
x_5 = x_80;
x_6 = x_73;
x_7 = x_83;
x_8 = x_78;
x_9 = x_81;
x_10 = x_180;
goto _start;
}
else
{
lean_dec(x_131);
lean_dec_ref(x_125);
lean_dec(x_124);
lean_dec(x_119);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
return x_179;
}
}
}
else
{
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_free_object(x_120);
lean_dec_ref(x_125);
lean_dec(x_124);
lean_dec(x_119);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_70);
return x_135;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_190 = lean_ctor_get(x_119, 0);
x_191 = lean_ctor_get(x_120, 0);
x_192 = lean_ctor_get(x_120, 2);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_120);
x_193 = lean_int_mul(x_76, x_190);
x_194 = lean_int_mul(x_191, x_70);
x_195 = l_Lean_Meta_Grind_Arith_gcdExt(x_193, x_194);
lean_dec(x_194);
lean_dec(x_193);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
lean_dec_ref(x_195);
x_198 = lean_ctor_get(x_196, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_200 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_201 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_200, x_69, x_71, x_82);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
x_204 = lean_int_mul(x_198, x_190);
lean_dec(x_198);
lean_inc_ref(x_79);
x_205 = l_Int_Linear_Poly_mul(x_79, x_204);
lean_dec(x_204);
x_206 = lean_int_mul(x_199, x_70);
lean_dec(x_199);
lean_inc_ref(x_192);
x_207 = l_Int_Linear_Poly_mul(x_192, x_206);
lean_dec(x_206);
x_208 = lean_int_mul(x_70, x_190);
lean_dec(x_70);
x_209 = l_Int_Linear_Poly_combine(x_205, x_207);
lean_inc(x_197);
x_210 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_210, 0, x_197);
lean_ctor_set(x_210, 1, x_85);
lean_ctor_set(x_210, 2, x_209);
lean_inc(x_119);
lean_inc_ref(x_72);
if (lean_is_scalar(x_203)) {
 x_211 = lean_alloc_ctor(4, 2, 0);
} else {
 x_211 = x_203;
 lean_ctor_set_tag(x_211, 4);
}
lean_ctor_set(x_211, 0, x_72);
lean_ctor_set(x_211, 1, x_119);
x_212 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_212, 0, x_208);
lean_ctor_set(x_212, 1, x_210);
lean_ctor_set(x_212, 2, x_211);
lean_inc(x_81);
lean_inc_ref(x_78);
lean_inc(x_83);
lean_inc_ref(x_73);
lean_inc(x_80);
lean_inc_ref(x_74);
lean_inc(x_77);
lean_inc(x_71);
x_213 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_212, x_71, x_77, x_74, x_80, x_73, x_83, x_78, x_81, x_202);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_215 = x_213;
} else {
 lean_dec_ref(x_213);
 x_215 = lean_box(0);
}
x_216 = l_Int_Linear_Poly_mul(x_79, x_191);
lean_dec(x_191);
x_217 = lean_int_neg(x_76);
lean_dec(x_76);
x_218 = l_Int_Linear_Poly_mul(x_192, x_217);
lean_dec(x_217);
x_219 = l_Int_Linear_Poly_combine(x_216, x_218);
lean_inc(x_119);
if (lean_is_scalar(x_215)) {
 x_220 = lean_alloc_ctor(5, 2, 0);
} else {
 x_220 = x_215;
 lean_ctor_set_tag(x_220, 5);
}
lean_ctor_set(x_220, 0, x_72);
lean_ctor_set(x_220, 1, x_119);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 x_221 = x_119;
} else {
 lean_dec_ref(x_119);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(0, 3, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_197);
lean_ctor_set(x_222, 1, x_219);
lean_ctor_set(x_222, 2, x_220);
x_1 = x_222;
x_2 = x_71;
x_3 = x_77;
x_4 = x_74;
x_5 = x_80;
x_6 = x_73;
x_7 = x_83;
x_8 = x_78;
x_9 = x_81;
x_10 = x_214;
goto _start;
}
else
{
lean_dec(x_197);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec(x_119);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
return x_213;
}
}
else
{
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec_ref(x_192);
lean_dec(x_191);
lean_dec(x_119);
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_70);
return x_201;
}
}
}
}
}
block_260:
{
lean_object* x_248; 
x_248 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_239, x_245, x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_249, 6);
lean_inc_ref(x_250);
lean_dec(x_249);
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
lean_dec_ref(x_248);
x_252 = lean_ctor_get(x_250, 2);
x_253 = lean_nat_dec_lt(x_238, x_252);
if (x_253 == 0)
{
lean_object* x_254; 
lean_dec_ref(x_250);
x_254 = l_outOfBounds___redArg(x_230);
x_69 = x_232;
x_70 = x_233;
x_71 = x_239;
x_72 = x_234;
x_73 = x_243;
x_74 = x_241;
x_75 = x_235;
x_76 = x_236;
x_77 = x_240;
x_78 = x_245;
x_79 = x_231;
x_80 = x_242;
x_81 = x_246;
x_82 = x_251;
x_83 = x_244;
x_84 = x_237;
x_85 = x_238;
x_86 = x_254;
goto block_224;
}
else
{
lean_object* x_255; 
x_255 = l_Lean_PersistentArray_get_x21___redArg(x_230, x_250, x_238);
x_69 = x_232;
x_70 = x_233;
x_71 = x_239;
x_72 = x_234;
x_73 = x_243;
x_74 = x_241;
x_75 = x_235;
x_76 = x_236;
x_77 = x_240;
x_78 = x_245;
x_79 = x_231;
x_80 = x_242;
x_81 = x_246;
x_82 = x_251;
x_83 = x_244;
x_84 = x_237;
x_85 = x_238;
x_86 = x_255;
goto block_224;
}
}
else
{
uint8_t x_256; 
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec_ref(x_237);
lean_dec(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
x_256 = !lean_is_exclusive(x_248);
if (x_256 == 0)
{
return x_248;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_248, 0);
x_258 = lean_ctor_get(x_248, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_248);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
block_364:
{
lean_object* x_270; lean_object* x_271; 
x_270 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_267);
x_271 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_270, x_261, x_262, x_263, x_264, x_265, x_266, x_267, x_268, x_269);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec_ref(x_271);
x_274 = lean_ctor_get(x_272, 0);
x_275 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
x_276 = l_Int_Linear_Poly_isUnsatDvd(x_274, x_275);
if (x_276 == 0)
{
uint8_t x_277; 
x_277 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_272);
if (x_277 == 0)
{
lean_dec(x_229);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_278; 
x_278 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_272, x_261, x_262, x_263, x_264, x_265, x_266, x_267, x_268, x_273);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_261);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_inc_ref(x_275);
lean_inc(x_274);
x_279 = lean_ctor_get(x_275, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_275, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_275, 2);
lean_inc_ref(x_281);
lean_inc(x_272);
x_282 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_272, x_261, x_267, x_273);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; uint8_t x_288; uint8_t x_289; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec_ref(x_282);
lean_inc(x_280);
lean_inc(x_272);
x_285 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(x_285, 0, x_272);
lean_closure_set(x_285, 1, x_280);
lean_inc(x_280);
x_286 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(x_286, 0, x_280);
x_287 = 0;
x_288 = lean_unbox(x_283);
lean_dec(x_283);
x_289 = l_Lean_instBEqLBool_beq(x_288, x_287);
if (x_289 == 0)
{
x_231 = x_281;
x_232 = x_286;
x_233 = x_274;
x_234 = x_272;
x_235 = x_275;
x_236 = x_279;
x_237 = x_285;
x_238 = x_280;
x_239 = x_261;
x_240 = x_262;
x_241 = x_263;
x_242 = x_264;
x_243 = x_265;
x_244 = x_266;
x_245 = x_267;
x_246 = x_268;
x_247 = x_284;
goto block_260;
}
else
{
lean_object* x_290; 
lean_inc(x_280);
x_290 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_280, x_261, x_284);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; 
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
lean_dec_ref(x_290);
x_231 = x_281;
x_232 = x_286;
x_233 = x_274;
x_234 = x_272;
x_235 = x_275;
x_236 = x_279;
x_237 = x_285;
x_238 = x_280;
x_239 = x_261;
x_240 = x_262;
x_241 = x_263;
x_242 = x_264;
x_243 = x_265;
x_244 = x_266;
x_245 = x_267;
x_246 = x_268;
x_247 = x_291;
goto block_260;
}
else
{
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec_ref(x_281);
lean_dec(x_280);
lean_dec(x_279);
lean_dec_ref(x_275);
lean_dec(x_274);
lean_dec(x_272);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_261);
return x_290;
}
}
}
else
{
uint8_t x_292; 
lean_dec_ref(x_281);
lean_dec(x_280);
lean_dec(x_279);
lean_dec_ref(x_275);
lean_dec(x_274);
lean_dec(x_272);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_261);
x_292 = !lean_is_exclusive(x_282);
if (x_292 == 0)
{
return x_282;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_282, 0);
x_294 = lean_ctor_get(x_282, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_282);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
x_296 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
x_297 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_296, x_267, x_273);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_unbox(x_298);
lean_dec(x_298);
if (x_299 == 0)
{
lean_object* x_300; 
lean_dec(x_272);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_261);
lean_dec(x_229);
x_300 = lean_ctor_get(x_297, 1);
lean_inc(x_300);
lean_dec_ref(x_297);
x_43 = x_300;
goto block_46;
}
else
{
uint8_t x_301; 
x_301 = !lean_is_exclusive(x_297);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_297, 1);
x_303 = lean_ctor_get(x_297, 0);
lean_dec(x_303);
x_304 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_272, x_261, x_267, x_302);
lean_dec(x_261);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec_ref(x_304);
x_307 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_297, 7);
lean_ctor_set(x_297, 1, x_305);
lean_ctor_set(x_297, 0, x_307);
if (lean_is_scalar(x_229)) {
 x_308 = lean_alloc_ctor(7, 2, 0);
} else {
 x_308 = x_229;
 lean_ctor_set_tag(x_308, 7);
}
lean_ctor_set(x_308, 0, x_297);
lean_ctor_set(x_308, 1, x_307);
x_309 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_296, x_308, x_265, x_266, x_267, x_268, x_306);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
x_310 = lean_ctor_get(x_309, 1);
lean_inc(x_310);
lean_dec_ref(x_309);
x_43 = x_310;
goto block_46;
}
else
{
uint8_t x_311; 
lean_free_object(x_297);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_229);
x_311 = !lean_is_exclusive(x_304);
if (x_311 == 0)
{
return x_304;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_304, 0);
x_313 = lean_ctor_get(x_304, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_304);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; 
x_315 = lean_ctor_get(x_297, 1);
lean_inc(x_315);
lean_dec(x_297);
x_316 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_272, x_261, x_267, x_315);
lean_dec(x_261);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec_ref(x_316);
x_319 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_320 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_317);
if (lean_is_scalar(x_229)) {
 x_321 = lean_alloc_ctor(7, 2, 0);
} else {
 x_321 = x_229;
 lean_ctor_set_tag(x_321, 7);
}
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_319);
x_322 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_296, x_321, x_265, x_266, x_267, x_268, x_318);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
lean_dec_ref(x_322);
x_43 = x_323;
goto block_46;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_229);
x_324 = lean_ctor_get(x_316, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_316, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_326 = x_316;
} else {
 lean_dec_ref(x_316);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 2, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
}
}
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_328 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8;
x_329 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_328, x_267, x_273);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_unbox(x_330);
lean_dec(x_330);
if (x_331 == 0)
{
lean_object* x_332; 
lean_dec(x_229);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_dec_ref(x_329);
x_11 = x_272;
x_12 = x_261;
x_13 = x_262;
x_14 = x_263;
x_15 = x_264;
x_16 = x_265;
x_17 = x_266;
x_18 = x_267;
x_19 = x_268;
x_20 = x_332;
goto block_29;
}
else
{
uint8_t x_333; 
x_333 = !lean_is_exclusive(x_329);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_329, 1);
x_335 = lean_ctor_get(x_329, 0);
lean_dec(x_335);
lean_inc(x_272);
x_336 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_272, x_261, x_267, x_334);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec_ref(x_336);
x_339 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_329, 7);
lean_ctor_set(x_329, 1, x_337);
lean_ctor_set(x_329, 0, x_339);
if (lean_is_scalar(x_229)) {
 x_340 = lean_alloc_ctor(7, 2, 0);
} else {
 x_340 = x_229;
 lean_ctor_set_tag(x_340, 7);
}
lean_ctor_set(x_340, 0, x_329);
lean_ctor_set(x_340, 1, x_339);
x_341 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_328, x_340, x_265, x_266, x_267, x_268, x_338);
x_342 = lean_ctor_get(x_341, 1);
lean_inc(x_342);
lean_dec_ref(x_341);
x_11 = x_272;
x_12 = x_261;
x_13 = x_262;
x_14 = x_263;
x_15 = x_264;
x_16 = x_265;
x_17 = x_266;
x_18 = x_267;
x_19 = x_268;
x_20 = x_342;
goto block_29;
}
else
{
uint8_t x_343; 
lean_free_object(x_329);
lean_dec(x_272);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_229);
x_343 = !lean_is_exclusive(x_336);
if (x_343 == 0)
{
return x_336;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_336, 0);
x_345 = lean_ctor_get(x_336, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_336);
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
x_347 = lean_ctor_get(x_329, 1);
lean_inc(x_347);
lean_dec(x_329);
lean_inc(x_272);
x_348 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_272, x_261, x_267, x_347);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec_ref(x_348);
x_351 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_352 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_349);
if (lean_is_scalar(x_229)) {
 x_353 = lean_alloc_ctor(7, 2, 0);
} else {
 x_353 = x_229;
 lean_ctor_set_tag(x_353, 7);
}
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_351);
x_354 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_328, x_353, x_265, x_266, x_267, x_268, x_350);
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
lean_dec_ref(x_354);
x_11 = x_272;
x_12 = x_261;
x_13 = x_262;
x_14 = x_263;
x_15 = x_264;
x_16 = x_265;
x_17 = x_266;
x_18 = x_267;
x_19 = x_268;
x_20 = x_355;
goto block_29;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_272);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_229);
x_356 = lean_ctor_get(x_348, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_348, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_358 = x_348;
} else {
 lean_dec_ref(x_348);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
}
}
}
}
else
{
uint8_t x_360; 
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_229);
x_360 = !lean_is_exclusive(x_271);
if (x_360 == 0)
{
return x_271;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_271, 0);
x_362 = lean_ctor_get(x_271, 1);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_271);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_362);
return x_363;
}
}
}
}
else
{
uint8_t x_378; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_378 = !lean_is_exclusive(x_65);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_65, 0);
lean_dec(x_379);
x_380 = lean_box(0);
lean_ctor_set(x_65, 0, x_380);
return x_65;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_65, 1);
lean_inc(x_381);
lean_dec(x_65);
x_382 = lean_box(0);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_381);
return x_383;
}
}
}
else
{
uint8_t x_384; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_384 = !lean_is_exclusive(x_65);
if (x_384 == 0)
{
return x_65;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_65, 0);
x_386 = lean_ctor_get(x_65, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_65);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
return x_387;
}
}
}
else
{
lean_object* x_388; 
lean_free_object(x_8);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_388 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_53, x_10);
return x_388;
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; uint8_t x_405; 
x_389 = lean_ctor_get(x_8, 0);
x_390 = lean_ctor_get(x_8, 1);
x_391 = lean_ctor_get(x_8, 2);
x_392 = lean_ctor_get(x_8, 3);
x_393 = lean_ctor_get(x_8, 4);
x_394 = lean_ctor_get(x_8, 5);
x_395 = lean_ctor_get(x_8, 6);
x_396 = lean_ctor_get(x_8, 7);
x_397 = lean_ctor_get(x_8, 8);
x_398 = lean_ctor_get(x_8, 9);
x_399 = lean_ctor_get(x_8, 10);
x_400 = lean_ctor_get(x_8, 11);
x_401 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_402 = lean_ctor_get(x_8, 12);
x_403 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_404 = lean_ctor_get(x_8, 13);
lean_inc(x_404);
lean_inc(x_402);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
lean_inc(x_397);
lean_inc(x_396);
lean_inc(x_395);
lean_inc(x_394);
lean_inc(x_393);
lean_inc(x_392);
lean_inc(x_391);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_8);
x_405 = lean_nat_dec_eq(x_392, x_393);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_406 = lean_unsigned_to_nat(1u);
x_407 = lean_nat_add(x_392, x_406);
lean_dec(x_392);
x_408 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_408, 0, x_389);
lean_ctor_set(x_408, 1, x_390);
lean_ctor_set(x_408, 2, x_391);
lean_ctor_set(x_408, 3, x_407);
lean_ctor_set(x_408, 4, x_393);
lean_ctor_set(x_408, 5, x_394);
lean_ctor_set(x_408, 6, x_395);
lean_ctor_set(x_408, 7, x_396);
lean_ctor_set(x_408, 8, x_397);
lean_ctor_set(x_408, 9, x_398);
lean_ctor_set(x_408, 10, x_399);
lean_ctor_set(x_408, 11, x_400);
lean_ctor_set(x_408, 12, x_402);
lean_ctor_set(x_408, 13, x_404);
lean_ctor_set_uint8(x_408, sizeof(void*)*14, x_401);
lean_ctor_set_uint8(x_408, sizeof(void*)*14 + 1, x_403);
x_409 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_408, x_10);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; uint8_t x_411; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_unbox(x_410);
lean_dec(x_410);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; uint8_t x_603; 
x_412 = lean_ctor_get(x_409, 1);
lean_inc(x_412);
lean_dec_ref(x_409);
x_489 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
x_490 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_489, x_408, x_412);
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_493 = x_490;
} else {
 lean_dec_ref(x_490);
 x_493 = lean_box(0);
}
x_494 = lean_box(0);
x_603 = lean_unbox(x_491);
lean_dec(x_491);
if (x_603 == 0)
{
x_525 = x_2;
x_526 = x_3;
x_527 = x_4;
x_528 = x_5;
x_529 = x_6;
x_530 = x_7;
x_531 = x_408;
x_532 = x_9;
x_533 = x_492;
goto block_602;
}
else
{
lean_object* x_604; 
lean_inc_ref(x_1);
x_604 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_408, x_492);
if (lean_obj_tag(x_604) == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_604, 1);
lean_inc(x_606);
lean_dec_ref(x_604);
x_607 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_608 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_608, 0, x_607);
lean_ctor_set(x_608, 1, x_605);
x_609 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_607);
x_610 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_489, x_609, x_6, x_7, x_408, x_9, x_606);
x_611 = lean_ctor_get(x_610, 1);
lean_inc(x_611);
lean_dec_ref(x_610);
x_525 = x_2;
x_526 = x_3;
x_527 = x_4;
x_528 = x_5;
x_529 = x_6;
x_530 = x_7;
x_531 = x_408;
x_532 = x_9;
x_533 = x_611;
goto block_602;
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec(x_493);
lean_dec_ref(x_408);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_612 = lean_ctor_get(x_604, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_604, 1);
lean_inc(x_613);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_614 = x_604;
} else {
 lean_dec_ref(x_604);
 x_614 = lean_box(0);
}
if (lean_is_scalar(x_614)) {
 x_615 = lean_alloc_ctor(1, 2, 0);
} else {
 x_615 = x_614;
}
lean_ctor_set(x_615, 0, x_612);
lean_ctor_set(x_615, 1, x_613);
return x_615;
}
}
block_488:
{
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
lean_dec(x_429);
lean_dec(x_424);
lean_dec_ref(x_423);
lean_dec(x_421);
lean_dec(x_420);
lean_dec_ref(x_418);
lean_dec(x_414);
lean_dec_ref(x_413);
x_431 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_432 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_431, x_422, x_426);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_unbox(x_433);
lean_dec(x_433);
if (x_434 == 0)
{
lean_object* x_435; 
lean_dec_ref(x_416);
x_435 = lean_ctor_get(x_432, 1);
lean_inc(x_435);
lean_dec_ref(x_432);
x_30 = x_419;
x_31 = x_428;
x_32 = x_415;
x_33 = x_417;
x_34 = x_427;
x_35 = x_422;
x_36 = x_425;
x_37 = x_435;
goto block_42;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_432, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_437 = x_432;
} else {
 lean_dec_ref(x_432);
 x_437 = lean_box(0);
}
x_438 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_416, x_415, x_422, x_436);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec_ref(x_438);
x_441 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_437)) {
 x_442 = lean_alloc_ctor(7, 2, 0);
} else {
 x_442 = x_437;
 lean_ctor_set_tag(x_442, 7);
}
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_439);
x_443 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_441);
x_444 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_431, x_443, x_417, x_427, x_422, x_425, x_440);
x_445 = lean_ctor_get(x_444, 1);
lean_inc(x_445);
lean_dec_ref(x_444);
x_30 = x_419;
x_31 = x_428;
x_32 = x_415;
x_33 = x_417;
x_34 = x_427;
x_35 = x_422;
x_36 = x_425;
x_37 = x_445;
goto block_42;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_437);
lean_dec_ref(x_428);
lean_dec(x_427);
lean_dec(x_425);
lean_dec_ref(x_422);
lean_dec_ref(x_419);
lean_dec_ref(x_417);
lean_dec(x_415);
x_446 = lean_ctor_get(x_438, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_438, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_448 = x_438;
} else {
 lean_dec_ref(x_438);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
}
else
{
lean_object* x_450; lean_object* x_451; 
lean_dec_ref(x_428);
lean_dec_ref(x_419);
x_450 = lean_ctor_get(x_430, 0);
lean_inc(x_450);
lean_dec_ref(x_430);
x_451 = lean_ctor_get(x_450, 1);
lean_inc_ref(x_451);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; 
lean_dec_ref(x_451);
lean_dec(x_429);
lean_dec_ref(x_423);
lean_dec(x_420);
lean_dec_ref(x_416);
lean_dec(x_414);
lean_dec_ref(x_413);
x_452 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_450, x_415, x_421, x_418, x_424, x_417, x_427, x_422, x_425, x_426);
lean_dec(x_425);
lean_dec_ref(x_422);
lean_dec(x_427);
lean_dec_ref(x_417);
lean_dec(x_424);
lean_dec_ref(x_418);
lean_dec(x_421);
lean_dec(x_415);
return x_452;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_453 = lean_ctor_get(x_450, 0);
x_454 = lean_ctor_get(x_451, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_451, 2);
lean_inc_ref(x_455);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 lean_ctor_release(x_451, 2);
 x_456 = x_451;
} else {
 lean_dec_ref(x_451);
 x_456 = lean_box(0);
}
x_457 = lean_int_mul(x_420, x_453);
x_458 = lean_int_mul(x_454, x_414);
x_459 = l_Lean_Meta_Grind_Arith_gcdExt(x_457, x_458);
lean_dec(x_458);
lean_dec(x_457);
x_460 = lean_ctor_get(x_459, 1);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 0);
lean_inc(x_461);
lean_dec_ref(x_459);
x_462 = lean_ctor_get(x_460, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_460, 1);
lean_inc(x_463);
lean_dec(x_460);
x_464 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_465 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_464, x_413, x_415, x_426);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_466 = lean_ctor_get(x_465, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_467 = x_465;
} else {
 lean_dec_ref(x_465);
 x_467 = lean_box(0);
}
x_468 = lean_int_mul(x_462, x_453);
lean_dec(x_462);
lean_inc_ref(x_423);
x_469 = l_Int_Linear_Poly_mul(x_423, x_468);
lean_dec(x_468);
x_470 = lean_int_mul(x_463, x_414);
lean_dec(x_463);
lean_inc_ref(x_455);
x_471 = l_Int_Linear_Poly_mul(x_455, x_470);
lean_dec(x_470);
x_472 = lean_int_mul(x_414, x_453);
lean_dec(x_414);
x_473 = l_Int_Linear_Poly_combine(x_469, x_471);
lean_inc(x_461);
if (lean_is_scalar(x_456)) {
 x_474 = lean_alloc_ctor(1, 3, 0);
} else {
 x_474 = x_456;
}
lean_ctor_set(x_474, 0, x_461);
lean_ctor_set(x_474, 1, x_429);
lean_ctor_set(x_474, 2, x_473);
lean_inc(x_450);
lean_inc_ref(x_416);
if (lean_is_scalar(x_467)) {
 x_475 = lean_alloc_ctor(4, 2, 0);
} else {
 x_475 = x_467;
 lean_ctor_set_tag(x_475, 4);
}
lean_ctor_set(x_475, 0, x_416);
lean_ctor_set(x_475, 1, x_450);
x_476 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_476, 0, x_472);
lean_ctor_set(x_476, 1, x_474);
lean_ctor_set(x_476, 2, x_475);
lean_inc(x_425);
lean_inc_ref(x_422);
lean_inc(x_427);
lean_inc_ref(x_417);
lean_inc(x_424);
lean_inc_ref(x_418);
lean_inc(x_421);
lean_inc(x_415);
x_477 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_476, x_415, x_421, x_418, x_424, x_417, x_427, x_422, x_425, x_466);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_478 = lean_ctor_get(x_477, 1);
lean_inc(x_478);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_479 = x_477;
} else {
 lean_dec_ref(x_477);
 x_479 = lean_box(0);
}
x_480 = l_Int_Linear_Poly_mul(x_423, x_454);
lean_dec(x_454);
x_481 = lean_int_neg(x_420);
lean_dec(x_420);
x_482 = l_Int_Linear_Poly_mul(x_455, x_481);
lean_dec(x_481);
x_483 = l_Int_Linear_Poly_combine(x_480, x_482);
lean_inc(x_450);
if (lean_is_scalar(x_479)) {
 x_484 = lean_alloc_ctor(5, 2, 0);
} else {
 x_484 = x_479;
 lean_ctor_set_tag(x_484, 5);
}
lean_ctor_set(x_484, 0, x_416);
lean_ctor_set(x_484, 1, x_450);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 lean_ctor_release(x_450, 2);
 x_485 = x_450;
} else {
 lean_dec_ref(x_450);
 x_485 = lean_box(0);
}
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(0, 3, 0);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_461);
lean_ctor_set(x_486, 1, x_483);
lean_ctor_set(x_486, 2, x_484);
x_1 = x_486;
x_2 = x_415;
x_3 = x_421;
x_4 = x_418;
x_5 = x_424;
x_6 = x_417;
x_7 = x_427;
x_8 = x_422;
x_9 = x_425;
x_10 = x_478;
goto _start;
}
else
{
lean_dec(x_461);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_450);
lean_dec(x_427);
lean_dec(x_425);
lean_dec(x_424);
lean_dec_ref(x_423);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec_ref(x_418);
lean_dec_ref(x_417);
lean_dec_ref(x_416);
lean_dec(x_415);
return x_477;
}
}
else
{
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_450);
lean_dec(x_429);
lean_dec(x_427);
lean_dec(x_425);
lean_dec(x_424);
lean_dec_ref(x_423);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec_ref(x_418);
lean_dec_ref(x_417);
lean_dec_ref(x_416);
lean_dec(x_415);
lean_dec(x_414);
return x_465;
}
}
}
}
block_524:
{
lean_object* x_512; 
x_512 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_503, x_509, x_511);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_513, 6);
lean_inc_ref(x_514);
lean_dec(x_513);
x_515 = lean_ctor_get(x_512, 1);
lean_inc(x_515);
lean_dec_ref(x_512);
x_516 = lean_ctor_get(x_514, 2);
x_517 = lean_nat_dec_lt(x_502, x_516);
if (x_517 == 0)
{
lean_object* x_518; 
lean_dec_ref(x_514);
x_518 = l_outOfBounds___redArg(x_494);
x_413 = x_496;
x_414 = x_497;
x_415 = x_503;
x_416 = x_498;
x_417 = x_507;
x_418 = x_505;
x_419 = x_499;
x_420 = x_500;
x_421 = x_504;
x_422 = x_509;
x_423 = x_495;
x_424 = x_506;
x_425 = x_510;
x_426 = x_515;
x_427 = x_508;
x_428 = x_501;
x_429 = x_502;
x_430 = x_518;
goto block_488;
}
else
{
lean_object* x_519; 
x_519 = l_Lean_PersistentArray_get_x21___redArg(x_494, x_514, x_502);
x_413 = x_496;
x_414 = x_497;
x_415 = x_503;
x_416 = x_498;
x_417 = x_507;
x_418 = x_505;
x_419 = x_499;
x_420 = x_500;
x_421 = x_504;
x_422 = x_509;
x_423 = x_495;
x_424 = x_506;
x_425 = x_510;
x_426 = x_515;
x_427 = x_508;
x_428 = x_501;
x_429 = x_502;
x_430 = x_519;
goto block_488;
}
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
lean_dec(x_510);
lean_dec_ref(x_509);
lean_dec(x_508);
lean_dec_ref(x_507);
lean_dec(x_506);
lean_dec_ref(x_505);
lean_dec(x_504);
lean_dec(x_503);
lean_dec(x_502);
lean_dec_ref(x_501);
lean_dec(x_500);
lean_dec_ref(x_499);
lean_dec_ref(x_498);
lean_dec(x_497);
lean_dec_ref(x_496);
lean_dec_ref(x_495);
x_520 = lean_ctor_get(x_512, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_512, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 lean_ctor_release(x_512, 1);
 x_522 = x_512;
} else {
 lean_dec_ref(x_512);
 x_522 = lean_box(0);
}
if (lean_is_scalar(x_522)) {
 x_523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_523 = x_522;
}
lean_ctor_set(x_523, 0, x_520);
lean_ctor_set(x_523, 1, x_521);
return x_523;
}
}
block_602:
{
lean_object* x_534; lean_object* x_535; 
x_534 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_531);
x_535 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_534, x_525, x_526, x_527, x_528, x_529, x_530, x_531, x_532, x_533);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; uint8_t x_540; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
lean_dec_ref(x_535);
x_538 = lean_ctor_get(x_536, 0);
x_539 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
x_540 = l_Int_Linear_Poly_isUnsatDvd(x_538, x_539);
if (x_540 == 0)
{
uint8_t x_541; 
x_541 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_536);
if (x_541 == 0)
{
lean_dec(x_493);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_542; 
x_542 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_536, x_525, x_526, x_527, x_528, x_529, x_530, x_531, x_532, x_537);
lean_dec(x_532);
lean_dec_ref(x_531);
lean_dec(x_530);
lean_dec_ref(x_529);
lean_dec(x_528);
lean_dec_ref(x_527);
lean_dec(x_526);
lean_dec(x_525);
return x_542;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_inc_ref(x_539);
lean_inc(x_538);
x_543 = lean_ctor_get(x_539, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_539, 1);
lean_inc(x_544);
x_545 = lean_ctor_get(x_539, 2);
lean_inc_ref(x_545);
lean_inc(x_536);
x_546 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_536, x_525, x_531, x_537);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; uint8_t x_551; uint8_t x_552; uint8_t x_553; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec_ref(x_546);
lean_inc(x_544);
lean_inc(x_536);
x_549 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(x_549, 0, x_536);
lean_closure_set(x_549, 1, x_544);
lean_inc(x_544);
x_550 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(x_550, 0, x_544);
x_551 = 0;
x_552 = lean_unbox(x_547);
lean_dec(x_547);
x_553 = l_Lean_instBEqLBool_beq(x_552, x_551);
if (x_553 == 0)
{
x_495 = x_545;
x_496 = x_550;
x_497 = x_538;
x_498 = x_536;
x_499 = x_539;
x_500 = x_543;
x_501 = x_549;
x_502 = x_544;
x_503 = x_525;
x_504 = x_526;
x_505 = x_527;
x_506 = x_528;
x_507 = x_529;
x_508 = x_530;
x_509 = x_531;
x_510 = x_532;
x_511 = x_548;
goto block_524;
}
else
{
lean_object* x_554; 
lean_inc(x_544);
x_554 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_544, x_525, x_548);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; 
x_555 = lean_ctor_get(x_554, 1);
lean_inc(x_555);
lean_dec_ref(x_554);
x_495 = x_545;
x_496 = x_550;
x_497 = x_538;
x_498 = x_536;
x_499 = x_539;
x_500 = x_543;
x_501 = x_549;
x_502 = x_544;
x_503 = x_525;
x_504 = x_526;
x_505 = x_527;
x_506 = x_528;
x_507 = x_529;
x_508 = x_530;
x_509 = x_531;
x_510 = x_532;
x_511 = x_555;
goto block_524;
}
else
{
lean_dec_ref(x_550);
lean_dec_ref(x_549);
lean_dec_ref(x_545);
lean_dec(x_544);
lean_dec(x_543);
lean_dec_ref(x_539);
lean_dec(x_538);
lean_dec(x_536);
lean_dec(x_532);
lean_dec_ref(x_531);
lean_dec(x_530);
lean_dec_ref(x_529);
lean_dec(x_528);
lean_dec_ref(x_527);
lean_dec(x_526);
lean_dec(x_525);
return x_554;
}
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec_ref(x_545);
lean_dec(x_544);
lean_dec(x_543);
lean_dec_ref(x_539);
lean_dec(x_538);
lean_dec(x_536);
lean_dec(x_532);
lean_dec_ref(x_531);
lean_dec(x_530);
lean_dec_ref(x_529);
lean_dec(x_528);
lean_dec_ref(x_527);
lean_dec(x_526);
lean_dec(x_525);
x_556 = lean_ctor_get(x_546, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_546, 1);
lean_inc(x_557);
if (lean_is_exclusive(x_546)) {
 lean_ctor_release(x_546, 0);
 lean_ctor_release(x_546, 1);
 x_558 = x_546;
} else {
 lean_dec_ref(x_546);
 x_558 = lean_box(0);
}
if (lean_is_scalar(x_558)) {
 x_559 = lean_alloc_ctor(1, 2, 0);
} else {
 x_559 = x_558;
}
lean_ctor_set(x_559, 0, x_556);
lean_ctor_set(x_559, 1, x_557);
return x_559;
}
}
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; uint8_t x_563; 
lean_dec(x_528);
lean_dec_ref(x_527);
lean_dec(x_526);
x_560 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
x_561 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_560, x_531, x_537);
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_unbox(x_562);
lean_dec(x_562);
if (x_563 == 0)
{
lean_object* x_564; 
lean_dec(x_536);
lean_dec(x_532);
lean_dec_ref(x_531);
lean_dec(x_530);
lean_dec_ref(x_529);
lean_dec(x_525);
lean_dec(x_493);
x_564 = lean_ctor_get(x_561, 1);
lean_inc(x_564);
lean_dec_ref(x_561);
x_43 = x_564;
goto block_46;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_561, 1);
lean_inc(x_565);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 lean_ctor_release(x_561, 1);
 x_566 = x_561;
} else {
 lean_dec_ref(x_561);
 x_566 = lean_box(0);
}
x_567 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_536, x_525, x_531, x_565);
lean_dec(x_525);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_567, 1);
lean_inc(x_569);
lean_dec_ref(x_567);
x_570 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_566)) {
 x_571 = lean_alloc_ctor(7, 2, 0);
} else {
 x_571 = x_566;
 lean_ctor_set_tag(x_571, 7);
}
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_568);
if (lean_is_scalar(x_493)) {
 x_572 = lean_alloc_ctor(7, 2, 0);
} else {
 x_572 = x_493;
 lean_ctor_set_tag(x_572, 7);
}
lean_ctor_set(x_572, 0, x_571);
lean_ctor_set(x_572, 1, x_570);
x_573 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_560, x_572, x_529, x_530, x_531, x_532, x_569);
lean_dec(x_532);
lean_dec_ref(x_531);
lean_dec(x_530);
lean_dec_ref(x_529);
x_574 = lean_ctor_get(x_573, 1);
lean_inc(x_574);
lean_dec_ref(x_573);
x_43 = x_574;
goto block_46;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_dec(x_566);
lean_dec(x_532);
lean_dec_ref(x_531);
lean_dec(x_530);
lean_dec_ref(x_529);
lean_dec(x_493);
x_575 = lean_ctor_get(x_567, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_567, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 x_577 = x_567;
} else {
 lean_dec_ref(x_567);
 x_577 = lean_box(0);
}
if (lean_is_scalar(x_577)) {
 x_578 = lean_alloc_ctor(1, 2, 0);
} else {
 x_578 = x_577;
}
lean_ctor_set(x_578, 0, x_575);
lean_ctor_set(x_578, 1, x_576);
return x_578;
}
}
}
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; uint8_t x_582; 
x_579 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8;
x_580 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_579, x_531, x_537);
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_unbox(x_581);
lean_dec(x_581);
if (x_582 == 0)
{
lean_object* x_583; 
lean_dec(x_493);
x_583 = lean_ctor_get(x_580, 1);
lean_inc(x_583);
lean_dec_ref(x_580);
x_11 = x_536;
x_12 = x_525;
x_13 = x_526;
x_14 = x_527;
x_15 = x_528;
x_16 = x_529;
x_17 = x_530;
x_18 = x_531;
x_19 = x_532;
x_20 = x_583;
goto block_29;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_580, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_585 = x_580;
} else {
 lean_dec_ref(x_580);
 x_585 = lean_box(0);
}
lean_inc(x_536);
x_586 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_536, x_525, x_531, x_584);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
lean_dec_ref(x_586);
x_589 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_585)) {
 x_590 = lean_alloc_ctor(7, 2, 0);
} else {
 x_590 = x_585;
 lean_ctor_set_tag(x_590, 7);
}
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_587);
if (lean_is_scalar(x_493)) {
 x_591 = lean_alloc_ctor(7, 2, 0);
} else {
 x_591 = x_493;
 lean_ctor_set_tag(x_591, 7);
}
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_589);
x_592 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_579, x_591, x_529, x_530, x_531, x_532, x_588);
x_593 = lean_ctor_get(x_592, 1);
lean_inc(x_593);
lean_dec_ref(x_592);
x_11 = x_536;
x_12 = x_525;
x_13 = x_526;
x_14 = x_527;
x_15 = x_528;
x_16 = x_529;
x_17 = x_530;
x_18 = x_531;
x_19 = x_532;
x_20 = x_593;
goto block_29;
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_dec(x_585);
lean_dec(x_536);
lean_dec(x_532);
lean_dec_ref(x_531);
lean_dec(x_530);
lean_dec_ref(x_529);
lean_dec(x_528);
lean_dec_ref(x_527);
lean_dec(x_526);
lean_dec(x_525);
lean_dec(x_493);
x_594 = lean_ctor_get(x_586, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_586, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 x_596 = x_586;
} else {
 lean_dec_ref(x_586);
 x_596 = lean_box(0);
}
if (lean_is_scalar(x_596)) {
 x_597 = lean_alloc_ctor(1, 2, 0);
} else {
 x_597 = x_596;
}
lean_ctor_set(x_597, 0, x_594);
lean_ctor_set(x_597, 1, x_595);
return x_597;
}
}
}
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
lean_dec(x_532);
lean_dec_ref(x_531);
lean_dec(x_530);
lean_dec_ref(x_529);
lean_dec(x_528);
lean_dec_ref(x_527);
lean_dec(x_526);
lean_dec(x_525);
lean_dec(x_493);
x_598 = lean_ctor_get(x_535, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_535, 1);
lean_inc(x_599);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_600 = x_535;
} else {
 lean_dec_ref(x_535);
 x_600 = lean_box(0);
}
if (lean_is_scalar(x_600)) {
 x_601 = lean_alloc_ctor(1, 2, 0);
} else {
 x_601 = x_600;
}
lean_ctor_set(x_601, 0, x_598);
lean_ctor_set(x_601, 1, x_599);
return x_601;
}
}
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
lean_dec_ref(x_408);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_616 = lean_ctor_get(x_409, 1);
lean_inc(x_616);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_617 = x_409;
} else {
 lean_dec_ref(x_409);
 x_617 = lean_box(0);
}
x_618 = lean_box(0);
if (lean_is_scalar(x_617)) {
 x_619 = lean_alloc_ctor(0, 2, 0);
} else {
 x_619 = x_617;
}
lean_ctor_set(x_619, 0, x_618);
lean_ctor_set(x_619, 1, x_616);
return x_619;
}
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_dec_ref(x_408);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_620 = lean_ctor_get(x_409, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_409, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_622 = x_409;
} else {
 lean_dec_ref(x_409);
 x_622 = lean_box(0);
}
if (lean_is_scalar(x_622)) {
 x_623 = lean_alloc_ctor(1, 2, 0);
} else {
 x_623 = x_622;
}
lean_ctor_set(x_623, 0, x_620);
lean_ctor_set(x_623, 1, x_621);
return x_623;
}
}
else
{
lean_object* x_624; 
lean_dec_ref(x_404);
lean_dec(x_402);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_391);
lean_dec_ref(x_390);
lean_dec_ref(x_389);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_624 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_394, x_10);
return x_624;
}
}
block_29:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_11);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
return x_22;
}
}
block_42:
{
lean_object* x_38; 
x_38 = l_Int_Linear_Poly_updateOccs___redArg(x_30, x_32, x_33, x_34, x_35, x_36, x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_41 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_40, x_31, x_32, x_39);
lean_dec(x_32);
return x_41;
}
else
{
lean_dec(x_32);
lean_dec_ref(x_31);
return x_38;
}
}
block_46:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_12);
x_13 = l_Int_Linear_Poly_normCommRing_x3f(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_11);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec_ref(x_13);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_21);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("non-linear divisibility constraint found", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_not_dvd", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_eagerReflBoolTrue;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; uint8_t x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_22 = l_Lean_Expr_cleanupAnnotations(x_16);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_21;
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_inc_ref(x_22);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_21;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_inc_ref(x_24);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_21;
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_inc_ref(x_26);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_21;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_32 = l_Lean_Expr_isConstOf(x_30, x_31);
lean_dec_ref(x_30);
if (x_32 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_21;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_18);
x_33 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_33);
lean_dec_ref(x_26);
x_34 = l_Lean_Meta_isInstDvdInt___redArg(x_33, x_7, x_17);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
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
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec_ref(x_34);
x_44 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_44);
lean_dec_ref(x_24);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_44);
x_45 = l_Lean_Meta_getIntValue_x3f(x_44, x_6, x_7, x_8, x_9, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_44);
lean_dec_ref(x_22);
lean_dec(x_2);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_49, sizeof(void*)*8 + 11);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec_ref(x_48);
x_11 = x_51;
goto block_14;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec_ref(x_48);
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
x_54 = l_Lean_indentExpr(x_1);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Meta_Grind_reportIssue(x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec_ref(x_58);
x_11 = x_59;
goto block_14;
}
else
{
return x_58;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
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
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_45, 1);
lean_inc(x_64);
lean_dec_ref(x_45);
x_65 = !lean_is_exclusive(x_46);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_1);
x_67 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_64);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_free_object(x_46);
lean_dec(x_66);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec_ref(x_67);
x_71 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_71);
lean_dec_ref(x_22);
lean_inc_ref(x_1);
x_72 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_dec_ref(x_71);
lean_dec_ref(x_44);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_72, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_72, 0, x_77);
return x_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_dec_ref(x_72);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_82 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec_ref(x_82);
x_85 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_86 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
x_87 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_83);
x_88 = l_Lean_mkApp4(x_85, x_44, x_71, x_86, x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Lean_Meta_Grind_pushNewFact(x_88, x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_84);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec_ref(x_71);
lean_dec_ref(x_44);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_91 = !lean_is_exclusive(x_82);
if (x_91 == 0)
{
return x_82;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_82, 0);
x_93 = lean_ctor_get(x_82, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_82);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_71);
lean_dec_ref(x_44);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_72);
if (x_95 == 0)
{
return x_72;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_72, 0);
x_97 = lean_ctor_get(x_72, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_72);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec_ref(x_44);
x_99 = lean_ctor_get(x_67, 1);
lean_inc(x_99);
lean_dec_ref(x_67);
x_100 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_100);
lean_dec_ref(x_22);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_101 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_100, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
lean_ctor_set_tag(x_46, 0);
lean_ctor_set(x_46, 0, x_1);
x_104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_104, 0, x_66);
lean_ctor_set(x_104, 1, x_102);
lean_ctor_set(x_104, 2, x_46);
x_105 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_103);
return x_105;
}
else
{
uint8_t x_106; 
lean_free_object(x_46);
lean_dec(x_66);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_106 = !lean_is_exclusive(x_101);
if (x_106 == 0)
{
return x_101;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_101, 0);
x_108 = lean_ctor_get(x_101, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_101);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_free_object(x_46);
lean_dec(x_66);
lean_dec_ref(x_44);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_110 = !lean_is_exclusive(x_67);
if (x_110 == 0)
{
return x_67;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_67, 0);
x_112 = lean_ctor_get(x_67, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_67);
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
x_114 = lean_ctor_get(x_46, 0);
lean_inc(x_114);
lean_dec(x_46);
lean_inc_ref(x_1);
x_115 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_64);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_114);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec_ref(x_115);
x_119 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_119);
lean_dec_ref(x_22);
lean_inc_ref(x_1);
x_120 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec_ref(x_119);
lean_dec_ref(x_44);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_124 = x_120;
} else {
 lean_dec_ref(x_120);
 x_124 = lean_box(0);
}
x_125 = lean_box(0);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_120, 1);
lean_inc(x_127);
lean_dec_ref(x_120);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_128 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec_ref(x_128);
x_131 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_132 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
x_133 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_129);
x_134 = l_Lean_mkApp4(x_131, x_44, x_119, x_132, x_133);
x_135 = lean_unsigned_to_nat(0u);
x_136 = l_Lean_Meta_Grind_pushNewFact(x_134, x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_130);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec_ref(x_119);
lean_dec_ref(x_44);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_128, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_139 = x_128;
} else {
 lean_dec_ref(x_128);
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
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec_ref(x_119);
lean_dec_ref(x_44);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_141 = lean_ctor_get(x_120, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_120, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_143 = x_120;
} else {
 lean_dec_ref(x_120);
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
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec_ref(x_44);
x_145 = lean_ctor_get(x_115, 1);
lean_inc(x_145);
lean_dec_ref(x_115);
x_146 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_146);
lean_dec_ref(x_22);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_147 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_146, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_145);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec_ref(x_147);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_1);
x_151 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_151, 0, x_114);
lean_ctor_set(x_151, 1, x_148);
lean_ctor_set(x_151, 2, x_150);
x_152 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_151, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_149);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_114);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_153 = lean_ctor_get(x_147, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_147, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_155 = x_147;
} else {
 lean_dec_ref(x_147);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_114);
lean_dec_ref(x_44);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_157 = lean_ctor_get(x_115, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_115, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_159 = x_115;
} else {
 lean_dec_ref(x_115);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
}
else
{
uint8_t x_161; 
lean_dec_ref(x_44);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_161 = !lean_is_exclusive(x_45);
if (x_161 == 0)
{
return x_45;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_45, 0);
x_163 = lean_ctor_get(x_45, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_45);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
else
{
uint8_t x_165; 
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_165 = !lean_is_exclusive(x_34);
if (x_165 == 0)
{
return x_34;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_34, 0);
x_167 = lean_ctor_get(x_34, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_34);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
}
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_169; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_169 = !lean_is_exclusive(x_15);
if (x_169 == 0)
{
return x_15;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_15, 0);
x_171 = lean_ctor_get(x_15, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_15);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
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
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_pos_of_not_dvd", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ToInt", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_dvd", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_19; uint8_t x_20; 
lean_inc_ref(x_1);
x_19 = l_Lean_Expr_cleanupAnnotations(x_1);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_inc_ref(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_inc_ref(x_21);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_inc_ref(x_23);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
lean_dec_ref(x_27);
if (x_29 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_23);
x_31 = l_Lean_Meta_isInstDvdNat___redArg(x_30, x_7, x_10);
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
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec_ref(x_31);
x_41 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_41);
lean_dec_ref(x_21);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_42 = l_Lean_Meta_getNatValue_x3f(x_41, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_41);
lean_dec_ref(x_19);
lean_dec(x_2);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_46, sizeof(void*)*8 + 11);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec_ref(x_45);
x_15 = x_48;
goto block_18;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec_ref(x_45);
x_50 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
x_51 = l_Lean_indentExpr(x_1);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Meta_Grind_reportIssue(x_54, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_49);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_15 = x_56;
goto block_18;
}
else
{
return x_55;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_45);
if (x_57 == 0)
{
return x_45;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_45, 0);
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_45);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_42, 1);
lean_inc(x_61);
lean_dec_ref(x_42);
x_62 = lean_ctor_get(x_43, 0);
lean_inc(x_62);
lean_dec_ref(x_43);
lean_inc_ref(x_1);
x_63 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_62);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec_ref(x_63);
x_67 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_67);
lean_dec_ref(x_19);
lean_inc_ref(x_1);
x_68 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
uint8_t x_71; 
lean_dec_ref(x_67);
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_68, 0);
lean_dec(x_72);
x_73 = lean_box(0);
lean_ctor_set(x_68, 0, x_73);
return x_68;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
lean_dec(x_68);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_68, 1);
lean_inc(x_77);
lean_dec_ref(x_68);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_78 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec_ref(x_78);
x_81 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_82 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_79);
x_83 = l_Lean_mkApp3(x_81, x_41, x_67, x_82);
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Lean_Meta_Grind_pushNewFact(x_83, x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_80);
return x_85;
}
else
{
uint8_t x_86; 
lean_dec_ref(x_67);
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_86 = !lean_is_exclusive(x_78);
if (x_86 == 0)
{
return x_78;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_78, 0);
x_88 = lean_ctor_get(x_78, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_78);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec_ref(x_67);
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_90 = !lean_is_exclusive(x_68);
if (x_90 == 0)
{
return x_68;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_68, 0);
x_92 = lean_ctor_get(x_68, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_68);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_63, 1);
lean_inc(x_94);
lean_dec_ref(x_63);
x_95 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_95);
lean_dec_ref(x_19);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_41);
x_96 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec_ref(x_96);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_95);
x_101 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_95, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_98);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_103);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec_ref(x_106);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_104);
x_109 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_104, x_107, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec_ref(x_109);
x_112 = l_Int_Linear_Expr_norm(x_110);
x_113 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
x_114 = l_Lean_mkApp6(x_113, x_41, x_95, x_99, x_104, x_100, x_105);
lean_inc(x_62);
x_115 = lean_nat_to_int(x_62);
x_116 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_116, 0, x_1);
lean_ctor_set(x_116, 1, x_114);
lean_ctor_set(x_116, 2, x_62);
lean_ctor_set(x_116, 3, x_110);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_112);
lean_ctor_set(x_117, 2, x_116);
x_118 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_117, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_111);
return x_118;
}
else
{
uint8_t x_119; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_100);
lean_dec(x_99);
lean_dec_ref(x_95);
lean_dec(x_62);
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_119 = !lean_is_exclusive(x_109);
if (x_119 == 0)
{
return x_109;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_109, 0);
x_121 = lean_ctor_get(x_109, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_109);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_100);
lean_dec(x_99);
lean_dec_ref(x_95);
lean_dec(x_62);
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_123 = !lean_is_exclusive(x_106);
if (x_123 == 0)
{
return x_106;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_106, 0);
x_125 = lean_ctor_get(x_106, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_106);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec_ref(x_95);
lean_dec(x_62);
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_127 = !lean_is_exclusive(x_101);
if (x_127 == 0)
{
return x_101;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_101, 0);
x_129 = lean_ctor_get(x_101, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_101);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_dec_ref(x_95);
lean_dec(x_62);
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_131 = !lean_is_exclusive(x_96);
if (x_131 == 0)
{
return x_96;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_96, 0);
x_133 = lean_ctor_get(x_96, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_96);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_62);
lean_dec_ref(x_41);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_135 = !lean_is_exclusive(x_63);
if (x_135 == 0)
{
return x_63;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_63, 0);
x_137 = lean_ctor_get(x_63, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_63);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
else
{
uint8_t x_139; 
lean_dec_ref(x_41);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_139 = !lean_is_exclusive(x_42);
if (x_139 == 0)
{
return x_42;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_42, 0);
x_141 = lean_ctor_get(x_42, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_42);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
else
{
uint8_t x_143; 
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_143 = !lean_is_exclusive(x_31);
if (x_143 == 0)
{
return x_31;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_31, 0);
x_145 = lean_ctor_get(x_31, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_31);
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
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*8 + 19);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec_ref(x_11);
lean_inc_ref(x_1);
x_21 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_28 = l_Lean_Expr_cleanupAnnotations(x_22);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_27;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_27;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_dec_ref(x_32);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_27;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_32);
x_35 = l_Lean_Expr_isApp(x_34);
if (x_35 == 0)
{
lean_dec_ref(x_34);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_27;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc_ref(x_34);
x_36 = l_Lean_Expr_appFnCleanup___redArg(x_34);
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_38 = l_Lean_Expr_isConstOf(x_36, x_37);
lean_dec_ref(x_36);
if (x_38 == 0)
{
lean_dec_ref(x_34);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_27;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_24);
x_39 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_39);
lean_dec_ref(x_34);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0;
x_41 = l_Lean_Expr_isConstOf(x_39, x_40);
lean_dec_ref(x_39);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
return x_43;
}
}
}
}
}
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8_t x_44; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_21);
if (x_44 == 0)
{
return x_21;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_21, 0);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_21);
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
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
return x_11;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1830001947____hygCtx___hyg_8_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Int(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin, lean_io_mk_world());
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
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0();
l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1);
l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0);
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
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1830001947____hygCtx___hyg_8_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

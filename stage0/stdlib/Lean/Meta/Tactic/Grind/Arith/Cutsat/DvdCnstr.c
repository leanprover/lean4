// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Simp.Arith.Int Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing Lean.Meta.NatInstTesters
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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static double l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__6;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
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
lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstDvdNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5;
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
x_36 = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(x_2, x_6, x_18);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
lean_inc_ref(x_3);
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_3, x_6, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
lean_inc_ref(x_5);
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_5, x_6, x_41);
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
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_1, 1);
x_28 = l_Int_Linear_Poly_findVarToSubst___redArg(x_27, x_2, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_free_object(x_8);
lean_dec_ref(x_25);
lean_dec(x_24);
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
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
lean_ctor_set(x_28, 0, x_1);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec_ref(x_29);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec_ref(x_28);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_15, x_41);
lean_dec(x_15);
lean_ctor_set(x_8, 3, x_42);
x_43 = l_Int_Linear_Poly_coeff(x_40, x_39);
x_44 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_43, x_39, x_36, x_38, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_38);
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
lean_free_object(x_8);
lean_dec_ref(x_25);
lean_dec(x_24);
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
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_1);
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
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_1, 1);
x_71 = l_Int_Linear_Poly_findVarToSubst___redArg(x_70, x_2, x_10);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_68);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
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
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
lean_dec_ref(x_72);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_71, 1);
lean_inc(x_79);
lean_dec_ref(x_71);
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
lean_dec(x_76);
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_ctor_get(x_78, 0);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_add(x_56, x_83);
lean_dec(x_56);
x_85 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_85, 0, x_53);
lean_ctor_set(x_85, 1, x_54);
lean_ctor_set(x_85, 2, x_55);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set(x_85, 4, x_57);
lean_ctor_set(x_85, 5, x_58);
lean_ctor_set(x_85, 6, x_59);
lean_ctor_set(x_85, 7, x_60);
lean_ctor_set(x_85, 8, x_61);
lean_ctor_set(x_85, 9, x_62);
lean_ctor_set(x_85, 10, x_63);
lean_ctor_set(x_85, 11, x_64);
lean_ctor_set(x_85, 12, x_66);
lean_ctor_set(x_85, 13, x_68);
lean_ctor_set_uint8(x_85, sizeof(void*)*14, x_65);
lean_ctor_set_uint8(x_85, sizeof(void*)*14 + 1, x_67);
x_86 = l_Int_Linear_Poly_coeff(x_82, x_81);
x_87 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_86, x_81, x_78, x_80, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_85, x_9, x_79);
lean_dec(x_80);
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
x_8 = x_85;
x_10 = x_89;
goto _start;
}
else
{
lean_dec_ref(x_85);
return x_87;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_68);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_1);
x_91 = lean_ctor_get(x_71, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_71, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_93 = x_71;
} else {
 lean_dec_ref(x_71);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_185; uint8_t x_189; 
x_189 = !lean_is_exclusive(x_8);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_190 = lean_ctor_get(x_8, 0);
x_191 = lean_ctor_get(x_8, 1);
x_192 = lean_ctor_get(x_8, 2);
x_193 = lean_ctor_get(x_8, 3);
x_194 = lean_ctor_get(x_8, 4);
x_195 = lean_ctor_get(x_8, 5);
x_196 = lean_ctor_get(x_8, 6);
x_197 = lean_ctor_get(x_8, 7);
x_198 = lean_ctor_get(x_8, 8);
x_199 = lean_ctor_get(x_8, 9);
x_200 = lean_ctor_get(x_8, 10);
x_201 = lean_ctor_get(x_8, 11);
x_202 = lean_ctor_get(x_8, 12);
x_203 = lean_ctor_get(x_8, 13);
x_204 = lean_nat_dec_eq(x_193, x_194);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; uint8_t x_207; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_unbox(x_206);
lean_dec(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_742; 
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_dec_ref(x_205);
x_209 = lean_unsigned_to_nat(1u);
x_210 = lean_nat_add(x_193, x_209);
lean_dec(x_193);
lean_ctor_set(x_8, 3, x_210);
x_606 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_607 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_606, x_8, x_208);
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 lean_ctor_release(x_607, 1);
 x_610 = x_607;
} else {
 lean_dec_ref(x_607);
 x_610 = lean_box(0);
}
x_611 = lean_box(0);
x_742 = lean_unbox(x_608);
lean_dec(x_608);
if (x_742 == 0)
{
x_640 = x_2;
x_641 = x_3;
x_642 = x_4;
x_643 = x_5;
x_644 = x_6;
x_645 = x_7;
x_646 = x_8;
x_647 = x_9;
x_648 = x_609;
goto block_741;
}
else
{
lean_object* x_743; 
lean_inc_ref(x_1);
x_743 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_609);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
lean_dec_ref(x_743);
x_746 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_747 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_747, 0, x_746);
lean_ctor_set(x_747, 1, x_744);
x_748 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_748, 0, x_747);
lean_ctor_set(x_748, 1, x_746);
x_749 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_606, x_748, x_6, x_7, x_8, x_9, x_745);
x_750 = lean_ctor_get(x_749, 1);
lean_inc(x_750);
lean_dec_ref(x_749);
x_640 = x_2;
x_641 = x_3;
x_642 = x_4;
x_643 = x_5;
x_644 = x_6;
x_645 = x_7;
x_646 = x_8;
x_647 = x_9;
x_648 = x_750;
goto block_741;
}
else
{
uint8_t x_751; 
lean_dec(x_610);
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_751 = !lean_is_exclusive(x_743);
if (x_751 == 0)
{
return x_743;
}
else
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; 
x_752 = lean_ctor_get(x_743, 0);
x_753 = lean_ctor_get(x_743, 1);
lean_inc(x_753);
lean_inc(x_752);
lean_dec(x_743);
x_754 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_754, 0, x_752);
lean_ctor_set(x_754, 1, x_753);
return x_754;
}
}
}
block_605:
{
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
lean_dec_ref(x_224);
lean_dec_ref(x_222);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_214);
lean_dec(x_211);
x_227 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_228 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_227, x_212, x_213);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_unbox(x_229);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
lean_dec_ref(x_228);
x_11 = x_215;
x_12 = x_216;
x_13 = x_225;
x_14 = x_223;
x_15 = x_221;
x_16 = x_217;
x_17 = x_212;
x_18 = x_220;
x_19 = x_231;
goto block_165;
}
else
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_228);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_228, 1);
x_234 = lean_ctor_get(x_228, 0);
lean_dec(x_234);
lean_inc_ref(x_215);
x_235 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_215, x_223, x_233);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec_ref(x_235);
x_238 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_228, 7);
lean_ctor_set(x_228, 1, x_236);
lean_ctor_set(x_228, 0, x_238);
x_239 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_239, 0, x_228);
lean_ctor_set(x_239, 1, x_238);
x_240 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_227, x_239, x_221, x_217, x_212, x_220, x_237);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec_ref(x_240);
x_11 = x_215;
x_12 = x_216;
x_13 = x_225;
x_14 = x_223;
x_15 = x_221;
x_16 = x_217;
x_17 = x_212;
x_18 = x_220;
x_19 = x_241;
goto block_165;
}
else
{
uint8_t x_242; 
lean_free_object(x_228);
lean_dec_ref(x_225);
lean_dec(x_223);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec_ref(x_212);
x_242 = !lean_is_exclusive(x_235);
if (x_242 == 0)
{
return x_235;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_235, 0);
x_244 = lean_ctor_get(x_235, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_235);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_228, 1);
lean_inc(x_246);
lean_dec(x_228);
lean_inc_ref(x_215);
x_247 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_215, x_223, x_246);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec_ref(x_247);
x_250 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_251 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_248);
x_252 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
x_253 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_227, x_252, x_221, x_217, x_212, x_220, x_249);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec_ref(x_253);
x_11 = x_215;
x_12 = x_216;
x_13 = x_225;
x_14 = x_223;
x_15 = x_221;
x_16 = x_217;
x_17 = x_212;
x_18 = x_220;
x_19 = x_254;
goto block_165;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec_ref(x_225);
lean_dec(x_223);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec_ref(x_212);
x_255 = lean_ctor_get(x_247, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_247, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_257 = x_247;
} else {
 lean_dec_ref(x_247);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
}
}
else
{
lean_object* x_259; lean_object* x_260; 
lean_dec_ref(x_225);
x_259 = lean_ctor_get(x_226, 0);
lean_inc(x_259);
lean_dec_ref(x_226);
x_260 = lean_ctor_get(x_259, 1);
lean_inc_ref(x_260);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; 
lean_dec_ref(x_260);
lean_dec_ref(x_224);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_216);
lean_dec_ref(x_215);
x_261 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_259, x_223, x_211, x_222, x_214, x_221, x_217, x_212, x_220, x_213);
lean_dec(x_220);
lean_dec_ref(x_212);
lean_dec(x_217);
lean_dec_ref(x_221);
lean_dec(x_214);
lean_dec_ref(x_222);
lean_dec(x_211);
lean_dec(x_223);
return x_261;
}
else
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_260);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_263 = lean_ctor_get(x_259, 0);
x_264 = lean_ctor_get(x_260, 0);
x_265 = lean_ctor_get(x_260, 2);
x_266 = lean_ctor_get(x_260, 1);
lean_dec(x_266);
x_267 = lean_int_mul(x_218, x_263);
x_268 = lean_int_mul(x_264, x_219);
x_269 = l_Lean_Meta_Grind_Arith_gcdExt(x_267, x_268);
lean_dec(x_268);
lean_dec(x_267);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
lean_dec_ref(x_269);
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_dec(x_270);
x_274 = lean_st_ref_take(x_223, x_213);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_275, 14);
lean_inc_ref(x_276);
x_277 = lean_ctor_get(x_276, 1);
lean_inc_ref(x_277);
x_278 = lean_ctor_get(x_274, 1);
lean_inc(x_278);
lean_dec_ref(x_274);
x_279 = !lean_is_exclusive(x_275);
if (x_279 == 0)
{
lean_object* x_280; uint8_t x_281; 
x_280 = lean_ctor_get(x_275, 14);
lean_dec(x_280);
x_281 = !lean_is_exclusive(x_276);
if (x_281 == 0)
{
lean_object* x_282; uint8_t x_283; 
x_282 = lean_ctor_get(x_276, 1);
lean_dec(x_282);
x_283 = !lean_is_exclusive(x_277);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_284 = lean_ctor_get(x_277, 6);
x_285 = lean_box(0);
x_286 = l_Lean_PersistentArray_set___redArg(x_284, x_216, x_285);
lean_ctor_set(x_277, 6, x_286);
x_287 = lean_st_ref_set(x_223, x_275, x_278);
x_288 = !lean_is_exclusive(x_287);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_289 = lean_ctor_get(x_287, 1);
x_290 = lean_ctor_get(x_287, 0);
lean_dec(x_290);
x_291 = lean_int_mul(x_272, x_263);
lean_dec(x_272);
lean_inc_ref(x_224);
x_292 = l_Int_Linear_Poly_mul(x_224, x_291);
lean_dec(x_291);
x_293 = lean_int_mul(x_273, x_219);
lean_dec(x_273);
lean_inc_ref(x_265);
x_294 = l_Int_Linear_Poly_mul(x_265, x_293);
lean_dec(x_293);
x_295 = lean_int_mul(x_219, x_263);
lean_dec(x_219);
x_296 = l_Int_Linear_Poly_combine(x_292, x_294);
lean_inc(x_271);
lean_ctor_set(x_260, 2, x_296);
lean_ctor_set(x_260, 1, x_216);
lean_ctor_set(x_260, 0, x_271);
lean_inc(x_259);
lean_inc_ref(x_215);
lean_ctor_set_tag(x_287, 4);
lean_ctor_set(x_287, 1, x_259);
lean_ctor_set(x_287, 0, x_215);
x_297 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_260);
lean_ctor_set(x_297, 2, x_287);
lean_inc(x_220);
lean_inc_ref(x_212);
lean_inc(x_217);
lean_inc_ref(x_221);
lean_inc(x_214);
lean_inc_ref(x_222);
lean_inc(x_211);
lean_inc(x_223);
x_298 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_297, x_223, x_211, x_222, x_214, x_221, x_217, x_212, x_220, x_289);
if (lean_obj_tag(x_298) == 0)
{
uint8_t x_299; 
x_299 = !lean_is_exclusive(x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_300 = lean_ctor_get(x_298, 1);
x_301 = lean_ctor_get(x_298, 0);
lean_dec(x_301);
x_302 = l_Int_Linear_Poly_mul(x_224, x_264);
lean_dec(x_264);
x_303 = lean_int_neg(x_218);
lean_dec(x_218);
x_304 = l_Int_Linear_Poly_mul(x_265, x_303);
lean_dec(x_303);
x_305 = l_Int_Linear_Poly_combine(x_302, x_304);
lean_inc(x_259);
lean_ctor_set_tag(x_298, 5);
lean_ctor_set(x_298, 1, x_259);
lean_ctor_set(x_298, 0, x_215);
x_306 = !lean_is_exclusive(x_259);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_259, 2);
lean_dec(x_307);
x_308 = lean_ctor_get(x_259, 1);
lean_dec(x_308);
x_309 = lean_ctor_get(x_259, 0);
lean_dec(x_309);
lean_ctor_set(x_259, 2, x_298);
lean_ctor_set(x_259, 1, x_305);
lean_ctor_set(x_259, 0, x_271);
x_1 = x_259;
x_2 = x_223;
x_3 = x_211;
x_4 = x_222;
x_5 = x_214;
x_6 = x_221;
x_7 = x_217;
x_8 = x_212;
x_9 = x_220;
x_10 = x_300;
goto _start;
}
else
{
lean_object* x_311; 
lean_dec(x_259);
x_311 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_311, 0, x_271);
lean_ctor_set(x_311, 1, x_305);
lean_ctor_set(x_311, 2, x_298);
x_1 = x_311;
x_2 = x_223;
x_3 = x_211;
x_4 = x_222;
x_5 = x_214;
x_6 = x_221;
x_7 = x_217;
x_8 = x_212;
x_9 = x_220;
x_10 = x_300;
goto _start;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_313 = lean_ctor_get(x_298, 1);
lean_inc(x_313);
lean_dec(x_298);
x_314 = l_Int_Linear_Poly_mul(x_224, x_264);
lean_dec(x_264);
x_315 = lean_int_neg(x_218);
lean_dec(x_218);
x_316 = l_Int_Linear_Poly_mul(x_265, x_315);
lean_dec(x_315);
x_317 = l_Int_Linear_Poly_combine(x_314, x_316);
lean_inc(x_259);
x_318 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_318, 0, x_215);
lean_ctor_set(x_318, 1, x_259);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 x_319 = x_259;
} else {
 lean_dec_ref(x_259);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(0, 3, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_271);
lean_ctor_set(x_320, 1, x_317);
lean_ctor_set(x_320, 2, x_318);
x_1 = x_320;
x_2 = x_223;
x_3 = x_211;
x_4 = x_222;
x_5 = x_214;
x_6 = x_221;
x_7 = x_217;
x_8 = x_212;
x_9 = x_220;
x_10 = x_313;
goto _start;
}
}
else
{
lean_dec(x_271);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec(x_259);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_217);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec_ref(x_212);
lean_dec(x_211);
return x_298;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_322 = lean_ctor_get(x_287, 1);
lean_inc(x_322);
lean_dec(x_287);
x_323 = lean_int_mul(x_272, x_263);
lean_dec(x_272);
lean_inc_ref(x_224);
x_324 = l_Int_Linear_Poly_mul(x_224, x_323);
lean_dec(x_323);
x_325 = lean_int_mul(x_273, x_219);
lean_dec(x_273);
lean_inc_ref(x_265);
x_326 = l_Int_Linear_Poly_mul(x_265, x_325);
lean_dec(x_325);
x_327 = lean_int_mul(x_219, x_263);
lean_dec(x_219);
x_328 = l_Int_Linear_Poly_combine(x_324, x_326);
lean_inc(x_271);
lean_ctor_set(x_260, 2, x_328);
lean_ctor_set(x_260, 1, x_216);
lean_ctor_set(x_260, 0, x_271);
lean_inc(x_259);
lean_inc_ref(x_215);
x_329 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_329, 0, x_215);
lean_ctor_set(x_329, 1, x_259);
x_330 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_260);
lean_ctor_set(x_330, 2, x_329);
lean_inc(x_220);
lean_inc_ref(x_212);
lean_inc(x_217);
lean_inc_ref(x_221);
lean_inc(x_214);
lean_inc_ref(x_222);
lean_inc(x_211);
lean_inc(x_223);
x_331 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_330, x_223, x_211, x_222, x_214, x_221, x_217, x_212, x_220, x_322);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_333 = x_331;
} else {
 lean_dec_ref(x_331);
 x_333 = lean_box(0);
}
x_334 = l_Int_Linear_Poly_mul(x_224, x_264);
lean_dec(x_264);
x_335 = lean_int_neg(x_218);
lean_dec(x_218);
x_336 = l_Int_Linear_Poly_mul(x_265, x_335);
lean_dec(x_335);
x_337 = l_Int_Linear_Poly_combine(x_334, x_336);
lean_inc(x_259);
if (lean_is_scalar(x_333)) {
 x_338 = lean_alloc_ctor(5, 2, 0);
} else {
 x_338 = x_333;
 lean_ctor_set_tag(x_338, 5);
}
lean_ctor_set(x_338, 0, x_215);
lean_ctor_set(x_338, 1, x_259);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 x_339 = x_259;
} else {
 lean_dec_ref(x_259);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(0, 3, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_271);
lean_ctor_set(x_340, 1, x_337);
lean_ctor_set(x_340, 2, x_338);
x_1 = x_340;
x_2 = x_223;
x_3 = x_211;
x_4 = x_222;
x_5 = x_214;
x_6 = x_221;
x_7 = x_217;
x_8 = x_212;
x_9 = x_220;
x_10 = x_332;
goto _start;
}
else
{
lean_dec(x_271);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec(x_259);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_217);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec_ref(x_212);
lean_dec(x_211);
return x_331;
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_342 = lean_ctor_get(x_277, 0);
x_343 = lean_ctor_get(x_277, 1);
x_344 = lean_ctor_get(x_277, 2);
x_345 = lean_ctor_get(x_277, 3);
x_346 = lean_ctor_get(x_277, 4);
x_347 = lean_ctor_get(x_277, 5);
x_348 = lean_ctor_get(x_277, 6);
x_349 = lean_ctor_get(x_277, 7);
x_350 = lean_ctor_get(x_277, 8);
x_351 = lean_ctor_get(x_277, 9);
x_352 = lean_ctor_get(x_277, 10);
x_353 = lean_ctor_get(x_277, 11);
x_354 = lean_ctor_get(x_277, 12);
x_355 = lean_ctor_get(x_277, 13);
x_356 = lean_ctor_get(x_277, 14);
x_357 = lean_ctor_get_uint8(x_277, sizeof(void*)*22);
x_358 = lean_ctor_get(x_277, 15);
x_359 = lean_ctor_get(x_277, 16);
x_360 = lean_ctor_get(x_277, 17);
x_361 = lean_ctor_get(x_277, 18);
x_362 = lean_ctor_get(x_277, 19);
x_363 = lean_ctor_get(x_277, 20);
x_364 = lean_ctor_get_uint8(x_277, sizeof(void*)*22 + 1);
x_365 = lean_ctor_get(x_277, 21);
lean_inc(x_365);
lean_inc(x_363);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_356);
lean_inc(x_355);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_352);
lean_inc(x_351);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_277);
x_366 = lean_box(0);
x_367 = l_Lean_PersistentArray_set___redArg(x_348, x_216, x_366);
x_368 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_368, 0, x_342);
lean_ctor_set(x_368, 1, x_343);
lean_ctor_set(x_368, 2, x_344);
lean_ctor_set(x_368, 3, x_345);
lean_ctor_set(x_368, 4, x_346);
lean_ctor_set(x_368, 5, x_347);
lean_ctor_set(x_368, 6, x_367);
lean_ctor_set(x_368, 7, x_349);
lean_ctor_set(x_368, 8, x_350);
lean_ctor_set(x_368, 9, x_351);
lean_ctor_set(x_368, 10, x_352);
lean_ctor_set(x_368, 11, x_353);
lean_ctor_set(x_368, 12, x_354);
lean_ctor_set(x_368, 13, x_355);
lean_ctor_set(x_368, 14, x_356);
lean_ctor_set(x_368, 15, x_358);
lean_ctor_set(x_368, 16, x_359);
lean_ctor_set(x_368, 17, x_360);
lean_ctor_set(x_368, 18, x_361);
lean_ctor_set(x_368, 19, x_362);
lean_ctor_set(x_368, 20, x_363);
lean_ctor_set(x_368, 21, x_365);
lean_ctor_set_uint8(x_368, sizeof(void*)*22, x_357);
lean_ctor_set_uint8(x_368, sizeof(void*)*22 + 1, x_364);
lean_ctor_set(x_276, 1, x_368);
x_369 = lean_st_ref_set(x_223, x_275, x_278);
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_371 = x_369;
} else {
 lean_dec_ref(x_369);
 x_371 = lean_box(0);
}
x_372 = lean_int_mul(x_272, x_263);
lean_dec(x_272);
lean_inc_ref(x_224);
x_373 = l_Int_Linear_Poly_mul(x_224, x_372);
lean_dec(x_372);
x_374 = lean_int_mul(x_273, x_219);
lean_dec(x_273);
lean_inc_ref(x_265);
x_375 = l_Int_Linear_Poly_mul(x_265, x_374);
lean_dec(x_374);
x_376 = lean_int_mul(x_219, x_263);
lean_dec(x_219);
x_377 = l_Int_Linear_Poly_combine(x_373, x_375);
lean_inc(x_271);
lean_ctor_set(x_260, 2, x_377);
lean_ctor_set(x_260, 1, x_216);
lean_ctor_set(x_260, 0, x_271);
lean_inc(x_259);
lean_inc_ref(x_215);
if (lean_is_scalar(x_371)) {
 x_378 = lean_alloc_ctor(4, 2, 0);
} else {
 x_378 = x_371;
 lean_ctor_set_tag(x_378, 4);
}
lean_ctor_set(x_378, 0, x_215);
lean_ctor_set(x_378, 1, x_259);
x_379 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_379, 0, x_376);
lean_ctor_set(x_379, 1, x_260);
lean_ctor_set(x_379, 2, x_378);
lean_inc(x_220);
lean_inc_ref(x_212);
lean_inc(x_217);
lean_inc_ref(x_221);
lean_inc(x_214);
lean_inc_ref(x_222);
lean_inc(x_211);
lean_inc(x_223);
x_380 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_379, x_223, x_211, x_222, x_214, x_221, x_217, x_212, x_220, x_370);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_382 = x_380;
} else {
 lean_dec_ref(x_380);
 x_382 = lean_box(0);
}
x_383 = l_Int_Linear_Poly_mul(x_224, x_264);
lean_dec(x_264);
x_384 = lean_int_neg(x_218);
lean_dec(x_218);
x_385 = l_Int_Linear_Poly_mul(x_265, x_384);
lean_dec(x_384);
x_386 = l_Int_Linear_Poly_combine(x_383, x_385);
lean_inc(x_259);
if (lean_is_scalar(x_382)) {
 x_387 = lean_alloc_ctor(5, 2, 0);
} else {
 x_387 = x_382;
 lean_ctor_set_tag(x_387, 5);
}
lean_ctor_set(x_387, 0, x_215);
lean_ctor_set(x_387, 1, x_259);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 x_388 = x_259;
} else {
 lean_dec_ref(x_259);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(0, 3, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_271);
lean_ctor_set(x_389, 1, x_386);
lean_ctor_set(x_389, 2, x_387);
x_1 = x_389;
x_2 = x_223;
x_3 = x_211;
x_4 = x_222;
x_5 = x_214;
x_6 = x_221;
x_7 = x_217;
x_8 = x_212;
x_9 = x_220;
x_10 = x_381;
goto _start;
}
else
{
lean_dec(x_271);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec(x_259);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_217);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec_ref(x_212);
lean_dec(x_211);
return x_380;
}
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_391 = lean_ctor_get(x_276, 0);
x_392 = lean_ctor_get(x_276, 2);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_276);
x_393 = lean_ctor_get(x_277, 0);
lean_inc_ref(x_393);
x_394 = lean_ctor_get(x_277, 1);
lean_inc_ref(x_394);
x_395 = lean_ctor_get(x_277, 2);
lean_inc_ref(x_395);
x_396 = lean_ctor_get(x_277, 3);
lean_inc_ref(x_396);
x_397 = lean_ctor_get(x_277, 4);
lean_inc_ref(x_397);
x_398 = lean_ctor_get(x_277, 5);
lean_inc_ref(x_398);
x_399 = lean_ctor_get(x_277, 6);
lean_inc_ref(x_399);
x_400 = lean_ctor_get(x_277, 7);
lean_inc_ref(x_400);
x_401 = lean_ctor_get(x_277, 8);
lean_inc_ref(x_401);
x_402 = lean_ctor_get(x_277, 9);
lean_inc_ref(x_402);
x_403 = lean_ctor_get(x_277, 10);
lean_inc_ref(x_403);
x_404 = lean_ctor_get(x_277, 11);
lean_inc(x_404);
x_405 = lean_ctor_get(x_277, 12);
lean_inc_ref(x_405);
x_406 = lean_ctor_get(x_277, 13);
lean_inc_ref(x_406);
x_407 = lean_ctor_get(x_277, 14);
lean_inc(x_407);
x_408 = lean_ctor_get_uint8(x_277, sizeof(void*)*22);
x_409 = lean_ctor_get(x_277, 15);
lean_inc(x_409);
x_410 = lean_ctor_get(x_277, 16);
lean_inc_ref(x_410);
x_411 = lean_ctor_get(x_277, 17);
lean_inc_ref(x_411);
x_412 = lean_ctor_get(x_277, 18);
lean_inc_ref(x_412);
x_413 = lean_ctor_get(x_277, 19);
lean_inc_ref(x_413);
x_414 = lean_ctor_get(x_277, 20);
lean_inc_ref(x_414);
x_415 = lean_ctor_get_uint8(x_277, sizeof(void*)*22 + 1);
x_416 = lean_ctor_get(x_277, 21);
lean_inc_ref(x_416);
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
 lean_ctor_release(x_277, 16);
 lean_ctor_release(x_277, 17);
 lean_ctor_release(x_277, 18);
 lean_ctor_release(x_277, 19);
 lean_ctor_release(x_277, 20);
 lean_ctor_release(x_277, 21);
 x_417 = x_277;
} else {
 lean_dec_ref(x_277);
 x_417 = lean_box(0);
}
x_418 = lean_box(0);
x_419 = l_Lean_PersistentArray_set___redArg(x_399, x_216, x_418);
if (lean_is_scalar(x_417)) {
 x_420 = lean_alloc_ctor(0, 22, 2);
} else {
 x_420 = x_417;
}
lean_ctor_set(x_420, 0, x_393);
lean_ctor_set(x_420, 1, x_394);
lean_ctor_set(x_420, 2, x_395);
lean_ctor_set(x_420, 3, x_396);
lean_ctor_set(x_420, 4, x_397);
lean_ctor_set(x_420, 5, x_398);
lean_ctor_set(x_420, 6, x_419);
lean_ctor_set(x_420, 7, x_400);
lean_ctor_set(x_420, 8, x_401);
lean_ctor_set(x_420, 9, x_402);
lean_ctor_set(x_420, 10, x_403);
lean_ctor_set(x_420, 11, x_404);
lean_ctor_set(x_420, 12, x_405);
lean_ctor_set(x_420, 13, x_406);
lean_ctor_set(x_420, 14, x_407);
lean_ctor_set(x_420, 15, x_409);
lean_ctor_set(x_420, 16, x_410);
lean_ctor_set(x_420, 17, x_411);
lean_ctor_set(x_420, 18, x_412);
lean_ctor_set(x_420, 19, x_413);
lean_ctor_set(x_420, 20, x_414);
lean_ctor_set(x_420, 21, x_416);
lean_ctor_set_uint8(x_420, sizeof(void*)*22, x_408);
lean_ctor_set_uint8(x_420, sizeof(void*)*22 + 1, x_415);
x_421 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_421, 0, x_391);
lean_ctor_set(x_421, 1, x_420);
lean_ctor_set(x_421, 2, x_392);
lean_ctor_set(x_275, 14, x_421);
x_422 = lean_st_ref_set(x_223, x_275, x_278);
x_423 = lean_ctor_get(x_422, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_424 = x_422;
} else {
 lean_dec_ref(x_422);
 x_424 = lean_box(0);
}
x_425 = lean_int_mul(x_272, x_263);
lean_dec(x_272);
lean_inc_ref(x_224);
x_426 = l_Int_Linear_Poly_mul(x_224, x_425);
lean_dec(x_425);
x_427 = lean_int_mul(x_273, x_219);
lean_dec(x_273);
lean_inc_ref(x_265);
x_428 = l_Int_Linear_Poly_mul(x_265, x_427);
lean_dec(x_427);
x_429 = lean_int_mul(x_219, x_263);
lean_dec(x_219);
x_430 = l_Int_Linear_Poly_combine(x_426, x_428);
lean_inc(x_271);
lean_ctor_set(x_260, 2, x_430);
lean_ctor_set(x_260, 1, x_216);
lean_ctor_set(x_260, 0, x_271);
lean_inc(x_259);
lean_inc_ref(x_215);
if (lean_is_scalar(x_424)) {
 x_431 = lean_alloc_ctor(4, 2, 0);
} else {
 x_431 = x_424;
 lean_ctor_set_tag(x_431, 4);
}
lean_ctor_set(x_431, 0, x_215);
lean_ctor_set(x_431, 1, x_259);
x_432 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_432, 0, x_429);
lean_ctor_set(x_432, 1, x_260);
lean_ctor_set(x_432, 2, x_431);
lean_inc(x_220);
lean_inc_ref(x_212);
lean_inc(x_217);
lean_inc_ref(x_221);
lean_inc(x_214);
lean_inc_ref(x_222);
lean_inc(x_211);
lean_inc(x_223);
x_433 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_432, x_223, x_211, x_222, x_214, x_221, x_217, x_212, x_220, x_423);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_434 = lean_ctor_get(x_433, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_435 = x_433;
} else {
 lean_dec_ref(x_433);
 x_435 = lean_box(0);
}
x_436 = l_Int_Linear_Poly_mul(x_224, x_264);
lean_dec(x_264);
x_437 = lean_int_neg(x_218);
lean_dec(x_218);
x_438 = l_Int_Linear_Poly_mul(x_265, x_437);
lean_dec(x_437);
x_439 = l_Int_Linear_Poly_combine(x_436, x_438);
lean_inc(x_259);
if (lean_is_scalar(x_435)) {
 x_440 = lean_alloc_ctor(5, 2, 0);
} else {
 x_440 = x_435;
 lean_ctor_set_tag(x_440, 5);
}
lean_ctor_set(x_440, 0, x_215);
lean_ctor_set(x_440, 1, x_259);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 x_441 = x_259;
} else {
 lean_dec_ref(x_259);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(0, 3, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_271);
lean_ctor_set(x_442, 1, x_439);
lean_ctor_set(x_442, 2, x_440);
x_1 = x_442;
x_2 = x_223;
x_3 = x_211;
x_4 = x_222;
x_5 = x_214;
x_6 = x_221;
x_7 = x_217;
x_8 = x_212;
x_9 = x_220;
x_10 = x_434;
goto _start;
}
else
{
lean_dec(x_271);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec(x_259);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_217);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec_ref(x_212);
lean_dec(x_211);
return x_433;
}
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_444 = lean_ctor_get(x_275, 0);
x_445 = lean_ctor_get(x_275, 1);
x_446 = lean_ctor_get(x_275, 2);
x_447 = lean_ctor_get(x_275, 3);
x_448 = lean_ctor_get(x_275, 4);
x_449 = lean_ctor_get(x_275, 5);
x_450 = lean_ctor_get(x_275, 6);
x_451 = lean_ctor_get(x_275, 7);
x_452 = lean_ctor_get_uint8(x_275, sizeof(void*)*17);
x_453 = lean_ctor_get(x_275, 8);
x_454 = lean_ctor_get(x_275, 9);
x_455 = lean_ctor_get(x_275, 10);
x_456 = lean_ctor_get(x_275, 11);
x_457 = lean_ctor_get(x_275, 12);
x_458 = lean_ctor_get(x_275, 13);
x_459 = lean_ctor_get(x_275, 15);
x_460 = lean_ctor_get(x_275, 16);
lean_inc(x_460);
lean_inc(x_459);
lean_inc(x_458);
lean_inc(x_457);
lean_inc(x_456);
lean_inc(x_455);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_451);
lean_inc(x_450);
lean_inc(x_449);
lean_inc(x_448);
lean_inc(x_447);
lean_inc(x_446);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_275);
x_461 = lean_ctor_get(x_276, 0);
lean_inc_ref(x_461);
x_462 = lean_ctor_get(x_276, 2);
lean_inc_ref(x_462);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 lean_ctor_release(x_276, 2);
 x_463 = x_276;
} else {
 lean_dec_ref(x_276);
 x_463 = lean_box(0);
}
x_464 = lean_ctor_get(x_277, 0);
lean_inc_ref(x_464);
x_465 = lean_ctor_get(x_277, 1);
lean_inc_ref(x_465);
x_466 = lean_ctor_get(x_277, 2);
lean_inc_ref(x_466);
x_467 = lean_ctor_get(x_277, 3);
lean_inc_ref(x_467);
x_468 = lean_ctor_get(x_277, 4);
lean_inc_ref(x_468);
x_469 = lean_ctor_get(x_277, 5);
lean_inc_ref(x_469);
x_470 = lean_ctor_get(x_277, 6);
lean_inc_ref(x_470);
x_471 = lean_ctor_get(x_277, 7);
lean_inc_ref(x_471);
x_472 = lean_ctor_get(x_277, 8);
lean_inc_ref(x_472);
x_473 = lean_ctor_get(x_277, 9);
lean_inc_ref(x_473);
x_474 = lean_ctor_get(x_277, 10);
lean_inc_ref(x_474);
x_475 = lean_ctor_get(x_277, 11);
lean_inc(x_475);
x_476 = lean_ctor_get(x_277, 12);
lean_inc_ref(x_476);
x_477 = lean_ctor_get(x_277, 13);
lean_inc_ref(x_477);
x_478 = lean_ctor_get(x_277, 14);
lean_inc(x_478);
x_479 = lean_ctor_get_uint8(x_277, sizeof(void*)*22);
x_480 = lean_ctor_get(x_277, 15);
lean_inc(x_480);
x_481 = lean_ctor_get(x_277, 16);
lean_inc_ref(x_481);
x_482 = lean_ctor_get(x_277, 17);
lean_inc_ref(x_482);
x_483 = lean_ctor_get(x_277, 18);
lean_inc_ref(x_483);
x_484 = lean_ctor_get(x_277, 19);
lean_inc_ref(x_484);
x_485 = lean_ctor_get(x_277, 20);
lean_inc_ref(x_485);
x_486 = lean_ctor_get_uint8(x_277, sizeof(void*)*22 + 1);
x_487 = lean_ctor_get(x_277, 21);
lean_inc_ref(x_487);
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
 lean_ctor_release(x_277, 16);
 lean_ctor_release(x_277, 17);
 lean_ctor_release(x_277, 18);
 lean_ctor_release(x_277, 19);
 lean_ctor_release(x_277, 20);
 lean_ctor_release(x_277, 21);
 x_488 = x_277;
} else {
 lean_dec_ref(x_277);
 x_488 = lean_box(0);
}
x_489 = lean_box(0);
x_490 = l_Lean_PersistentArray_set___redArg(x_470, x_216, x_489);
if (lean_is_scalar(x_488)) {
 x_491 = lean_alloc_ctor(0, 22, 2);
} else {
 x_491 = x_488;
}
lean_ctor_set(x_491, 0, x_464);
lean_ctor_set(x_491, 1, x_465);
lean_ctor_set(x_491, 2, x_466);
lean_ctor_set(x_491, 3, x_467);
lean_ctor_set(x_491, 4, x_468);
lean_ctor_set(x_491, 5, x_469);
lean_ctor_set(x_491, 6, x_490);
lean_ctor_set(x_491, 7, x_471);
lean_ctor_set(x_491, 8, x_472);
lean_ctor_set(x_491, 9, x_473);
lean_ctor_set(x_491, 10, x_474);
lean_ctor_set(x_491, 11, x_475);
lean_ctor_set(x_491, 12, x_476);
lean_ctor_set(x_491, 13, x_477);
lean_ctor_set(x_491, 14, x_478);
lean_ctor_set(x_491, 15, x_480);
lean_ctor_set(x_491, 16, x_481);
lean_ctor_set(x_491, 17, x_482);
lean_ctor_set(x_491, 18, x_483);
lean_ctor_set(x_491, 19, x_484);
lean_ctor_set(x_491, 20, x_485);
lean_ctor_set(x_491, 21, x_487);
lean_ctor_set_uint8(x_491, sizeof(void*)*22, x_479);
lean_ctor_set_uint8(x_491, sizeof(void*)*22 + 1, x_486);
if (lean_is_scalar(x_463)) {
 x_492 = lean_alloc_ctor(0, 3, 0);
} else {
 x_492 = x_463;
}
lean_ctor_set(x_492, 0, x_461);
lean_ctor_set(x_492, 1, x_491);
lean_ctor_set(x_492, 2, x_462);
x_493 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_493, 0, x_444);
lean_ctor_set(x_493, 1, x_445);
lean_ctor_set(x_493, 2, x_446);
lean_ctor_set(x_493, 3, x_447);
lean_ctor_set(x_493, 4, x_448);
lean_ctor_set(x_493, 5, x_449);
lean_ctor_set(x_493, 6, x_450);
lean_ctor_set(x_493, 7, x_451);
lean_ctor_set(x_493, 8, x_453);
lean_ctor_set(x_493, 9, x_454);
lean_ctor_set(x_493, 10, x_455);
lean_ctor_set(x_493, 11, x_456);
lean_ctor_set(x_493, 12, x_457);
lean_ctor_set(x_493, 13, x_458);
lean_ctor_set(x_493, 14, x_492);
lean_ctor_set(x_493, 15, x_459);
lean_ctor_set(x_493, 16, x_460);
lean_ctor_set_uint8(x_493, sizeof(void*)*17, x_452);
x_494 = lean_st_ref_set(x_223, x_493, x_278);
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_496 = x_494;
} else {
 lean_dec_ref(x_494);
 x_496 = lean_box(0);
}
x_497 = lean_int_mul(x_272, x_263);
lean_dec(x_272);
lean_inc_ref(x_224);
x_498 = l_Int_Linear_Poly_mul(x_224, x_497);
lean_dec(x_497);
x_499 = lean_int_mul(x_273, x_219);
lean_dec(x_273);
lean_inc_ref(x_265);
x_500 = l_Int_Linear_Poly_mul(x_265, x_499);
lean_dec(x_499);
x_501 = lean_int_mul(x_219, x_263);
lean_dec(x_219);
x_502 = l_Int_Linear_Poly_combine(x_498, x_500);
lean_inc(x_271);
lean_ctor_set(x_260, 2, x_502);
lean_ctor_set(x_260, 1, x_216);
lean_ctor_set(x_260, 0, x_271);
lean_inc(x_259);
lean_inc_ref(x_215);
if (lean_is_scalar(x_496)) {
 x_503 = lean_alloc_ctor(4, 2, 0);
} else {
 x_503 = x_496;
 lean_ctor_set_tag(x_503, 4);
}
lean_ctor_set(x_503, 0, x_215);
lean_ctor_set(x_503, 1, x_259);
x_504 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_260);
lean_ctor_set(x_504, 2, x_503);
lean_inc(x_220);
lean_inc_ref(x_212);
lean_inc(x_217);
lean_inc_ref(x_221);
lean_inc(x_214);
lean_inc_ref(x_222);
lean_inc(x_211);
lean_inc(x_223);
x_505 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_504, x_223, x_211, x_222, x_214, x_221, x_217, x_212, x_220, x_495);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_507 = x_505;
} else {
 lean_dec_ref(x_505);
 x_507 = lean_box(0);
}
x_508 = l_Int_Linear_Poly_mul(x_224, x_264);
lean_dec(x_264);
x_509 = lean_int_neg(x_218);
lean_dec(x_218);
x_510 = l_Int_Linear_Poly_mul(x_265, x_509);
lean_dec(x_509);
x_511 = l_Int_Linear_Poly_combine(x_508, x_510);
lean_inc(x_259);
if (lean_is_scalar(x_507)) {
 x_512 = lean_alloc_ctor(5, 2, 0);
} else {
 x_512 = x_507;
 lean_ctor_set_tag(x_512, 5);
}
lean_ctor_set(x_512, 0, x_215);
lean_ctor_set(x_512, 1, x_259);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 x_513 = x_259;
} else {
 lean_dec_ref(x_259);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(0, 3, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_271);
lean_ctor_set(x_514, 1, x_511);
lean_ctor_set(x_514, 2, x_512);
x_1 = x_514;
x_2 = x_223;
x_3 = x_211;
x_4 = x_222;
x_5 = x_214;
x_6 = x_221;
x_7 = x_217;
x_8 = x_212;
x_9 = x_220;
x_10 = x_506;
goto _start;
}
else
{
lean_dec(x_271);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec(x_259);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_217);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec_ref(x_212);
lean_dec(x_211);
return x_505;
}
}
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; uint8_t x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; uint8_t x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_516 = lean_ctor_get(x_259, 0);
x_517 = lean_ctor_get(x_260, 0);
x_518 = lean_ctor_get(x_260, 2);
lean_inc(x_518);
lean_inc(x_517);
lean_dec(x_260);
x_519 = lean_int_mul(x_218, x_516);
x_520 = lean_int_mul(x_517, x_219);
x_521 = l_Lean_Meta_Grind_Arith_gcdExt(x_519, x_520);
lean_dec(x_520);
lean_dec(x_519);
x_522 = lean_ctor_get(x_521, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 0);
lean_inc(x_523);
lean_dec_ref(x_521);
x_524 = lean_ctor_get(x_522, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_522, 1);
lean_inc(x_525);
lean_dec(x_522);
x_526 = lean_st_ref_take(x_223, x_213);
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_527, 14);
lean_inc_ref(x_528);
x_529 = lean_ctor_get(x_528, 1);
lean_inc_ref(x_529);
x_530 = lean_ctor_get(x_526, 1);
lean_inc(x_530);
lean_dec_ref(x_526);
x_531 = lean_ctor_get(x_527, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_527, 1);
lean_inc_ref(x_532);
x_533 = lean_ctor_get(x_527, 2);
lean_inc(x_533);
x_534 = lean_ctor_get(x_527, 3);
lean_inc_ref(x_534);
x_535 = lean_ctor_get(x_527, 4);
lean_inc_ref(x_535);
x_536 = lean_ctor_get(x_527, 5);
lean_inc_ref(x_536);
x_537 = lean_ctor_get(x_527, 6);
lean_inc_ref(x_537);
x_538 = lean_ctor_get(x_527, 7);
lean_inc_ref(x_538);
x_539 = lean_ctor_get_uint8(x_527, sizeof(void*)*17);
x_540 = lean_ctor_get(x_527, 8);
lean_inc(x_540);
x_541 = lean_ctor_get(x_527, 9);
lean_inc_ref(x_541);
x_542 = lean_ctor_get(x_527, 10);
lean_inc_ref(x_542);
x_543 = lean_ctor_get(x_527, 11);
lean_inc_ref(x_543);
x_544 = lean_ctor_get(x_527, 12);
lean_inc_ref(x_544);
x_545 = lean_ctor_get(x_527, 13);
lean_inc_ref(x_545);
x_546 = lean_ctor_get(x_527, 15);
lean_inc_ref(x_546);
x_547 = lean_ctor_get(x_527, 16);
lean_inc_ref(x_547);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 lean_ctor_release(x_527, 2);
 lean_ctor_release(x_527, 3);
 lean_ctor_release(x_527, 4);
 lean_ctor_release(x_527, 5);
 lean_ctor_release(x_527, 6);
 lean_ctor_release(x_527, 7);
 lean_ctor_release(x_527, 8);
 lean_ctor_release(x_527, 9);
 lean_ctor_release(x_527, 10);
 lean_ctor_release(x_527, 11);
 lean_ctor_release(x_527, 12);
 lean_ctor_release(x_527, 13);
 lean_ctor_release(x_527, 14);
 lean_ctor_release(x_527, 15);
 lean_ctor_release(x_527, 16);
 x_548 = x_527;
} else {
 lean_dec_ref(x_527);
 x_548 = lean_box(0);
}
x_549 = lean_ctor_get(x_528, 0);
lean_inc_ref(x_549);
x_550 = lean_ctor_get(x_528, 2);
lean_inc_ref(x_550);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 lean_ctor_release(x_528, 2);
 x_551 = x_528;
} else {
 lean_dec_ref(x_528);
 x_551 = lean_box(0);
}
x_552 = lean_ctor_get(x_529, 0);
lean_inc_ref(x_552);
x_553 = lean_ctor_get(x_529, 1);
lean_inc_ref(x_553);
x_554 = lean_ctor_get(x_529, 2);
lean_inc_ref(x_554);
x_555 = lean_ctor_get(x_529, 3);
lean_inc_ref(x_555);
x_556 = lean_ctor_get(x_529, 4);
lean_inc_ref(x_556);
x_557 = lean_ctor_get(x_529, 5);
lean_inc_ref(x_557);
x_558 = lean_ctor_get(x_529, 6);
lean_inc_ref(x_558);
x_559 = lean_ctor_get(x_529, 7);
lean_inc_ref(x_559);
x_560 = lean_ctor_get(x_529, 8);
lean_inc_ref(x_560);
x_561 = lean_ctor_get(x_529, 9);
lean_inc_ref(x_561);
x_562 = lean_ctor_get(x_529, 10);
lean_inc_ref(x_562);
x_563 = lean_ctor_get(x_529, 11);
lean_inc(x_563);
x_564 = lean_ctor_get(x_529, 12);
lean_inc_ref(x_564);
x_565 = lean_ctor_get(x_529, 13);
lean_inc_ref(x_565);
x_566 = lean_ctor_get(x_529, 14);
lean_inc(x_566);
x_567 = lean_ctor_get_uint8(x_529, sizeof(void*)*22);
x_568 = lean_ctor_get(x_529, 15);
lean_inc(x_568);
x_569 = lean_ctor_get(x_529, 16);
lean_inc_ref(x_569);
x_570 = lean_ctor_get(x_529, 17);
lean_inc_ref(x_570);
x_571 = lean_ctor_get(x_529, 18);
lean_inc_ref(x_571);
x_572 = lean_ctor_get(x_529, 19);
lean_inc_ref(x_572);
x_573 = lean_ctor_get(x_529, 20);
lean_inc_ref(x_573);
x_574 = lean_ctor_get_uint8(x_529, sizeof(void*)*22 + 1);
x_575 = lean_ctor_get(x_529, 21);
lean_inc_ref(x_575);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 lean_ctor_release(x_529, 2);
 lean_ctor_release(x_529, 3);
 lean_ctor_release(x_529, 4);
 lean_ctor_release(x_529, 5);
 lean_ctor_release(x_529, 6);
 lean_ctor_release(x_529, 7);
 lean_ctor_release(x_529, 8);
 lean_ctor_release(x_529, 9);
 lean_ctor_release(x_529, 10);
 lean_ctor_release(x_529, 11);
 lean_ctor_release(x_529, 12);
 lean_ctor_release(x_529, 13);
 lean_ctor_release(x_529, 14);
 lean_ctor_release(x_529, 15);
 lean_ctor_release(x_529, 16);
 lean_ctor_release(x_529, 17);
 lean_ctor_release(x_529, 18);
 lean_ctor_release(x_529, 19);
 lean_ctor_release(x_529, 20);
 lean_ctor_release(x_529, 21);
 x_576 = x_529;
} else {
 lean_dec_ref(x_529);
 x_576 = lean_box(0);
}
x_577 = lean_box(0);
x_578 = l_Lean_PersistentArray_set___redArg(x_558, x_216, x_577);
if (lean_is_scalar(x_576)) {
 x_579 = lean_alloc_ctor(0, 22, 2);
} else {
 x_579 = x_576;
}
lean_ctor_set(x_579, 0, x_552);
lean_ctor_set(x_579, 1, x_553);
lean_ctor_set(x_579, 2, x_554);
lean_ctor_set(x_579, 3, x_555);
lean_ctor_set(x_579, 4, x_556);
lean_ctor_set(x_579, 5, x_557);
lean_ctor_set(x_579, 6, x_578);
lean_ctor_set(x_579, 7, x_559);
lean_ctor_set(x_579, 8, x_560);
lean_ctor_set(x_579, 9, x_561);
lean_ctor_set(x_579, 10, x_562);
lean_ctor_set(x_579, 11, x_563);
lean_ctor_set(x_579, 12, x_564);
lean_ctor_set(x_579, 13, x_565);
lean_ctor_set(x_579, 14, x_566);
lean_ctor_set(x_579, 15, x_568);
lean_ctor_set(x_579, 16, x_569);
lean_ctor_set(x_579, 17, x_570);
lean_ctor_set(x_579, 18, x_571);
lean_ctor_set(x_579, 19, x_572);
lean_ctor_set(x_579, 20, x_573);
lean_ctor_set(x_579, 21, x_575);
lean_ctor_set_uint8(x_579, sizeof(void*)*22, x_567);
lean_ctor_set_uint8(x_579, sizeof(void*)*22 + 1, x_574);
if (lean_is_scalar(x_551)) {
 x_580 = lean_alloc_ctor(0, 3, 0);
} else {
 x_580 = x_551;
}
lean_ctor_set(x_580, 0, x_549);
lean_ctor_set(x_580, 1, x_579);
lean_ctor_set(x_580, 2, x_550);
if (lean_is_scalar(x_548)) {
 x_581 = lean_alloc_ctor(0, 17, 1);
} else {
 x_581 = x_548;
}
lean_ctor_set(x_581, 0, x_531);
lean_ctor_set(x_581, 1, x_532);
lean_ctor_set(x_581, 2, x_533);
lean_ctor_set(x_581, 3, x_534);
lean_ctor_set(x_581, 4, x_535);
lean_ctor_set(x_581, 5, x_536);
lean_ctor_set(x_581, 6, x_537);
lean_ctor_set(x_581, 7, x_538);
lean_ctor_set(x_581, 8, x_540);
lean_ctor_set(x_581, 9, x_541);
lean_ctor_set(x_581, 10, x_542);
lean_ctor_set(x_581, 11, x_543);
lean_ctor_set(x_581, 12, x_544);
lean_ctor_set(x_581, 13, x_545);
lean_ctor_set(x_581, 14, x_580);
lean_ctor_set(x_581, 15, x_546);
lean_ctor_set(x_581, 16, x_547);
lean_ctor_set_uint8(x_581, sizeof(void*)*17, x_539);
x_582 = lean_st_ref_set(x_223, x_581, x_530);
x_583 = lean_ctor_get(x_582, 1);
lean_inc(x_583);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_584 = x_582;
} else {
 lean_dec_ref(x_582);
 x_584 = lean_box(0);
}
x_585 = lean_int_mul(x_524, x_516);
lean_dec(x_524);
lean_inc_ref(x_224);
x_586 = l_Int_Linear_Poly_mul(x_224, x_585);
lean_dec(x_585);
x_587 = lean_int_mul(x_525, x_219);
lean_dec(x_525);
lean_inc_ref(x_518);
x_588 = l_Int_Linear_Poly_mul(x_518, x_587);
lean_dec(x_587);
x_589 = lean_int_mul(x_219, x_516);
lean_dec(x_219);
x_590 = l_Int_Linear_Poly_combine(x_586, x_588);
lean_inc(x_523);
x_591 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_591, 0, x_523);
lean_ctor_set(x_591, 1, x_216);
lean_ctor_set(x_591, 2, x_590);
lean_inc(x_259);
lean_inc_ref(x_215);
if (lean_is_scalar(x_584)) {
 x_592 = lean_alloc_ctor(4, 2, 0);
} else {
 x_592 = x_584;
 lean_ctor_set_tag(x_592, 4);
}
lean_ctor_set(x_592, 0, x_215);
lean_ctor_set(x_592, 1, x_259);
x_593 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_593, 0, x_589);
lean_ctor_set(x_593, 1, x_591);
lean_ctor_set(x_593, 2, x_592);
lean_inc(x_220);
lean_inc_ref(x_212);
lean_inc(x_217);
lean_inc_ref(x_221);
lean_inc(x_214);
lean_inc_ref(x_222);
lean_inc(x_211);
lean_inc(x_223);
x_594 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_593, x_223, x_211, x_222, x_214, x_221, x_217, x_212, x_220, x_583);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_595 = lean_ctor_get(x_594, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_596 = x_594;
} else {
 lean_dec_ref(x_594);
 x_596 = lean_box(0);
}
x_597 = l_Int_Linear_Poly_mul(x_224, x_517);
lean_dec(x_517);
x_598 = lean_int_neg(x_218);
lean_dec(x_218);
x_599 = l_Int_Linear_Poly_mul(x_518, x_598);
lean_dec(x_598);
x_600 = l_Int_Linear_Poly_combine(x_597, x_599);
lean_inc(x_259);
if (lean_is_scalar(x_596)) {
 x_601 = lean_alloc_ctor(5, 2, 0);
} else {
 x_601 = x_596;
 lean_ctor_set_tag(x_601, 5);
}
lean_ctor_set(x_601, 0, x_215);
lean_ctor_set(x_601, 1, x_259);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 x_602 = x_259;
} else {
 lean_dec_ref(x_259);
 x_602 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_603 = lean_alloc_ctor(0, 3, 0);
} else {
 x_603 = x_602;
}
lean_ctor_set(x_603, 0, x_523);
lean_ctor_set(x_603, 1, x_600);
lean_ctor_set(x_603, 2, x_601);
x_1 = x_603;
x_2 = x_223;
x_3 = x_211;
x_4 = x_222;
x_5 = x_214;
x_6 = x_221;
x_7 = x_217;
x_8 = x_212;
x_9 = x_220;
x_10 = x_595;
goto _start;
}
else
{
lean_dec(x_523);
lean_dec_ref(x_518);
lean_dec(x_517);
lean_dec(x_259);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_217);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec_ref(x_212);
lean_dec(x_211);
return x_594;
}
}
}
}
}
block_639:
{
lean_object* x_627; 
x_627 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_618, x_626);
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; uint8_t x_632; 
x_628 = lean_ctor_get(x_627, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_628, 6);
lean_inc_ref(x_629);
lean_dec(x_628);
x_630 = lean_ctor_get(x_627, 1);
lean_inc(x_630);
lean_dec_ref(x_627);
x_631 = lean_ctor_get(x_629, 2);
x_632 = lean_nat_dec_lt(x_613, x_631);
if (x_632 == 0)
{
lean_object* x_633; 
lean_dec_ref(x_629);
x_633 = l_outOfBounds___redArg(x_611);
x_211 = x_619;
x_212 = x_624;
x_213 = x_630;
x_214 = x_621;
x_215 = x_612;
x_216 = x_613;
x_217 = x_623;
x_218 = x_614;
x_219 = x_616;
x_220 = x_625;
x_221 = x_622;
x_222 = x_620;
x_223 = x_618;
x_224 = x_615;
x_225 = x_617;
x_226 = x_633;
goto block_605;
}
else
{
lean_object* x_634; 
x_634 = l_Lean_PersistentArray_get_x21___redArg(x_611, x_629, x_613);
x_211 = x_619;
x_212 = x_624;
x_213 = x_630;
x_214 = x_621;
x_215 = x_612;
x_216 = x_613;
x_217 = x_623;
x_218 = x_614;
x_219 = x_616;
x_220 = x_625;
x_221 = x_622;
x_222 = x_620;
x_223 = x_618;
x_224 = x_615;
x_225 = x_617;
x_226 = x_634;
goto block_605;
}
}
else
{
uint8_t x_635; 
lean_dec(x_625);
lean_dec_ref(x_624);
lean_dec(x_623);
lean_dec_ref(x_622);
lean_dec(x_621);
lean_dec_ref(x_620);
lean_dec(x_619);
lean_dec(x_618);
lean_dec_ref(x_617);
lean_dec(x_616);
lean_dec_ref(x_615);
lean_dec(x_614);
lean_dec(x_613);
lean_dec_ref(x_612);
x_635 = !lean_is_exclusive(x_627);
if (x_635 == 0)
{
return x_627;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_636 = lean_ctor_get(x_627, 0);
x_637 = lean_ctor_get(x_627, 1);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_627);
x_638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_637);
return x_638;
}
}
}
block_741:
{
lean_object* x_649; lean_object* x_650; 
x_649 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_646);
x_650 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_649, x_640, x_641, x_642, x_643, x_644, x_645, x_646, x_647, x_648);
if (lean_obj_tag(x_650) == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; 
x_651 = lean_ctor_get(x_650, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_650, 1);
lean_inc(x_652);
lean_dec_ref(x_650);
x_653 = lean_ctor_get(x_651, 0);
x_654 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
x_655 = l_Int_Linear_Poly_isUnsatDvd(x_653, x_654);
if (x_655 == 0)
{
uint8_t x_656; 
x_656 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_651);
if (x_656 == 0)
{
lean_dec(x_610);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_657; 
x_657 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_651, x_640, x_641, x_642, x_643, x_644, x_645, x_646, x_647, x_652);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec(x_641);
lean_dec(x_640);
return x_657;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_inc_ref(x_654);
lean_inc(x_653);
x_658 = lean_ctor_get(x_654, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_654, 1);
lean_inc(x_659);
x_660 = lean_ctor_get(x_654, 2);
lean_inc_ref(x_660);
lean_inc(x_651);
x_661 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_651, x_640, x_652);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; lean_object* x_663; uint8_t x_664; uint8_t x_665; uint8_t x_666; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_661, 1);
lean_inc(x_663);
lean_dec_ref(x_661);
x_664 = 0;
x_665 = lean_unbox(x_662);
lean_dec(x_662);
x_666 = l_Lean_instBEqLBool_beq(x_665, x_664);
if (x_666 == 0)
{
x_612 = x_651;
x_613 = x_659;
x_614 = x_658;
x_615 = x_660;
x_616 = x_653;
x_617 = x_654;
x_618 = x_640;
x_619 = x_641;
x_620 = x_642;
x_621 = x_643;
x_622 = x_644;
x_623 = x_645;
x_624 = x_646;
x_625 = x_647;
x_626 = x_663;
goto block_639;
}
else
{
lean_object* x_667; 
x_667 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_659, x_640, x_663);
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_668; 
x_668 = lean_ctor_get(x_667, 1);
lean_inc(x_668);
lean_dec_ref(x_667);
x_612 = x_651;
x_613 = x_659;
x_614 = x_658;
x_615 = x_660;
x_616 = x_653;
x_617 = x_654;
x_618 = x_640;
x_619 = x_641;
x_620 = x_642;
x_621 = x_643;
x_622 = x_644;
x_623 = x_645;
x_624 = x_646;
x_625 = x_647;
x_626 = x_668;
goto block_639;
}
else
{
lean_dec_ref(x_660);
lean_dec(x_659);
lean_dec(x_658);
lean_dec_ref(x_654);
lean_dec(x_653);
lean_dec(x_651);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec(x_641);
lean_dec(x_640);
return x_667;
}
}
}
else
{
uint8_t x_669; 
lean_dec_ref(x_660);
lean_dec(x_659);
lean_dec(x_658);
lean_dec_ref(x_654);
lean_dec(x_653);
lean_dec(x_651);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec(x_641);
lean_dec(x_640);
x_669 = !lean_is_exclusive(x_661);
if (x_669 == 0)
{
return x_661;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_670 = lean_ctor_get(x_661, 0);
x_671 = lean_ctor_get(x_661, 1);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_661);
x_672 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_672, 0, x_670);
lean_ctor_set(x_672, 1, x_671);
return x_672;
}
}
}
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; 
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec(x_641);
x_673 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_674 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_673, x_646, x_652);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_unbox(x_675);
lean_dec(x_675);
if (x_676 == 0)
{
lean_object* x_677; 
lean_dec(x_651);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_640);
lean_dec(x_610);
x_677 = lean_ctor_get(x_674, 1);
lean_inc(x_677);
lean_dec_ref(x_674);
x_185 = x_677;
goto block_188;
}
else
{
uint8_t x_678; 
x_678 = !lean_is_exclusive(x_674);
if (x_678 == 0)
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_679 = lean_ctor_get(x_674, 1);
x_680 = lean_ctor_get(x_674, 0);
lean_dec(x_680);
x_681 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_651, x_640, x_679);
lean_dec(x_640);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
lean_dec_ref(x_681);
x_684 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_674, 7);
lean_ctor_set(x_674, 1, x_682);
lean_ctor_set(x_674, 0, x_684);
if (lean_is_scalar(x_610)) {
 x_685 = lean_alloc_ctor(7, 2, 0);
} else {
 x_685 = x_610;
 lean_ctor_set_tag(x_685, 7);
}
lean_ctor_set(x_685, 0, x_674);
lean_ctor_set(x_685, 1, x_684);
x_686 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_673, x_685, x_644, x_645, x_646, x_647, x_683);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
x_687 = lean_ctor_get(x_686, 1);
lean_inc(x_687);
lean_dec_ref(x_686);
x_185 = x_687;
goto block_188;
}
else
{
uint8_t x_688; 
lean_free_object(x_674);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_610);
x_688 = !lean_is_exclusive(x_681);
if (x_688 == 0)
{
return x_681;
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_689 = lean_ctor_get(x_681, 0);
x_690 = lean_ctor_get(x_681, 1);
lean_inc(x_690);
lean_inc(x_689);
lean_dec(x_681);
x_691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_691, 0, x_689);
lean_ctor_set(x_691, 1, x_690);
return x_691;
}
}
}
else
{
lean_object* x_692; lean_object* x_693; 
x_692 = lean_ctor_get(x_674, 1);
lean_inc(x_692);
lean_dec(x_674);
x_693 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_651, x_640, x_692);
lean_dec(x_640);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
lean_dec_ref(x_693);
x_696 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_697 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_697, 0, x_696);
lean_ctor_set(x_697, 1, x_694);
if (lean_is_scalar(x_610)) {
 x_698 = lean_alloc_ctor(7, 2, 0);
} else {
 x_698 = x_610;
 lean_ctor_set_tag(x_698, 7);
}
lean_ctor_set(x_698, 0, x_697);
lean_ctor_set(x_698, 1, x_696);
x_699 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_673, x_698, x_644, x_645, x_646, x_647, x_695);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
x_700 = lean_ctor_get(x_699, 1);
lean_inc(x_700);
lean_dec_ref(x_699);
x_185 = x_700;
goto block_188;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_610);
x_701 = lean_ctor_get(x_693, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_693, 1);
lean_inc(x_702);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_703 = x_693;
} else {
 lean_dec_ref(x_693);
 x_703 = lean_box(0);
}
if (lean_is_scalar(x_703)) {
 x_704 = lean_alloc_ctor(1, 2, 0);
} else {
 x_704 = x_703;
}
lean_ctor_set(x_704, 0, x_701);
lean_ctor_set(x_704, 1, x_702);
return x_704;
}
}
}
}
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; uint8_t x_708; 
x_705 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_706 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_705, x_646, x_652);
x_707 = lean_ctor_get(x_706, 0);
lean_inc(x_707);
x_708 = lean_unbox(x_707);
lean_dec(x_707);
if (x_708 == 0)
{
lean_object* x_709; 
lean_dec(x_610);
x_709 = lean_ctor_get(x_706, 1);
lean_inc(x_709);
lean_dec_ref(x_706);
x_166 = x_651;
x_167 = x_640;
x_168 = x_641;
x_169 = x_642;
x_170 = x_643;
x_171 = x_644;
x_172 = x_645;
x_173 = x_646;
x_174 = x_647;
x_175 = x_709;
goto block_184;
}
else
{
uint8_t x_710; 
x_710 = !lean_is_exclusive(x_706);
if (x_710 == 0)
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_711 = lean_ctor_get(x_706, 1);
x_712 = lean_ctor_get(x_706, 0);
lean_dec(x_712);
lean_inc(x_651);
x_713 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_651, x_640, x_711);
if (lean_obj_tag(x_713) == 0)
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_714 = lean_ctor_get(x_713, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_713, 1);
lean_inc(x_715);
lean_dec_ref(x_713);
x_716 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_706, 7);
lean_ctor_set(x_706, 1, x_714);
lean_ctor_set(x_706, 0, x_716);
if (lean_is_scalar(x_610)) {
 x_717 = lean_alloc_ctor(7, 2, 0);
} else {
 x_717 = x_610;
 lean_ctor_set_tag(x_717, 7);
}
lean_ctor_set(x_717, 0, x_706);
lean_ctor_set(x_717, 1, x_716);
x_718 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_705, x_717, x_644, x_645, x_646, x_647, x_715);
x_719 = lean_ctor_get(x_718, 1);
lean_inc(x_719);
lean_dec_ref(x_718);
x_166 = x_651;
x_167 = x_640;
x_168 = x_641;
x_169 = x_642;
x_170 = x_643;
x_171 = x_644;
x_172 = x_645;
x_173 = x_646;
x_174 = x_647;
x_175 = x_719;
goto block_184;
}
else
{
uint8_t x_720; 
lean_free_object(x_706);
lean_dec(x_651);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec(x_641);
lean_dec(x_640);
lean_dec(x_610);
x_720 = !lean_is_exclusive(x_713);
if (x_720 == 0)
{
return x_713;
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_721 = lean_ctor_get(x_713, 0);
x_722 = lean_ctor_get(x_713, 1);
lean_inc(x_722);
lean_inc(x_721);
lean_dec(x_713);
x_723 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_723, 0, x_721);
lean_ctor_set(x_723, 1, x_722);
return x_723;
}
}
}
else
{
lean_object* x_724; lean_object* x_725; 
x_724 = lean_ctor_get(x_706, 1);
lean_inc(x_724);
lean_dec(x_706);
lean_inc(x_651);
x_725 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_651, x_640, x_724);
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_725, 1);
lean_inc(x_727);
lean_dec_ref(x_725);
x_728 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_729 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_729, 0, x_728);
lean_ctor_set(x_729, 1, x_726);
if (lean_is_scalar(x_610)) {
 x_730 = lean_alloc_ctor(7, 2, 0);
} else {
 x_730 = x_610;
 lean_ctor_set_tag(x_730, 7);
}
lean_ctor_set(x_730, 0, x_729);
lean_ctor_set(x_730, 1, x_728);
x_731 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_705, x_730, x_644, x_645, x_646, x_647, x_727);
x_732 = lean_ctor_get(x_731, 1);
lean_inc(x_732);
lean_dec_ref(x_731);
x_166 = x_651;
x_167 = x_640;
x_168 = x_641;
x_169 = x_642;
x_170 = x_643;
x_171 = x_644;
x_172 = x_645;
x_173 = x_646;
x_174 = x_647;
x_175 = x_732;
goto block_184;
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
lean_dec(x_651);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec(x_641);
lean_dec(x_640);
lean_dec(x_610);
x_733 = lean_ctor_get(x_725, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_725, 1);
lean_inc(x_734);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 lean_ctor_release(x_725, 1);
 x_735 = x_725;
} else {
 lean_dec_ref(x_725);
 x_735 = lean_box(0);
}
if (lean_is_scalar(x_735)) {
 x_736 = lean_alloc_ctor(1, 2, 0);
} else {
 x_736 = x_735;
}
lean_ctor_set(x_736, 0, x_733);
lean_ctor_set(x_736, 1, x_734);
return x_736;
}
}
}
}
}
else
{
uint8_t x_737; 
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec_ref(x_642);
lean_dec(x_641);
lean_dec(x_640);
lean_dec(x_610);
x_737 = !lean_is_exclusive(x_650);
if (x_737 == 0)
{
return x_650;
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_738 = lean_ctor_get(x_650, 0);
x_739 = lean_ctor_get(x_650, 1);
lean_inc(x_739);
lean_inc(x_738);
lean_dec(x_650);
x_740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_740, 0, x_738);
lean_ctor_set(x_740, 1, x_739);
return x_740;
}
}
}
}
else
{
uint8_t x_755; 
lean_free_object(x_8);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_190);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_755 = !lean_is_exclusive(x_205);
if (x_755 == 0)
{
lean_object* x_756; lean_object* x_757; 
x_756 = lean_ctor_get(x_205, 0);
lean_dec(x_756);
x_757 = lean_box(0);
lean_ctor_set(x_205, 0, x_757);
return x_205;
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_758 = lean_ctor_get(x_205, 1);
lean_inc(x_758);
lean_dec(x_205);
x_759 = lean_box(0);
x_760 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_760, 0, x_759);
lean_ctor_set(x_760, 1, x_758);
return x_760;
}
}
}
else
{
uint8_t x_761; 
lean_free_object(x_8);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_190);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_761 = !lean_is_exclusive(x_205);
if (x_761 == 0)
{
return x_205;
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; 
x_762 = lean_ctor_get(x_205, 0);
x_763 = lean_ctor_get(x_205, 1);
lean_inc(x_763);
lean_inc(x_762);
lean_dec(x_205);
x_764 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_764, 0, x_762);
lean_ctor_set(x_764, 1, x_763);
return x_764;
}
}
}
else
{
lean_object* x_765; 
lean_free_object(x_8);
lean_dec_ref(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_190);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_765 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_195, x_10);
return x_765;
}
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; uint8_t x_778; lean_object* x_779; uint8_t x_780; lean_object* x_781; uint8_t x_782; 
x_766 = lean_ctor_get(x_8, 0);
x_767 = lean_ctor_get(x_8, 1);
x_768 = lean_ctor_get(x_8, 2);
x_769 = lean_ctor_get(x_8, 3);
x_770 = lean_ctor_get(x_8, 4);
x_771 = lean_ctor_get(x_8, 5);
x_772 = lean_ctor_get(x_8, 6);
x_773 = lean_ctor_get(x_8, 7);
x_774 = lean_ctor_get(x_8, 8);
x_775 = lean_ctor_get(x_8, 9);
x_776 = lean_ctor_get(x_8, 10);
x_777 = lean_ctor_get(x_8, 11);
x_778 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_779 = lean_ctor_get(x_8, 12);
x_780 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_781 = lean_ctor_get(x_8, 13);
lean_inc(x_781);
lean_inc(x_779);
lean_inc(x_777);
lean_inc(x_776);
lean_inc(x_775);
lean_inc(x_774);
lean_inc(x_773);
lean_inc(x_772);
lean_inc(x_771);
lean_inc(x_770);
lean_inc(x_769);
lean_inc(x_768);
lean_inc(x_767);
lean_inc(x_766);
lean_dec(x_8);
x_782 = lean_nat_dec_eq(x_769, x_770);
if (x_782 == 0)
{
lean_object* x_783; 
x_783 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; uint8_t x_785; 
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_unbox(x_784);
lean_dec(x_784);
if (x_785 == 0)
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; uint8_t x_1029; 
x_786 = lean_ctor_get(x_783, 1);
lean_inc(x_786);
lean_dec_ref(x_783);
x_787 = lean_unsigned_to_nat(1u);
x_788 = lean_nat_add(x_769, x_787);
lean_dec(x_769);
x_789 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_789, 0, x_766);
lean_ctor_set(x_789, 1, x_767);
lean_ctor_set(x_789, 2, x_768);
lean_ctor_set(x_789, 3, x_788);
lean_ctor_set(x_789, 4, x_770);
lean_ctor_set(x_789, 5, x_771);
lean_ctor_set(x_789, 6, x_772);
lean_ctor_set(x_789, 7, x_773);
lean_ctor_set(x_789, 8, x_774);
lean_ctor_set(x_789, 9, x_775);
lean_ctor_set(x_789, 10, x_776);
lean_ctor_set(x_789, 11, x_777);
lean_ctor_set(x_789, 12, x_779);
lean_ctor_set(x_789, 13, x_781);
lean_ctor_set_uint8(x_789, sizeof(void*)*14, x_778);
lean_ctor_set_uint8(x_789, sizeof(void*)*14 + 1, x_780);
x_919 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_920 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_919, x_789, x_786);
x_921 = lean_ctor_get(x_920, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_920, 1);
lean_inc(x_922);
if (lean_is_exclusive(x_920)) {
 lean_ctor_release(x_920, 0);
 lean_ctor_release(x_920, 1);
 x_923 = x_920;
} else {
 lean_dec_ref(x_920);
 x_923 = lean_box(0);
}
x_924 = lean_box(0);
x_1029 = lean_unbox(x_921);
lean_dec(x_921);
if (x_1029 == 0)
{
x_953 = x_2;
x_954 = x_3;
x_955 = x_4;
x_956 = x_5;
x_957 = x_6;
x_958 = x_7;
x_959 = x_789;
x_960 = x_9;
x_961 = x_922;
goto block_1028;
}
else
{
lean_object* x_1030; 
lean_inc_ref(x_1);
x_1030 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_922);
if (lean_obj_tag(x_1030) == 0)
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
x_1031 = lean_ctor_get(x_1030, 0);
lean_inc(x_1031);
x_1032 = lean_ctor_get(x_1030, 1);
lean_inc(x_1032);
lean_dec_ref(x_1030);
x_1033 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_1034 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1034, 0, x_1033);
lean_ctor_set(x_1034, 1, x_1031);
x_1035 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1035, 0, x_1034);
lean_ctor_set(x_1035, 1, x_1033);
x_1036 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_919, x_1035, x_6, x_7, x_789, x_9, x_1032);
x_1037 = lean_ctor_get(x_1036, 1);
lean_inc(x_1037);
lean_dec_ref(x_1036);
x_953 = x_2;
x_954 = x_3;
x_955 = x_4;
x_956 = x_5;
x_957 = x_6;
x_958 = x_7;
x_959 = x_789;
x_960 = x_9;
x_961 = x_1037;
goto block_1028;
}
else
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
lean_dec(x_923);
lean_dec_ref(x_789);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1038 = lean_ctor_get(x_1030, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1030, 1);
lean_inc(x_1039);
if (lean_is_exclusive(x_1030)) {
 lean_ctor_release(x_1030, 0);
 lean_ctor_release(x_1030, 1);
 x_1040 = x_1030;
} else {
 lean_dec_ref(x_1030);
 x_1040 = lean_box(0);
}
if (lean_is_scalar(x_1040)) {
 x_1041 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1041 = x_1040;
}
lean_ctor_set(x_1041, 0, x_1038);
lean_ctor_set(x_1041, 1, x_1039);
return x_1041;
}
}
block_918:
{
if (lean_obj_tag(x_805) == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; uint8_t x_809; 
lean_dec_ref(x_803);
lean_dec_ref(x_801);
lean_dec(x_798);
lean_dec(x_797);
lean_dec(x_793);
lean_dec(x_790);
x_806 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_807 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_806, x_791, x_792);
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
x_809 = lean_unbox(x_808);
lean_dec(x_808);
if (x_809 == 0)
{
lean_object* x_810; 
x_810 = lean_ctor_get(x_807, 1);
lean_inc(x_810);
lean_dec_ref(x_807);
x_11 = x_794;
x_12 = x_795;
x_13 = x_804;
x_14 = x_802;
x_15 = x_800;
x_16 = x_796;
x_17 = x_791;
x_18 = x_799;
x_19 = x_810;
goto block_165;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; 
x_811 = lean_ctor_get(x_807, 1);
lean_inc(x_811);
if (lean_is_exclusive(x_807)) {
 lean_ctor_release(x_807, 0);
 lean_ctor_release(x_807, 1);
 x_812 = x_807;
} else {
 lean_dec_ref(x_807);
 x_812 = lean_box(0);
}
lean_inc_ref(x_794);
x_813 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_794, x_802, x_811);
if (lean_obj_tag(x_813) == 0)
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_814 = lean_ctor_get(x_813, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_813, 1);
lean_inc(x_815);
lean_dec_ref(x_813);
x_816 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_812)) {
 x_817 = lean_alloc_ctor(7, 2, 0);
} else {
 x_817 = x_812;
 lean_ctor_set_tag(x_817, 7);
}
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_814);
x_818 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_818, 0, x_817);
lean_ctor_set(x_818, 1, x_816);
x_819 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_806, x_818, x_800, x_796, x_791, x_799, x_815);
x_820 = lean_ctor_get(x_819, 1);
lean_inc(x_820);
lean_dec_ref(x_819);
x_11 = x_794;
x_12 = x_795;
x_13 = x_804;
x_14 = x_802;
x_15 = x_800;
x_16 = x_796;
x_17 = x_791;
x_18 = x_799;
x_19 = x_820;
goto block_165;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
lean_dec(x_812);
lean_dec_ref(x_804);
lean_dec(x_802);
lean_dec_ref(x_800);
lean_dec(x_799);
lean_dec(x_796);
lean_dec(x_795);
lean_dec_ref(x_794);
lean_dec_ref(x_791);
x_821 = lean_ctor_get(x_813, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_813, 1);
lean_inc(x_822);
if (lean_is_exclusive(x_813)) {
 lean_ctor_release(x_813, 0);
 lean_ctor_release(x_813, 1);
 x_823 = x_813;
} else {
 lean_dec_ref(x_813);
 x_823 = lean_box(0);
}
if (lean_is_scalar(x_823)) {
 x_824 = lean_alloc_ctor(1, 2, 0);
} else {
 x_824 = x_823;
}
lean_ctor_set(x_824, 0, x_821);
lean_ctor_set(x_824, 1, x_822);
return x_824;
}
}
}
else
{
lean_object* x_825; lean_object* x_826; 
lean_dec_ref(x_804);
x_825 = lean_ctor_get(x_805, 0);
lean_inc(x_825);
lean_dec_ref(x_805);
x_826 = lean_ctor_get(x_825, 1);
lean_inc_ref(x_826);
if (lean_obj_tag(x_826) == 0)
{
lean_object* x_827; 
lean_dec_ref(x_826);
lean_dec_ref(x_803);
lean_dec(x_798);
lean_dec(x_797);
lean_dec(x_795);
lean_dec_ref(x_794);
x_827 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_825, x_802, x_790, x_801, x_793, x_800, x_796, x_791, x_799, x_792);
lean_dec(x_799);
lean_dec_ref(x_791);
lean_dec(x_796);
lean_dec_ref(x_800);
lean_dec(x_793);
lean_dec_ref(x_801);
lean_dec(x_790);
lean_dec(x_802);
return x_827;
}
else
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; uint8_t x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; uint8_t x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; uint8_t x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; 
x_828 = lean_ctor_get(x_825, 0);
x_829 = lean_ctor_get(x_826, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_826, 2);
lean_inc_ref(x_830);
if (lean_is_exclusive(x_826)) {
 lean_ctor_release(x_826, 0);
 lean_ctor_release(x_826, 1);
 lean_ctor_release(x_826, 2);
 x_831 = x_826;
} else {
 lean_dec_ref(x_826);
 x_831 = lean_box(0);
}
x_832 = lean_int_mul(x_797, x_828);
x_833 = lean_int_mul(x_829, x_798);
x_834 = l_Lean_Meta_Grind_Arith_gcdExt(x_832, x_833);
lean_dec(x_833);
lean_dec(x_832);
x_835 = lean_ctor_get(x_834, 1);
lean_inc(x_835);
x_836 = lean_ctor_get(x_834, 0);
lean_inc(x_836);
lean_dec_ref(x_834);
x_837 = lean_ctor_get(x_835, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_835, 1);
lean_inc(x_838);
lean_dec(x_835);
x_839 = lean_st_ref_take(x_802, x_792);
x_840 = lean_ctor_get(x_839, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_840, 14);
lean_inc_ref(x_841);
x_842 = lean_ctor_get(x_841, 1);
lean_inc_ref(x_842);
x_843 = lean_ctor_get(x_839, 1);
lean_inc(x_843);
lean_dec_ref(x_839);
x_844 = lean_ctor_get(x_840, 0);
lean_inc(x_844);
x_845 = lean_ctor_get(x_840, 1);
lean_inc_ref(x_845);
x_846 = lean_ctor_get(x_840, 2);
lean_inc(x_846);
x_847 = lean_ctor_get(x_840, 3);
lean_inc_ref(x_847);
x_848 = lean_ctor_get(x_840, 4);
lean_inc_ref(x_848);
x_849 = lean_ctor_get(x_840, 5);
lean_inc_ref(x_849);
x_850 = lean_ctor_get(x_840, 6);
lean_inc_ref(x_850);
x_851 = lean_ctor_get(x_840, 7);
lean_inc_ref(x_851);
x_852 = lean_ctor_get_uint8(x_840, sizeof(void*)*17);
x_853 = lean_ctor_get(x_840, 8);
lean_inc(x_853);
x_854 = lean_ctor_get(x_840, 9);
lean_inc_ref(x_854);
x_855 = lean_ctor_get(x_840, 10);
lean_inc_ref(x_855);
x_856 = lean_ctor_get(x_840, 11);
lean_inc_ref(x_856);
x_857 = lean_ctor_get(x_840, 12);
lean_inc_ref(x_857);
x_858 = lean_ctor_get(x_840, 13);
lean_inc_ref(x_858);
x_859 = lean_ctor_get(x_840, 15);
lean_inc_ref(x_859);
x_860 = lean_ctor_get(x_840, 16);
lean_inc_ref(x_860);
if (lean_is_exclusive(x_840)) {
 lean_ctor_release(x_840, 0);
 lean_ctor_release(x_840, 1);
 lean_ctor_release(x_840, 2);
 lean_ctor_release(x_840, 3);
 lean_ctor_release(x_840, 4);
 lean_ctor_release(x_840, 5);
 lean_ctor_release(x_840, 6);
 lean_ctor_release(x_840, 7);
 lean_ctor_release(x_840, 8);
 lean_ctor_release(x_840, 9);
 lean_ctor_release(x_840, 10);
 lean_ctor_release(x_840, 11);
 lean_ctor_release(x_840, 12);
 lean_ctor_release(x_840, 13);
 lean_ctor_release(x_840, 14);
 lean_ctor_release(x_840, 15);
 lean_ctor_release(x_840, 16);
 x_861 = x_840;
} else {
 lean_dec_ref(x_840);
 x_861 = lean_box(0);
}
x_862 = lean_ctor_get(x_841, 0);
lean_inc_ref(x_862);
x_863 = lean_ctor_get(x_841, 2);
lean_inc_ref(x_863);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 lean_ctor_release(x_841, 2);
 x_864 = x_841;
} else {
 lean_dec_ref(x_841);
 x_864 = lean_box(0);
}
x_865 = lean_ctor_get(x_842, 0);
lean_inc_ref(x_865);
x_866 = lean_ctor_get(x_842, 1);
lean_inc_ref(x_866);
x_867 = lean_ctor_get(x_842, 2);
lean_inc_ref(x_867);
x_868 = lean_ctor_get(x_842, 3);
lean_inc_ref(x_868);
x_869 = lean_ctor_get(x_842, 4);
lean_inc_ref(x_869);
x_870 = lean_ctor_get(x_842, 5);
lean_inc_ref(x_870);
x_871 = lean_ctor_get(x_842, 6);
lean_inc_ref(x_871);
x_872 = lean_ctor_get(x_842, 7);
lean_inc_ref(x_872);
x_873 = lean_ctor_get(x_842, 8);
lean_inc_ref(x_873);
x_874 = lean_ctor_get(x_842, 9);
lean_inc_ref(x_874);
x_875 = lean_ctor_get(x_842, 10);
lean_inc_ref(x_875);
x_876 = lean_ctor_get(x_842, 11);
lean_inc(x_876);
x_877 = lean_ctor_get(x_842, 12);
lean_inc_ref(x_877);
x_878 = lean_ctor_get(x_842, 13);
lean_inc_ref(x_878);
x_879 = lean_ctor_get(x_842, 14);
lean_inc(x_879);
x_880 = lean_ctor_get_uint8(x_842, sizeof(void*)*22);
x_881 = lean_ctor_get(x_842, 15);
lean_inc(x_881);
x_882 = lean_ctor_get(x_842, 16);
lean_inc_ref(x_882);
x_883 = lean_ctor_get(x_842, 17);
lean_inc_ref(x_883);
x_884 = lean_ctor_get(x_842, 18);
lean_inc_ref(x_884);
x_885 = lean_ctor_get(x_842, 19);
lean_inc_ref(x_885);
x_886 = lean_ctor_get(x_842, 20);
lean_inc_ref(x_886);
x_887 = lean_ctor_get_uint8(x_842, sizeof(void*)*22 + 1);
x_888 = lean_ctor_get(x_842, 21);
lean_inc_ref(x_888);
if (lean_is_exclusive(x_842)) {
 lean_ctor_release(x_842, 0);
 lean_ctor_release(x_842, 1);
 lean_ctor_release(x_842, 2);
 lean_ctor_release(x_842, 3);
 lean_ctor_release(x_842, 4);
 lean_ctor_release(x_842, 5);
 lean_ctor_release(x_842, 6);
 lean_ctor_release(x_842, 7);
 lean_ctor_release(x_842, 8);
 lean_ctor_release(x_842, 9);
 lean_ctor_release(x_842, 10);
 lean_ctor_release(x_842, 11);
 lean_ctor_release(x_842, 12);
 lean_ctor_release(x_842, 13);
 lean_ctor_release(x_842, 14);
 lean_ctor_release(x_842, 15);
 lean_ctor_release(x_842, 16);
 lean_ctor_release(x_842, 17);
 lean_ctor_release(x_842, 18);
 lean_ctor_release(x_842, 19);
 lean_ctor_release(x_842, 20);
 lean_ctor_release(x_842, 21);
 x_889 = x_842;
} else {
 lean_dec_ref(x_842);
 x_889 = lean_box(0);
}
x_890 = lean_box(0);
x_891 = l_Lean_PersistentArray_set___redArg(x_871, x_795, x_890);
if (lean_is_scalar(x_889)) {
 x_892 = lean_alloc_ctor(0, 22, 2);
} else {
 x_892 = x_889;
}
lean_ctor_set(x_892, 0, x_865);
lean_ctor_set(x_892, 1, x_866);
lean_ctor_set(x_892, 2, x_867);
lean_ctor_set(x_892, 3, x_868);
lean_ctor_set(x_892, 4, x_869);
lean_ctor_set(x_892, 5, x_870);
lean_ctor_set(x_892, 6, x_891);
lean_ctor_set(x_892, 7, x_872);
lean_ctor_set(x_892, 8, x_873);
lean_ctor_set(x_892, 9, x_874);
lean_ctor_set(x_892, 10, x_875);
lean_ctor_set(x_892, 11, x_876);
lean_ctor_set(x_892, 12, x_877);
lean_ctor_set(x_892, 13, x_878);
lean_ctor_set(x_892, 14, x_879);
lean_ctor_set(x_892, 15, x_881);
lean_ctor_set(x_892, 16, x_882);
lean_ctor_set(x_892, 17, x_883);
lean_ctor_set(x_892, 18, x_884);
lean_ctor_set(x_892, 19, x_885);
lean_ctor_set(x_892, 20, x_886);
lean_ctor_set(x_892, 21, x_888);
lean_ctor_set_uint8(x_892, sizeof(void*)*22, x_880);
lean_ctor_set_uint8(x_892, sizeof(void*)*22 + 1, x_887);
if (lean_is_scalar(x_864)) {
 x_893 = lean_alloc_ctor(0, 3, 0);
} else {
 x_893 = x_864;
}
lean_ctor_set(x_893, 0, x_862);
lean_ctor_set(x_893, 1, x_892);
lean_ctor_set(x_893, 2, x_863);
if (lean_is_scalar(x_861)) {
 x_894 = lean_alloc_ctor(0, 17, 1);
} else {
 x_894 = x_861;
}
lean_ctor_set(x_894, 0, x_844);
lean_ctor_set(x_894, 1, x_845);
lean_ctor_set(x_894, 2, x_846);
lean_ctor_set(x_894, 3, x_847);
lean_ctor_set(x_894, 4, x_848);
lean_ctor_set(x_894, 5, x_849);
lean_ctor_set(x_894, 6, x_850);
lean_ctor_set(x_894, 7, x_851);
lean_ctor_set(x_894, 8, x_853);
lean_ctor_set(x_894, 9, x_854);
lean_ctor_set(x_894, 10, x_855);
lean_ctor_set(x_894, 11, x_856);
lean_ctor_set(x_894, 12, x_857);
lean_ctor_set(x_894, 13, x_858);
lean_ctor_set(x_894, 14, x_893);
lean_ctor_set(x_894, 15, x_859);
lean_ctor_set(x_894, 16, x_860);
lean_ctor_set_uint8(x_894, sizeof(void*)*17, x_852);
x_895 = lean_st_ref_set(x_802, x_894, x_843);
x_896 = lean_ctor_get(x_895, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_895)) {
 lean_ctor_release(x_895, 0);
 lean_ctor_release(x_895, 1);
 x_897 = x_895;
} else {
 lean_dec_ref(x_895);
 x_897 = lean_box(0);
}
x_898 = lean_int_mul(x_837, x_828);
lean_dec(x_837);
lean_inc_ref(x_803);
x_899 = l_Int_Linear_Poly_mul(x_803, x_898);
lean_dec(x_898);
x_900 = lean_int_mul(x_838, x_798);
lean_dec(x_838);
lean_inc_ref(x_830);
x_901 = l_Int_Linear_Poly_mul(x_830, x_900);
lean_dec(x_900);
x_902 = lean_int_mul(x_798, x_828);
lean_dec(x_798);
x_903 = l_Int_Linear_Poly_combine(x_899, x_901);
lean_inc(x_836);
if (lean_is_scalar(x_831)) {
 x_904 = lean_alloc_ctor(1, 3, 0);
} else {
 x_904 = x_831;
}
lean_ctor_set(x_904, 0, x_836);
lean_ctor_set(x_904, 1, x_795);
lean_ctor_set(x_904, 2, x_903);
lean_inc(x_825);
lean_inc_ref(x_794);
if (lean_is_scalar(x_897)) {
 x_905 = lean_alloc_ctor(4, 2, 0);
} else {
 x_905 = x_897;
 lean_ctor_set_tag(x_905, 4);
}
lean_ctor_set(x_905, 0, x_794);
lean_ctor_set(x_905, 1, x_825);
x_906 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_906, 0, x_902);
lean_ctor_set(x_906, 1, x_904);
lean_ctor_set(x_906, 2, x_905);
lean_inc(x_799);
lean_inc_ref(x_791);
lean_inc(x_796);
lean_inc_ref(x_800);
lean_inc(x_793);
lean_inc_ref(x_801);
lean_inc(x_790);
lean_inc(x_802);
x_907 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_906, x_802, x_790, x_801, x_793, x_800, x_796, x_791, x_799, x_896);
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; 
x_908 = lean_ctor_get(x_907, 1);
lean_inc(x_908);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 lean_ctor_release(x_907, 1);
 x_909 = x_907;
} else {
 lean_dec_ref(x_907);
 x_909 = lean_box(0);
}
x_910 = l_Int_Linear_Poly_mul(x_803, x_829);
lean_dec(x_829);
x_911 = lean_int_neg(x_797);
lean_dec(x_797);
x_912 = l_Int_Linear_Poly_mul(x_830, x_911);
lean_dec(x_911);
x_913 = l_Int_Linear_Poly_combine(x_910, x_912);
lean_inc(x_825);
if (lean_is_scalar(x_909)) {
 x_914 = lean_alloc_ctor(5, 2, 0);
} else {
 x_914 = x_909;
 lean_ctor_set_tag(x_914, 5);
}
lean_ctor_set(x_914, 0, x_794);
lean_ctor_set(x_914, 1, x_825);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 lean_ctor_release(x_825, 2);
 x_915 = x_825;
} else {
 lean_dec_ref(x_825);
 x_915 = lean_box(0);
}
if (lean_is_scalar(x_915)) {
 x_916 = lean_alloc_ctor(0, 3, 0);
} else {
 x_916 = x_915;
}
lean_ctor_set(x_916, 0, x_836);
lean_ctor_set(x_916, 1, x_913);
lean_ctor_set(x_916, 2, x_914);
x_1 = x_916;
x_2 = x_802;
x_3 = x_790;
x_4 = x_801;
x_5 = x_793;
x_6 = x_800;
x_7 = x_796;
x_8 = x_791;
x_9 = x_799;
x_10 = x_908;
goto _start;
}
else
{
lean_dec(x_836);
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_825);
lean_dec_ref(x_803);
lean_dec(x_802);
lean_dec_ref(x_801);
lean_dec_ref(x_800);
lean_dec(x_799);
lean_dec(x_797);
lean_dec(x_796);
lean_dec_ref(x_794);
lean_dec(x_793);
lean_dec_ref(x_791);
lean_dec(x_790);
return x_907;
}
}
}
}
block_952:
{
lean_object* x_940; 
x_940 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_931, x_939);
if (lean_obj_tag(x_940) == 0)
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; uint8_t x_945; 
x_941 = lean_ctor_get(x_940, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_941, 6);
lean_inc_ref(x_942);
lean_dec(x_941);
x_943 = lean_ctor_get(x_940, 1);
lean_inc(x_943);
lean_dec_ref(x_940);
x_944 = lean_ctor_get(x_942, 2);
x_945 = lean_nat_dec_lt(x_926, x_944);
if (x_945 == 0)
{
lean_object* x_946; 
lean_dec_ref(x_942);
x_946 = l_outOfBounds___redArg(x_924);
x_790 = x_932;
x_791 = x_937;
x_792 = x_943;
x_793 = x_934;
x_794 = x_925;
x_795 = x_926;
x_796 = x_936;
x_797 = x_927;
x_798 = x_929;
x_799 = x_938;
x_800 = x_935;
x_801 = x_933;
x_802 = x_931;
x_803 = x_928;
x_804 = x_930;
x_805 = x_946;
goto block_918;
}
else
{
lean_object* x_947; 
x_947 = l_Lean_PersistentArray_get_x21___redArg(x_924, x_942, x_926);
x_790 = x_932;
x_791 = x_937;
x_792 = x_943;
x_793 = x_934;
x_794 = x_925;
x_795 = x_926;
x_796 = x_936;
x_797 = x_927;
x_798 = x_929;
x_799 = x_938;
x_800 = x_935;
x_801 = x_933;
x_802 = x_931;
x_803 = x_928;
x_804 = x_930;
x_805 = x_947;
goto block_918;
}
}
else
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; 
lean_dec(x_938);
lean_dec_ref(x_937);
lean_dec(x_936);
lean_dec_ref(x_935);
lean_dec(x_934);
lean_dec_ref(x_933);
lean_dec(x_932);
lean_dec(x_931);
lean_dec_ref(x_930);
lean_dec(x_929);
lean_dec_ref(x_928);
lean_dec(x_927);
lean_dec(x_926);
lean_dec_ref(x_925);
x_948 = lean_ctor_get(x_940, 0);
lean_inc(x_948);
x_949 = lean_ctor_get(x_940, 1);
lean_inc(x_949);
if (lean_is_exclusive(x_940)) {
 lean_ctor_release(x_940, 0);
 lean_ctor_release(x_940, 1);
 x_950 = x_940;
} else {
 lean_dec_ref(x_940);
 x_950 = lean_box(0);
}
if (lean_is_scalar(x_950)) {
 x_951 = lean_alloc_ctor(1, 2, 0);
} else {
 x_951 = x_950;
}
lean_ctor_set(x_951, 0, x_948);
lean_ctor_set(x_951, 1, x_949);
return x_951;
}
}
block_1028:
{
lean_object* x_962; lean_object* x_963; 
x_962 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_959);
x_963 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_962, x_953, x_954, x_955, x_956, x_957, x_958, x_959, x_960, x_961);
if (lean_obj_tag(x_963) == 0)
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; uint8_t x_968; 
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_963, 1);
lean_inc(x_965);
lean_dec_ref(x_963);
x_966 = lean_ctor_get(x_964, 0);
x_967 = lean_ctor_get(x_964, 1);
lean_inc(x_966);
x_968 = l_Int_Linear_Poly_isUnsatDvd(x_966, x_967);
if (x_968 == 0)
{
uint8_t x_969; 
x_969 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_964);
if (x_969 == 0)
{
lean_dec(x_923);
if (lean_obj_tag(x_967) == 0)
{
lean_object* x_970; 
x_970 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_964, x_953, x_954, x_955, x_956, x_957, x_958, x_959, x_960, x_965);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_958);
lean_dec_ref(x_957);
lean_dec(x_956);
lean_dec_ref(x_955);
lean_dec(x_954);
lean_dec(x_953);
return x_970;
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
lean_inc_ref(x_967);
lean_inc(x_966);
x_971 = lean_ctor_get(x_967, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_967, 1);
lean_inc(x_972);
x_973 = lean_ctor_get(x_967, 2);
lean_inc_ref(x_973);
lean_inc(x_964);
x_974 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_964, x_953, x_965);
if (lean_obj_tag(x_974) == 0)
{
lean_object* x_975; lean_object* x_976; uint8_t x_977; uint8_t x_978; uint8_t x_979; 
x_975 = lean_ctor_get(x_974, 0);
lean_inc(x_975);
x_976 = lean_ctor_get(x_974, 1);
lean_inc(x_976);
lean_dec_ref(x_974);
x_977 = 0;
x_978 = lean_unbox(x_975);
lean_dec(x_975);
x_979 = l_Lean_instBEqLBool_beq(x_978, x_977);
if (x_979 == 0)
{
x_925 = x_964;
x_926 = x_972;
x_927 = x_971;
x_928 = x_973;
x_929 = x_966;
x_930 = x_967;
x_931 = x_953;
x_932 = x_954;
x_933 = x_955;
x_934 = x_956;
x_935 = x_957;
x_936 = x_958;
x_937 = x_959;
x_938 = x_960;
x_939 = x_976;
goto block_952;
}
else
{
lean_object* x_980; 
x_980 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_972, x_953, x_976);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; 
x_981 = lean_ctor_get(x_980, 1);
lean_inc(x_981);
lean_dec_ref(x_980);
x_925 = x_964;
x_926 = x_972;
x_927 = x_971;
x_928 = x_973;
x_929 = x_966;
x_930 = x_967;
x_931 = x_953;
x_932 = x_954;
x_933 = x_955;
x_934 = x_956;
x_935 = x_957;
x_936 = x_958;
x_937 = x_959;
x_938 = x_960;
x_939 = x_981;
goto block_952;
}
else
{
lean_dec_ref(x_973);
lean_dec(x_972);
lean_dec(x_971);
lean_dec_ref(x_967);
lean_dec(x_966);
lean_dec(x_964);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_958);
lean_dec_ref(x_957);
lean_dec(x_956);
lean_dec_ref(x_955);
lean_dec(x_954);
lean_dec(x_953);
return x_980;
}
}
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; 
lean_dec_ref(x_973);
lean_dec(x_972);
lean_dec(x_971);
lean_dec_ref(x_967);
lean_dec(x_966);
lean_dec(x_964);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_958);
lean_dec_ref(x_957);
lean_dec(x_956);
lean_dec_ref(x_955);
lean_dec(x_954);
lean_dec(x_953);
x_982 = lean_ctor_get(x_974, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_974, 1);
lean_inc(x_983);
if (lean_is_exclusive(x_974)) {
 lean_ctor_release(x_974, 0);
 lean_ctor_release(x_974, 1);
 x_984 = x_974;
} else {
 lean_dec_ref(x_974);
 x_984 = lean_box(0);
}
if (lean_is_scalar(x_984)) {
 x_985 = lean_alloc_ctor(1, 2, 0);
} else {
 x_985 = x_984;
}
lean_ctor_set(x_985, 0, x_982);
lean_ctor_set(x_985, 1, x_983);
return x_985;
}
}
}
else
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; uint8_t x_989; 
lean_dec(x_956);
lean_dec_ref(x_955);
lean_dec(x_954);
x_986 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_987 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_986, x_959, x_965);
x_988 = lean_ctor_get(x_987, 0);
lean_inc(x_988);
x_989 = lean_unbox(x_988);
lean_dec(x_988);
if (x_989 == 0)
{
lean_object* x_990; 
lean_dec(x_964);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_958);
lean_dec_ref(x_957);
lean_dec(x_953);
lean_dec(x_923);
x_990 = lean_ctor_get(x_987, 1);
lean_inc(x_990);
lean_dec_ref(x_987);
x_185 = x_990;
goto block_188;
}
else
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_991 = lean_ctor_get(x_987, 1);
lean_inc(x_991);
if (lean_is_exclusive(x_987)) {
 lean_ctor_release(x_987, 0);
 lean_ctor_release(x_987, 1);
 x_992 = x_987;
} else {
 lean_dec_ref(x_987);
 x_992 = lean_box(0);
}
x_993 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_964, x_953, x_991);
lean_dec(x_953);
if (lean_obj_tag(x_993) == 0)
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_994 = lean_ctor_get(x_993, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_993, 1);
lean_inc(x_995);
lean_dec_ref(x_993);
x_996 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_992)) {
 x_997 = lean_alloc_ctor(7, 2, 0);
} else {
 x_997 = x_992;
 lean_ctor_set_tag(x_997, 7);
}
lean_ctor_set(x_997, 0, x_996);
lean_ctor_set(x_997, 1, x_994);
if (lean_is_scalar(x_923)) {
 x_998 = lean_alloc_ctor(7, 2, 0);
} else {
 x_998 = x_923;
 lean_ctor_set_tag(x_998, 7);
}
lean_ctor_set(x_998, 0, x_997);
lean_ctor_set(x_998, 1, x_996);
x_999 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_986, x_998, x_957, x_958, x_959, x_960, x_995);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_958);
lean_dec_ref(x_957);
x_1000 = lean_ctor_get(x_999, 1);
lean_inc(x_1000);
lean_dec_ref(x_999);
x_185 = x_1000;
goto block_188;
}
else
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
lean_dec(x_992);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_958);
lean_dec_ref(x_957);
lean_dec(x_923);
x_1001 = lean_ctor_get(x_993, 0);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_993, 1);
lean_inc(x_1002);
if (lean_is_exclusive(x_993)) {
 lean_ctor_release(x_993, 0);
 lean_ctor_release(x_993, 1);
 x_1003 = x_993;
} else {
 lean_dec_ref(x_993);
 x_1003 = lean_box(0);
}
if (lean_is_scalar(x_1003)) {
 x_1004 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1004 = x_1003;
}
lean_ctor_set(x_1004, 0, x_1001);
lean_ctor_set(x_1004, 1, x_1002);
return x_1004;
}
}
}
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; uint8_t x_1008; 
x_1005 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_1006 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_1005, x_959, x_965);
x_1007 = lean_ctor_get(x_1006, 0);
lean_inc(x_1007);
x_1008 = lean_unbox(x_1007);
lean_dec(x_1007);
if (x_1008 == 0)
{
lean_object* x_1009; 
lean_dec(x_923);
x_1009 = lean_ctor_get(x_1006, 1);
lean_inc(x_1009);
lean_dec_ref(x_1006);
x_166 = x_964;
x_167 = x_953;
x_168 = x_954;
x_169 = x_955;
x_170 = x_956;
x_171 = x_957;
x_172 = x_958;
x_173 = x_959;
x_174 = x_960;
x_175 = x_1009;
goto block_184;
}
else
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1010 = lean_ctor_get(x_1006, 1);
lean_inc(x_1010);
if (lean_is_exclusive(x_1006)) {
 lean_ctor_release(x_1006, 0);
 lean_ctor_release(x_1006, 1);
 x_1011 = x_1006;
} else {
 lean_dec_ref(x_1006);
 x_1011 = lean_box(0);
}
lean_inc(x_964);
x_1012 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_964, x_953, x_1010);
if (lean_obj_tag(x_1012) == 0)
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1013 = lean_ctor_get(x_1012, 0);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_1012, 1);
lean_inc(x_1014);
lean_dec_ref(x_1012);
x_1015 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_1011)) {
 x_1016 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1016 = x_1011;
 lean_ctor_set_tag(x_1016, 7);
}
lean_ctor_set(x_1016, 0, x_1015);
lean_ctor_set(x_1016, 1, x_1013);
if (lean_is_scalar(x_923)) {
 x_1017 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1017 = x_923;
 lean_ctor_set_tag(x_1017, 7);
}
lean_ctor_set(x_1017, 0, x_1016);
lean_ctor_set(x_1017, 1, x_1015);
x_1018 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_1005, x_1017, x_957, x_958, x_959, x_960, x_1014);
x_1019 = lean_ctor_get(x_1018, 1);
lean_inc(x_1019);
lean_dec_ref(x_1018);
x_166 = x_964;
x_167 = x_953;
x_168 = x_954;
x_169 = x_955;
x_170 = x_956;
x_171 = x_957;
x_172 = x_958;
x_173 = x_959;
x_174 = x_960;
x_175 = x_1019;
goto block_184;
}
else
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
lean_dec(x_1011);
lean_dec(x_964);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_958);
lean_dec_ref(x_957);
lean_dec(x_956);
lean_dec_ref(x_955);
lean_dec(x_954);
lean_dec(x_953);
lean_dec(x_923);
x_1020 = lean_ctor_get(x_1012, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1012, 1);
lean_inc(x_1021);
if (lean_is_exclusive(x_1012)) {
 lean_ctor_release(x_1012, 0);
 lean_ctor_release(x_1012, 1);
 x_1022 = x_1012;
} else {
 lean_dec_ref(x_1012);
 x_1022 = lean_box(0);
}
if (lean_is_scalar(x_1022)) {
 x_1023 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1023 = x_1022;
}
lean_ctor_set(x_1023, 0, x_1020);
lean_ctor_set(x_1023, 1, x_1021);
return x_1023;
}
}
}
}
else
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; 
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_958);
lean_dec_ref(x_957);
lean_dec(x_956);
lean_dec_ref(x_955);
lean_dec(x_954);
lean_dec(x_953);
lean_dec(x_923);
x_1024 = lean_ctor_get(x_963, 0);
lean_inc(x_1024);
x_1025 = lean_ctor_get(x_963, 1);
lean_inc(x_1025);
if (lean_is_exclusive(x_963)) {
 lean_ctor_release(x_963, 0);
 lean_ctor_release(x_963, 1);
 x_1026 = x_963;
} else {
 lean_dec_ref(x_963);
 x_1026 = lean_box(0);
}
if (lean_is_scalar(x_1026)) {
 x_1027 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1027 = x_1026;
}
lean_ctor_set(x_1027, 0, x_1024);
lean_ctor_set(x_1027, 1, x_1025);
return x_1027;
}
}
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
lean_dec_ref(x_781);
lean_dec(x_779);
lean_dec(x_777);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_771);
lean_dec(x_770);
lean_dec(x_769);
lean_dec(x_768);
lean_dec_ref(x_767);
lean_dec_ref(x_766);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1042 = lean_ctor_get(x_783, 1);
lean_inc(x_1042);
if (lean_is_exclusive(x_783)) {
 lean_ctor_release(x_783, 0);
 lean_ctor_release(x_783, 1);
 x_1043 = x_783;
} else {
 lean_dec_ref(x_783);
 x_1043 = lean_box(0);
}
x_1044 = lean_box(0);
if (lean_is_scalar(x_1043)) {
 x_1045 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1045 = x_1043;
}
lean_ctor_set(x_1045, 0, x_1044);
lean_ctor_set(x_1045, 1, x_1042);
return x_1045;
}
}
else
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; 
lean_dec_ref(x_781);
lean_dec(x_779);
lean_dec(x_777);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_771);
lean_dec(x_770);
lean_dec(x_769);
lean_dec(x_768);
lean_dec_ref(x_767);
lean_dec_ref(x_766);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1046 = lean_ctor_get(x_783, 0);
lean_inc(x_1046);
x_1047 = lean_ctor_get(x_783, 1);
lean_inc(x_1047);
if (lean_is_exclusive(x_783)) {
 lean_ctor_release(x_783, 0);
 lean_ctor_release(x_783, 1);
 x_1048 = x_783;
} else {
 lean_dec_ref(x_783);
 x_1048 = lean_box(0);
}
if (lean_is_scalar(x_1048)) {
 x_1049 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1049 = x_1048;
}
lean_ctor_set(x_1049, 0, x_1046);
lean_ctor_set(x_1049, 1, x_1047);
return x_1049;
}
}
else
{
lean_object* x_1050; 
lean_dec_ref(x_781);
lean_dec(x_779);
lean_dec(x_777);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_770);
lean_dec(x_769);
lean_dec(x_768);
lean_dec_ref(x_767);
lean_dec_ref(x_766);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1050 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_771, x_10);
return x_1050;
}
}
block_165:
{
lean_object* x_20; 
x_20 = l_Int_Linear_Poly_updateOccs___redArg(x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_st_ref_take(x_14, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 14);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec_ref(x_22);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_23, 14);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_24, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_25, 6);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_11);
x_34 = l_Lean_PersistentArray_set___redArg(x_32, x_12, x_33);
lean_dec(x_12);
lean_ctor_set(x_25, 6, x_34);
x_35 = lean_st_ref_set(x_14, x_23, x_26);
lean_dec(x_14);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
x_44 = lean_ctor_get(x_25, 2);
x_45 = lean_ctor_get(x_25, 3);
x_46 = lean_ctor_get(x_25, 4);
x_47 = lean_ctor_get(x_25, 5);
x_48 = lean_ctor_get(x_25, 6);
x_49 = lean_ctor_get(x_25, 7);
x_50 = lean_ctor_get(x_25, 8);
x_51 = lean_ctor_get(x_25, 9);
x_52 = lean_ctor_get(x_25, 10);
x_53 = lean_ctor_get(x_25, 11);
x_54 = lean_ctor_get(x_25, 12);
x_55 = lean_ctor_get(x_25, 13);
x_56 = lean_ctor_get(x_25, 14);
x_57 = lean_ctor_get_uint8(x_25, sizeof(void*)*22);
x_58 = lean_ctor_get(x_25, 15);
x_59 = lean_ctor_get(x_25, 16);
x_60 = lean_ctor_get(x_25, 17);
x_61 = lean_ctor_get(x_25, 18);
x_62 = lean_ctor_get(x_25, 19);
x_63 = lean_ctor_get(x_25, 20);
x_64 = lean_ctor_get_uint8(x_25, sizeof(void*)*22 + 1);
x_65 = lean_ctor_get(x_25, 21);
lean_inc(x_65);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
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
lean_dec(x_25);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_11);
x_67 = l_Lean_PersistentArray_set___redArg(x_48, x_12, x_66);
lean_dec(x_12);
x_68 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_68, 0, x_42);
lean_ctor_set(x_68, 1, x_43);
lean_ctor_set(x_68, 2, x_44);
lean_ctor_set(x_68, 3, x_45);
lean_ctor_set(x_68, 4, x_46);
lean_ctor_set(x_68, 5, x_47);
lean_ctor_set(x_68, 6, x_67);
lean_ctor_set(x_68, 7, x_49);
lean_ctor_set(x_68, 8, x_50);
lean_ctor_set(x_68, 9, x_51);
lean_ctor_set(x_68, 10, x_52);
lean_ctor_set(x_68, 11, x_53);
lean_ctor_set(x_68, 12, x_54);
lean_ctor_set(x_68, 13, x_55);
lean_ctor_set(x_68, 14, x_56);
lean_ctor_set(x_68, 15, x_58);
lean_ctor_set(x_68, 16, x_59);
lean_ctor_set(x_68, 17, x_60);
lean_ctor_set(x_68, 18, x_61);
lean_ctor_set(x_68, 19, x_62);
lean_ctor_set(x_68, 20, x_63);
lean_ctor_set(x_68, 21, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*22, x_57);
lean_ctor_set_uint8(x_68, sizeof(void*)*22 + 1, x_64);
lean_ctor_set(x_24, 1, x_68);
x_69 = lean_st_ref_set(x_14, x_23, x_26);
lean_dec(x_14);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_74 = lean_ctor_get(x_24, 0);
x_75 = lean_ctor_get(x_24, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_24);
x_76 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_25, 4);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_25, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_25, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_25, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_25, 8);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_25, 9);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_25, 10);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_25, 11);
lean_inc(x_87);
x_88 = lean_ctor_get(x_25, 12);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_25, 13);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_25, 14);
lean_inc(x_90);
x_91 = lean_ctor_get_uint8(x_25, sizeof(void*)*22);
x_92 = lean_ctor_get(x_25, 15);
lean_inc(x_92);
x_93 = lean_ctor_get(x_25, 16);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_25, 17);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_25, 18);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_25, 19);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_25, 20);
lean_inc_ref(x_97);
x_98 = lean_ctor_get_uint8(x_25, sizeof(void*)*22 + 1);
x_99 = lean_ctor_get(x_25, 21);
lean_inc_ref(x_99);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 lean_ctor_release(x_25, 5);
 lean_ctor_release(x_25, 6);
 lean_ctor_release(x_25, 7);
 lean_ctor_release(x_25, 8);
 lean_ctor_release(x_25, 9);
 lean_ctor_release(x_25, 10);
 lean_ctor_release(x_25, 11);
 lean_ctor_release(x_25, 12);
 lean_ctor_release(x_25, 13);
 lean_ctor_release(x_25, 14);
 lean_ctor_release(x_25, 15);
 lean_ctor_release(x_25, 16);
 lean_ctor_release(x_25, 17);
 lean_ctor_release(x_25, 18);
 lean_ctor_release(x_25, 19);
 lean_ctor_release(x_25, 20);
 lean_ctor_release(x_25, 21);
 x_100 = x_25;
} else {
 lean_dec_ref(x_25);
 x_100 = lean_box(0);
}
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_11);
x_102 = l_Lean_PersistentArray_set___redArg(x_82, x_12, x_101);
lean_dec(x_12);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 22, 2);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_76);
lean_ctor_set(x_103, 1, x_77);
lean_ctor_set(x_103, 2, x_78);
lean_ctor_set(x_103, 3, x_79);
lean_ctor_set(x_103, 4, x_80);
lean_ctor_set(x_103, 5, x_81);
lean_ctor_set(x_103, 6, x_102);
lean_ctor_set(x_103, 7, x_83);
lean_ctor_set(x_103, 8, x_84);
lean_ctor_set(x_103, 9, x_85);
lean_ctor_set(x_103, 10, x_86);
lean_ctor_set(x_103, 11, x_87);
lean_ctor_set(x_103, 12, x_88);
lean_ctor_set(x_103, 13, x_89);
lean_ctor_set(x_103, 14, x_90);
lean_ctor_set(x_103, 15, x_92);
lean_ctor_set(x_103, 16, x_93);
lean_ctor_set(x_103, 17, x_94);
lean_ctor_set(x_103, 18, x_95);
lean_ctor_set(x_103, 19, x_96);
lean_ctor_set(x_103, 20, x_97);
lean_ctor_set(x_103, 21, x_99);
lean_ctor_set_uint8(x_103, sizeof(void*)*22, x_91);
lean_ctor_set_uint8(x_103, sizeof(void*)*22 + 1, x_98);
x_104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_104, 0, x_74);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_75);
lean_ctor_set(x_23, 14, x_104);
x_105 = lean_st_ref_set(x_14, x_23, x_26);
lean_dec(x_14);
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
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_110 = lean_ctor_get(x_23, 0);
x_111 = lean_ctor_get(x_23, 1);
x_112 = lean_ctor_get(x_23, 2);
x_113 = lean_ctor_get(x_23, 3);
x_114 = lean_ctor_get(x_23, 4);
x_115 = lean_ctor_get(x_23, 5);
x_116 = lean_ctor_get(x_23, 6);
x_117 = lean_ctor_get(x_23, 7);
x_118 = lean_ctor_get_uint8(x_23, sizeof(void*)*17);
x_119 = lean_ctor_get(x_23, 8);
x_120 = lean_ctor_get(x_23, 9);
x_121 = lean_ctor_get(x_23, 10);
x_122 = lean_ctor_get(x_23, 11);
x_123 = lean_ctor_get(x_23, 12);
x_124 = lean_ctor_get(x_23, 13);
x_125 = lean_ctor_get(x_23, 15);
x_126 = lean_ctor_get(x_23, 16);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_23);
x_127 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_128);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_129 = x_24;
} else {
 lean_dec_ref(x_24);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_25, 4);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_25, 5);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_25, 6);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_25, 7);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_25, 8);
lean_inc_ref(x_138);
x_139 = lean_ctor_get(x_25, 9);
lean_inc_ref(x_139);
x_140 = lean_ctor_get(x_25, 10);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_25, 11);
lean_inc(x_141);
x_142 = lean_ctor_get(x_25, 12);
lean_inc_ref(x_142);
x_143 = lean_ctor_get(x_25, 13);
lean_inc_ref(x_143);
x_144 = lean_ctor_get(x_25, 14);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_25, sizeof(void*)*22);
x_146 = lean_ctor_get(x_25, 15);
lean_inc(x_146);
x_147 = lean_ctor_get(x_25, 16);
lean_inc_ref(x_147);
x_148 = lean_ctor_get(x_25, 17);
lean_inc_ref(x_148);
x_149 = lean_ctor_get(x_25, 18);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_25, 19);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_25, 20);
lean_inc_ref(x_151);
x_152 = lean_ctor_get_uint8(x_25, sizeof(void*)*22 + 1);
x_153 = lean_ctor_get(x_25, 21);
lean_inc_ref(x_153);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 lean_ctor_release(x_25, 5);
 lean_ctor_release(x_25, 6);
 lean_ctor_release(x_25, 7);
 lean_ctor_release(x_25, 8);
 lean_ctor_release(x_25, 9);
 lean_ctor_release(x_25, 10);
 lean_ctor_release(x_25, 11);
 lean_ctor_release(x_25, 12);
 lean_ctor_release(x_25, 13);
 lean_ctor_release(x_25, 14);
 lean_ctor_release(x_25, 15);
 lean_ctor_release(x_25, 16);
 lean_ctor_release(x_25, 17);
 lean_ctor_release(x_25, 18);
 lean_ctor_release(x_25, 19);
 lean_ctor_release(x_25, 20);
 lean_ctor_release(x_25, 21);
 x_154 = x_25;
} else {
 lean_dec_ref(x_25);
 x_154 = lean_box(0);
}
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_11);
x_156 = l_Lean_PersistentArray_set___redArg(x_136, x_12, x_155);
lean_dec(x_12);
if (lean_is_scalar(x_154)) {
 x_157 = lean_alloc_ctor(0, 22, 2);
} else {
 x_157 = x_154;
}
lean_ctor_set(x_157, 0, x_130);
lean_ctor_set(x_157, 1, x_131);
lean_ctor_set(x_157, 2, x_132);
lean_ctor_set(x_157, 3, x_133);
lean_ctor_set(x_157, 4, x_134);
lean_ctor_set(x_157, 5, x_135);
lean_ctor_set(x_157, 6, x_156);
lean_ctor_set(x_157, 7, x_137);
lean_ctor_set(x_157, 8, x_138);
lean_ctor_set(x_157, 9, x_139);
lean_ctor_set(x_157, 10, x_140);
lean_ctor_set(x_157, 11, x_141);
lean_ctor_set(x_157, 12, x_142);
lean_ctor_set(x_157, 13, x_143);
lean_ctor_set(x_157, 14, x_144);
lean_ctor_set(x_157, 15, x_146);
lean_ctor_set(x_157, 16, x_147);
lean_ctor_set(x_157, 17, x_148);
lean_ctor_set(x_157, 18, x_149);
lean_ctor_set(x_157, 19, x_150);
lean_ctor_set(x_157, 20, x_151);
lean_ctor_set(x_157, 21, x_153);
lean_ctor_set_uint8(x_157, sizeof(void*)*22, x_145);
lean_ctor_set_uint8(x_157, sizeof(void*)*22 + 1, x_152);
if (lean_is_scalar(x_129)) {
 x_158 = lean_alloc_ctor(0, 3, 0);
} else {
 x_158 = x_129;
}
lean_ctor_set(x_158, 0, x_127);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_158, 2, x_128);
x_159 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_159, 0, x_110);
lean_ctor_set(x_159, 1, x_111);
lean_ctor_set(x_159, 2, x_112);
lean_ctor_set(x_159, 3, x_113);
lean_ctor_set(x_159, 4, x_114);
lean_ctor_set(x_159, 5, x_115);
lean_ctor_set(x_159, 6, x_116);
lean_ctor_set(x_159, 7, x_117);
lean_ctor_set(x_159, 8, x_119);
lean_ctor_set(x_159, 9, x_120);
lean_ctor_set(x_159, 10, x_121);
lean_ctor_set(x_159, 11, x_122);
lean_ctor_set(x_159, 12, x_123);
lean_ctor_set(x_159, 13, x_124);
lean_ctor_set(x_159, 14, x_158);
lean_ctor_set(x_159, 15, x_125);
lean_ctor_set(x_159, 16, x_126);
lean_ctor_set_uint8(x_159, sizeof(void*)*17, x_118);
x_160 = lean_st_ref_set(x_14, x_159, x_26);
lean_dec(x_14);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = lean_box(0);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
return x_164;
}
}
else
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
return x_20;
}
}
block_184:
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_166);
x_177 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_176, x_167, x_168, x_169, x_170, x_171, x_172, x_173, x_174, x_175);
if (lean_obj_tag(x_177) == 0)
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_177, 0);
lean_dec(x_179);
x_180 = lean_box(0);
lean_ctor_set(x_177, 0, x_180);
return x_177;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
lean_dec(x_177);
x_182 = lean_box(0);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
return x_177;
}
}
block_188:
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
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

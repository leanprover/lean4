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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_188; uint8_t x_192; 
x_192 = !lean_is_exclusive(x_8);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_193 = lean_ctor_get(x_8, 0);
x_194 = lean_ctor_get(x_8, 1);
x_195 = lean_ctor_get(x_8, 2);
x_196 = lean_ctor_get(x_8, 3);
x_197 = lean_ctor_get(x_8, 4);
x_198 = lean_ctor_get(x_8, 5);
x_199 = lean_ctor_get(x_8, 6);
x_200 = lean_ctor_get(x_8, 7);
x_201 = lean_ctor_get(x_8, 8);
x_202 = lean_ctor_get(x_8, 9);
x_203 = lean_ctor_get(x_8, 10);
x_204 = lean_ctor_get(x_8, 11);
x_205 = lean_ctor_get(x_8, 12);
x_206 = lean_ctor_get(x_8, 13);
x_207 = lean_nat_dec_eq(x_196, x_197);
if (x_207 == 0)
{
lean_object* x_208; 
x_208 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; uint8_t x_210; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_unbox(x_209);
lean_dec(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_750; 
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec_ref(x_208);
x_212 = lean_unsigned_to_nat(1u);
x_213 = lean_nat_add(x_196, x_212);
lean_dec(x_196);
lean_ctor_set(x_8, 3, x_213);
x_614 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_615 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_614, x_8, x_211);
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_615, 1);
lean_inc(x_617);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 lean_ctor_release(x_615, 1);
 x_618 = x_615;
} else {
 lean_dec_ref(x_615);
 x_618 = lean_box(0);
}
x_619 = lean_box(0);
x_750 = lean_unbox(x_616);
lean_dec(x_616);
if (x_750 == 0)
{
x_648 = x_2;
x_649 = x_3;
x_650 = x_4;
x_651 = x_5;
x_652 = x_6;
x_653 = x_7;
x_654 = x_8;
x_655 = x_9;
x_656 = x_617;
goto block_749;
}
else
{
lean_object* x_751; 
lean_inc_ref(x_1);
x_751 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_617);
if (lean_obj_tag(x_751) == 0)
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_751, 1);
lean_inc(x_753);
lean_dec_ref(x_751);
x_754 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_755 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_755, 0, x_754);
lean_ctor_set(x_755, 1, x_752);
x_756 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_756, 0, x_755);
lean_ctor_set(x_756, 1, x_754);
x_757 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_614, x_756, x_6, x_7, x_8, x_9, x_753);
x_758 = lean_ctor_get(x_757, 1);
lean_inc(x_758);
lean_dec_ref(x_757);
x_648 = x_2;
x_649 = x_3;
x_650 = x_4;
x_651 = x_5;
x_652 = x_6;
x_653 = x_7;
x_654 = x_8;
x_655 = x_9;
x_656 = x_758;
goto block_749;
}
else
{
uint8_t x_759; 
lean_dec(x_618);
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_759 = !lean_is_exclusive(x_751);
if (x_759 == 0)
{
return x_751;
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; 
x_760 = lean_ctor_get(x_751, 0);
x_761 = lean_ctor_get(x_751, 1);
lean_inc(x_761);
lean_inc(x_760);
lean_dec(x_751);
x_762 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_762, 0, x_760);
lean_ctor_set(x_762, 1, x_761);
return x_762;
}
}
}
block_613:
{
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
lean_dec(x_228);
lean_dec(x_223);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec(x_217);
x_230 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_231 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_230, x_225, x_226);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_unbox(x_232);
lean_dec(x_232);
if (x_233 == 0)
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_231, 1);
lean_inc(x_234);
lean_dec_ref(x_231);
x_11 = x_221;
x_12 = x_224;
x_13 = x_216;
x_14 = x_222;
x_15 = x_215;
x_16 = x_227;
x_17 = x_225;
x_18 = x_214;
x_19 = x_234;
goto block_168;
}
else
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_231);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_231, 1);
x_237 = lean_ctor_get(x_231, 0);
lean_dec(x_237);
lean_inc_ref(x_221);
x_238 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_221, x_222, x_236);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec_ref(x_238);
x_241 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_231, 7);
lean_ctor_set(x_231, 1, x_239);
lean_ctor_set(x_231, 0, x_241);
x_242 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_242, 0, x_231);
lean_ctor_set(x_242, 1, x_241);
x_243 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_230, x_242, x_215, x_227, x_225, x_214, x_240);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec_ref(x_243);
x_11 = x_221;
x_12 = x_224;
x_13 = x_216;
x_14 = x_222;
x_15 = x_215;
x_16 = x_227;
x_17 = x_225;
x_18 = x_214;
x_19 = x_244;
goto block_168;
}
else
{
uint8_t x_245; 
lean_free_object(x_231);
lean_dec(x_227);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec_ref(x_216);
lean_dec_ref(x_215);
lean_dec(x_214);
x_245 = !lean_is_exclusive(x_238);
if (x_245 == 0)
{
return x_238;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_238, 0);
x_247 = lean_ctor_get(x_238, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_238);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_231, 1);
lean_inc(x_249);
lean_dec(x_231);
lean_inc_ref(x_221);
x_250 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_221, x_222, x_249);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec_ref(x_250);
x_253 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_251);
x_255 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
x_256 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_230, x_255, x_215, x_227, x_225, x_214, x_252);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
lean_dec_ref(x_256);
x_11 = x_221;
x_12 = x_224;
x_13 = x_216;
x_14 = x_222;
x_15 = x_215;
x_16 = x_227;
x_17 = x_225;
x_18 = x_214;
x_19 = x_257;
goto block_168;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_227);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec_ref(x_216);
lean_dec_ref(x_215);
lean_dec(x_214);
x_258 = lean_ctor_get(x_250, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_250, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_260 = x_250;
} else {
 lean_dec_ref(x_250);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
}
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec_ref(x_216);
x_262 = lean_ctor_get(x_229, 0);
lean_inc(x_262);
lean_dec_ref(x_229);
x_263 = lean_ctor_get(x_262, 1);
lean_inc_ref(x_263);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; 
lean_dec_ref(x_263);
lean_dec(x_228);
lean_dec(x_224);
lean_dec_ref(x_221);
lean_dec_ref(x_218);
lean_dec(x_217);
x_264 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_262, x_222, x_223, x_219, x_220, x_215, x_227, x_225, x_214, x_226);
lean_dec(x_214);
lean_dec_ref(x_225);
lean_dec(x_227);
lean_dec_ref(x_215);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_223);
lean_dec(x_222);
return x_264;
}
else
{
uint8_t x_265; 
x_265 = !lean_is_exclusive(x_263);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_266 = lean_ctor_get(x_262, 0);
x_267 = lean_ctor_get(x_263, 0);
x_268 = lean_ctor_get(x_263, 2);
x_269 = lean_ctor_get(x_263, 1);
lean_dec(x_269);
x_270 = lean_int_mul(x_228, x_266);
x_271 = lean_int_mul(x_267, x_217);
x_272 = l_Lean_Meta_Grind_Arith_gcdExt(x_270, x_271);
lean_dec(x_271);
lean_dec(x_270);
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
lean_dec_ref(x_272);
x_275 = lean_ctor_get(x_273, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_273, 1);
lean_inc(x_276);
lean_dec(x_273);
x_277 = lean_st_ref_take(x_222, x_226);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_278, 14);
lean_inc_ref(x_279);
x_280 = lean_ctor_get(x_279, 1);
lean_inc_ref(x_280);
x_281 = lean_ctor_get(x_277, 1);
lean_inc(x_281);
lean_dec_ref(x_277);
x_282 = !lean_is_exclusive(x_278);
if (x_282 == 0)
{
lean_object* x_283; uint8_t x_284; 
x_283 = lean_ctor_get(x_278, 14);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_279);
if (x_284 == 0)
{
lean_object* x_285; uint8_t x_286; 
x_285 = lean_ctor_get(x_279, 1);
lean_dec(x_285);
x_286 = !lean_is_exclusive(x_280);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_287 = lean_ctor_get(x_280, 6);
x_288 = lean_box(0);
x_289 = l_Lean_PersistentArray_set___redArg(x_287, x_224, x_288);
lean_ctor_set(x_280, 6, x_289);
x_290 = lean_st_ref_set(x_222, x_278, x_281);
x_291 = !lean_is_exclusive(x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_292 = lean_ctor_get(x_290, 1);
x_293 = lean_ctor_get(x_290, 0);
lean_dec(x_293);
x_294 = lean_int_mul(x_275, x_266);
lean_dec(x_275);
lean_inc_ref(x_218);
x_295 = l_Int_Linear_Poly_mul(x_218, x_294);
lean_dec(x_294);
x_296 = lean_int_mul(x_276, x_217);
lean_dec(x_276);
lean_inc_ref(x_268);
x_297 = l_Int_Linear_Poly_mul(x_268, x_296);
lean_dec(x_296);
x_298 = lean_int_mul(x_217, x_266);
lean_dec(x_217);
x_299 = l_Int_Linear_Poly_combine(x_295, x_297);
lean_inc(x_274);
lean_ctor_set(x_263, 2, x_299);
lean_ctor_set(x_263, 1, x_224);
lean_ctor_set(x_263, 0, x_274);
lean_inc(x_262);
lean_inc_ref(x_221);
lean_ctor_set_tag(x_290, 4);
lean_ctor_set(x_290, 1, x_262);
lean_ctor_set(x_290, 0, x_221);
x_300 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_263);
lean_ctor_set(x_300, 2, x_290);
lean_inc(x_214);
lean_inc_ref(x_225);
lean_inc(x_227);
lean_inc_ref(x_215);
lean_inc(x_220);
lean_inc_ref(x_219);
lean_inc(x_223);
lean_inc(x_222);
x_301 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_300, x_222, x_223, x_219, x_220, x_215, x_227, x_225, x_214, x_292);
if (lean_obj_tag(x_301) == 0)
{
uint8_t x_302; 
x_302 = !lean_is_exclusive(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_303 = lean_ctor_get(x_301, 1);
x_304 = lean_ctor_get(x_301, 0);
lean_dec(x_304);
x_305 = l_Int_Linear_Poly_mul(x_218, x_267);
lean_dec(x_267);
x_306 = lean_int_neg(x_228);
lean_dec(x_228);
x_307 = l_Int_Linear_Poly_mul(x_268, x_306);
lean_dec(x_306);
x_308 = l_Int_Linear_Poly_combine(x_305, x_307);
lean_inc(x_262);
lean_ctor_set_tag(x_301, 5);
lean_ctor_set(x_301, 1, x_262);
lean_ctor_set(x_301, 0, x_221);
x_309 = !lean_is_exclusive(x_262);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_262, 2);
lean_dec(x_310);
x_311 = lean_ctor_get(x_262, 1);
lean_dec(x_311);
x_312 = lean_ctor_get(x_262, 0);
lean_dec(x_312);
lean_ctor_set(x_262, 2, x_301);
lean_ctor_set(x_262, 1, x_308);
lean_ctor_set(x_262, 0, x_274);
x_1 = x_262;
x_2 = x_222;
x_3 = x_223;
x_4 = x_219;
x_5 = x_220;
x_6 = x_215;
x_7 = x_227;
x_8 = x_225;
x_9 = x_214;
x_10 = x_303;
goto _start;
}
else
{
lean_object* x_314; 
lean_dec(x_262);
x_314 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_314, 0, x_274);
lean_ctor_set(x_314, 1, x_308);
lean_ctor_set(x_314, 2, x_301);
x_1 = x_314;
x_2 = x_222;
x_3 = x_223;
x_4 = x_219;
x_5 = x_220;
x_6 = x_215;
x_7 = x_227;
x_8 = x_225;
x_9 = x_214;
x_10 = x_303;
goto _start;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_316 = lean_ctor_get(x_301, 1);
lean_inc(x_316);
lean_dec(x_301);
x_317 = l_Int_Linear_Poly_mul(x_218, x_267);
lean_dec(x_267);
x_318 = lean_int_neg(x_228);
lean_dec(x_228);
x_319 = l_Int_Linear_Poly_mul(x_268, x_318);
lean_dec(x_318);
x_320 = l_Int_Linear_Poly_combine(x_317, x_319);
lean_inc(x_262);
x_321 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_321, 0, x_221);
lean_ctor_set(x_321, 1, x_262);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 lean_ctor_release(x_262, 2);
 x_322 = x_262;
} else {
 lean_dec_ref(x_262);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(0, 3, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_274);
lean_ctor_set(x_323, 1, x_320);
lean_ctor_set(x_323, 2, x_321);
x_1 = x_323;
x_2 = x_222;
x_3 = x_223;
x_4 = x_219;
x_5 = x_220;
x_6 = x_215;
x_7 = x_227;
x_8 = x_225;
x_9 = x_214;
x_10 = x_316;
goto _start;
}
}
else
{
lean_dec(x_274);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec(x_262);
lean_dec(x_228);
lean_dec(x_227);
lean_dec_ref(x_225);
lean_dec(x_223);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec_ref(x_215);
lean_dec(x_214);
return x_301;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_325 = lean_ctor_get(x_290, 1);
lean_inc(x_325);
lean_dec(x_290);
x_326 = lean_int_mul(x_275, x_266);
lean_dec(x_275);
lean_inc_ref(x_218);
x_327 = l_Int_Linear_Poly_mul(x_218, x_326);
lean_dec(x_326);
x_328 = lean_int_mul(x_276, x_217);
lean_dec(x_276);
lean_inc_ref(x_268);
x_329 = l_Int_Linear_Poly_mul(x_268, x_328);
lean_dec(x_328);
x_330 = lean_int_mul(x_217, x_266);
lean_dec(x_217);
x_331 = l_Int_Linear_Poly_combine(x_327, x_329);
lean_inc(x_274);
lean_ctor_set(x_263, 2, x_331);
lean_ctor_set(x_263, 1, x_224);
lean_ctor_set(x_263, 0, x_274);
lean_inc(x_262);
lean_inc_ref(x_221);
x_332 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_332, 0, x_221);
lean_ctor_set(x_332, 1, x_262);
x_333 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_263);
lean_ctor_set(x_333, 2, x_332);
lean_inc(x_214);
lean_inc_ref(x_225);
lean_inc(x_227);
lean_inc_ref(x_215);
lean_inc(x_220);
lean_inc_ref(x_219);
lean_inc(x_223);
lean_inc(x_222);
x_334 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_333, x_222, x_223, x_219, x_220, x_215, x_227, x_225, x_214, x_325);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_335 = lean_ctor_get(x_334, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_336 = x_334;
} else {
 lean_dec_ref(x_334);
 x_336 = lean_box(0);
}
x_337 = l_Int_Linear_Poly_mul(x_218, x_267);
lean_dec(x_267);
x_338 = lean_int_neg(x_228);
lean_dec(x_228);
x_339 = l_Int_Linear_Poly_mul(x_268, x_338);
lean_dec(x_338);
x_340 = l_Int_Linear_Poly_combine(x_337, x_339);
lean_inc(x_262);
if (lean_is_scalar(x_336)) {
 x_341 = lean_alloc_ctor(5, 2, 0);
} else {
 x_341 = x_336;
 lean_ctor_set_tag(x_341, 5);
}
lean_ctor_set(x_341, 0, x_221);
lean_ctor_set(x_341, 1, x_262);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 lean_ctor_release(x_262, 2);
 x_342 = x_262;
} else {
 lean_dec_ref(x_262);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(0, 3, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_274);
lean_ctor_set(x_343, 1, x_340);
lean_ctor_set(x_343, 2, x_341);
x_1 = x_343;
x_2 = x_222;
x_3 = x_223;
x_4 = x_219;
x_5 = x_220;
x_6 = x_215;
x_7 = x_227;
x_8 = x_225;
x_9 = x_214;
x_10 = x_335;
goto _start;
}
else
{
lean_dec(x_274);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec(x_262);
lean_dec(x_228);
lean_dec(x_227);
lean_dec_ref(x_225);
lean_dec(x_223);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec_ref(x_215);
lean_dec(x_214);
return x_334;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_345 = lean_ctor_get(x_280, 0);
x_346 = lean_ctor_get(x_280, 1);
x_347 = lean_ctor_get(x_280, 2);
x_348 = lean_ctor_get(x_280, 3);
x_349 = lean_ctor_get(x_280, 4);
x_350 = lean_ctor_get(x_280, 5);
x_351 = lean_ctor_get(x_280, 6);
x_352 = lean_ctor_get(x_280, 7);
x_353 = lean_ctor_get(x_280, 8);
x_354 = lean_ctor_get(x_280, 9);
x_355 = lean_ctor_get(x_280, 10);
x_356 = lean_ctor_get(x_280, 11);
x_357 = lean_ctor_get(x_280, 12);
x_358 = lean_ctor_get(x_280, 13);
x_359 = lean_ctor_get(x_280, 14);
x_360 = lean_ctor_get_uint8(x_280, sizeof(void*)*22);
x_361 = lean_ctor_get(x_280, 15);
x_362 = lean_ctor_get(x_280, 16);
x_363 = lean_ctor_get(x_280, 17);
x_364 = lean_ctor_get(x_280, 18);
x_365 = lean_ctor_get(x_280, 19);
x_366 = lean_ctor_get(x_280, 20);
x_367 = lean_ctor_get_uint8(x_280, sizeof(void*)*22 + 1);
x_368 = lean_ctor_get(x_280, 21);
lean_inc(x_368);
lean_inc(x_366);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
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
lean_dec(x_280);
x_369 = lean_box(0);
x_370 = l_Lean_PersistentArray_set___redArg(x_351, x_224, x_369);
x_371 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_371, 0, x_345);
lean_ctor_set(x_371, 1, x_346);
lean_ctor_set(x_371, 2, x_347);
lean_ctor_set(x_371, 3, x_348);
lean_ctor_set(x_371, 4, x_349);
lean_ctor_set(x_371, 5, x_350);
lean_ctor_set(x_371, 6, x_370);
lean_ctor_set(x_371, 7, x_352);
lean_ctor_set(x_371, 8, x_353);
lean_ctor_set(x_371, 9, x_354);
lean_ctor_set(x_371, 10, x_355);
lean_ctor_set(x_371, 11, x_356);
lean_ctor_set(x_371, 12, x_357);
lean_ctor_set(x_371, 13, x_358);
lean_ctor_set(x_371, 14, x_359);
lean_ctor_set(x_371, 15, x_361);
lean_ctor_set(x_371, 16, x_362);
lean_ctor_set(x_371, 17, x_363);
lean_ctor_set(x_371, 18, x_364);
lean_ctor_set(x_371, 19, x_365);
lean_ctor_set(x_371, 20, x_366);
lean_ctor_set(x_371, 21, x_368);
lean_ctor_set_uint8(x_371, sizeof(void*)*22, x_360);
lean_ctor_set_uint8(x_371, sizeof(void*)*22 + 1, x_367);
lean_ctor_set(x_279, 1, x_371);
x_372 = lean_st_ref_set(x_222, x_278, x_281);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_374 = x_372;
} else {
 lean_dec_ref(x_372);
 x_374 = lean_box(0);
}
x_375 = lean_int_mul(x_275, x_266);
lean_dec(x_275);
lean_inc_ref(x_218);
x_376 = l_Int_Linear_Poly_mul(x_218, x_375);
lean_dec(x_375);
x_377 = lean_int_mul(x_276, x_217);
lean_dec(x_276);
lean_inc_ref(x_268);
x_378 = l_Int_Linear_Poly_mul(x_268, x_377);
lean_dec(x_377);
x_379 = lean_int_mul(x_217, x_266);
lean_dec(x_217);
x_380 = l_Int_Linear_Poly_combine(x_376, x_378);
lean_inc(x_274);
lean_ctor_set(x_263, 2, x_380);
lean_ctor_set(x_263, 1, x_224);
lean_ctor_set(x_263, 0, x_274);
lean_inc(x_262);
lean_inc_ref(x_221);
if (lean_is_scalar(x_374)) {
 x_381 = lean_alloc_ctor(4, 2, 0);
} else {
 x_381 = x_374;
 lean_ctor_set_tag(x_381, 4);
}
lean_ctor_set(x_381, 0, x_221);
lean_ctor_set(x_381, 1, x_262);
x_382 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_382, 0, x_379);
lean_ctor_set(x_382, 1, x_263);
lean_ctor_set(x_382, 2, x_381);
lean_inc(x_214);
lean_inc_ref(x_225);
lean_inc(x_227);
lean_inc_ref(x_215);
lean_inc(x_220);
lean_inc_ref(x_219);
lean_inc(x_223);
lean_inc(x_222);
x_383 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_382, x_222, x_223, x_219, x_220, x_215, x_227, x_225, x_214, x_373);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_384 = lean_ctor_get(x_383, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_385 = x_383;
} else {
 lean_dec_ref(x_383);
 x_385 = lean_box(0);
}
x_386 = l_Int_Linear_Poly_mul(x_218, x_267);
lean_dec(x_267);
x_387 = lean_int_neg(x_228);
lean_dec(x_228);
x_388 = l_Int_Linear_Poly_mul(x_268, x_387);
lean_dec(x_387);
x_389 = l_Int_Linear_Poly_combine(x_386, x_388);
lean_inc(x_262);
if (lean_is_scalar(x_385)) {
 x_390 = lean_alloc_ctor(5, 2, 0);
} else {
 x_390 = x_385;
 lean_ctor_set_tag(x_390, 5);
}
lean_ctor_set(x_390, 0, x_221);
lean_ctor_set(x_390, 1, x_262);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 lean_ctor_release(x_262, 2);
 x_391 = x_262;
} else {
 lean_dec_ref(x_262);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(0, 3, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_274);
lean_ctor_set(x_392, 1, x_389);
lean_ctor_set(x_392, 2, x_390);
x_1 = x_392;
x_2 = x_222;
x_3 = x_223;
x_4 = x_219;
x_5 = x_220;
x_6 = x_215;
x_7 = x_227;
x_8 = x_225;
x_9 = x_214;
x_10 = x_384;
goto _start;
}
else
{
lean_dec(x_274);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec(x_262);
lean_dec(x_228);
lean_dec(x_227);
lean_dec_ref(x_225);
lean_dec(x_223);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec_ref(x_215);
lean_dec(x_214);
return x_383;
}
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_394 = lean_ctor_get(x_279, 0);
x_395 = lean_ctor_get(x_279, 2);
x_396 = lean_ctor_get(x_279, 3);
lean_inc(x_396);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_279);
x_397 = lean_ctor_get(x_280, 0);
lean_inc_ref(x_397);
x_398 = lean_ctor_get(x_280, 1);
lean_inc_ref(x_398);
x_399 = lean_ctor_get(x_280, 2);
lean_inc_ref(x_399);
x_400 = lean_ctor_get(x_280, 3);
lean_inc_ref(x_400);
x_401 = lean_ctor_get(x_280, 4);
lean_inc_ref(x_401);
x_402 = lean_ctor_get(x_280, 5);
lean_inc_ref(x_402);
x_403 = lean_ctor_get(x_280, 6);
lean_inc_ref(x_403);
x_404 = lean_ctor_get(x_280, 7);
lean_inc_ref(x_404);
x_405 = lean_ctor_get(x_280, 8);
lean_inc_ref(x_405);
x_406 = lean_ctor_get(x_280, 9);
lean_inc_ref(x_406);
x_407 = lean_ctor_get(x_280, 10);
lean_inc_ref(x_407);
x_408 = lean_ctor_get(x_280, 11);
lean_inc(x_408);
x_409 = lean_ctor_get(x_280, 12);
lean_inc_ref(x_409);
x_410 = lean_ctor_get(x_280, 13);
lean_inc_ref(x_410);
x_411 = lean_ctor_get(x_280, 14);
lean_inc(x_411);
x_412 = lean_ctor_get_uint8(x_280, sizeof(void*)*22);
x_413 = lean_ctor_get(x_280, 15);
lean_inc(x_413);
x_414 = lean_ctor_get(x_280, 16);
lean_inc_ref(x_414);
x_415 = lean_ctor_get(x_280, 17);
lean_inc_ref(x_415);
x_416 = lean_ctor_get(x_280, 18);
lean_inc_ref(x_416);
x_417 = lean_ctor_get(x_280, 19);
lean_inc_ref(x_417);
x_418 = lean_ctor_get(x_280, 20);
lean_inc_ref(x_418);
x_419 = lean_ctor_get_uint8(x_280, sizeof(void*)*22 + 1);
x_420 = lean_ctor_get(x_280, 21);
lean_inc_ref(x_420);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 lean_ctor_release(x_280, 2);
 lean_ctor_release(x_280, 3);
 lean_ctor_release(x_280, 4);
 lean_ctor_release(x_280, 5);
 lean_ctor_release(x_280, 6);
 lean_ctor_release(x_280, 7);
 lean_ctor_release(x_280, 8);
 lean_ctor_release(x_280, 9);
 lean_ctor_release(x_280, 10);
 lean_ctor_release(x_280, 11);
 lean_ctor_release(x_280, 12);
 lean_ctor_release(x_280, 13);
 lean_ctor_release(x_280, 14);
 lean_ctor_release(x_280, 15);
 lean_ctor_release(x_280, 16);
 lean_ctor_release(x_280, 17);
 lean_ctor_release(x_280, 18);
 lean_ctor_release(x_280, 19);
 lean_ctor_release(x_280, 20);
 lean_ctor_release(x_280, 21);
 x_421 = x_280;
} else {
 lean_dec_ref(x_280);
 x_421 = lean_box(0);
}
x_422 = lean_box(0);
x_423 = l_Lean_PersistentArray_set___redArg(x_403, x_224, x_422);
if (lean_is_scalar(x_421)) {
 x_424 = lean_alloc_ctor(0, 22, 2);
} else {
 x_424 = x_421;
}
lean_ctor_set(x_424, 0, x_397);
lean_ctor_set(x_424, 1, x_398);
lean_ctor_set(x_424, 2, x_399);
lean_ctor_set(x_424, 3, x_400);
lean_ctor_set(x_424, 4, x_401);
lean_ctor_set(x_424, 5, x_402);
lean_ctor_set(x_424, 6, x_423);
lean_ctor_set(x_424, 7, x_404);
lean_ctor_set(x_424, 8, x_405);
lean_ctor_set(x_424, 9, x_406);
lean_ctor_set(x_424, 10, x_407);
lean_ctor_set(x_424, 11, x_408);
lean_ctor_set(x_424, 12, x_409);
lean_ctor_set(x_424, 13, x_410);
lean_ctor_set(x_424, 14, x_411);
lean_ctor_set(x_424, 15, x_413);
lean_ctor_set(x_424, 16, x_414);
lean_ctor_set(x_424, 17, x_415);
lean_ctor_set(x_424, 18, x_416);
lean_ctor_set(x_424, 19, x_417);
lean_ctor_set(x_424, 20, x_418);
lean_ctor_set(x_424, 21, x_420);
lean_ctor_set_uint8(x_424, sizeof(void*)*22, x_412);
lean_ctor_set_uint8(x_424, sizeof(void*)*22 + 1, x_419);
x_425 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_425, 0, x_394);
lean_ctor_set(x_425, 1, x_424);
lean_ctor_set(x_425, 2, x_395);
lean_ctor_set(x_425, 3, x_396);
lean_ctor_set(x_278, 14, x_425);
x_426 = lean_st_ref_set(x_222, x_278, x_281);
x_427 = lean_ctor_get(x_426, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_428 = x_426;
} else {
 lean_dec_ref(x_426);
 x_428 = lean_box(0);
}
x_429 = lean_int_mul(x_275, x_266);
lean_dec(x_275);
lean_inc_ref(x_218);
x_430 = l_Int_Linear_Poly_mul(x_218, x_429);
lean_dec(x_429);
x_431 = lean_int_mul(x_276, x_217);
lean_dec(x_276);
lean_inc_ref(x_268);
x_432 = l_Int_Linear_Poly_mul(x_268, x_431);
lean_dec(x_431);
x_433 = lean_int_mul(x_217, x_266);
lean_dec(x_217);
x_434 = l_Int_Linear_Poly_combine(x_430, x_432);
lean_inc(x_274);
lean_ctor_set(x_263, 2, x_434);
lean_ctor_set(x_263, 1, x_224);
lean_ctor_set(x_263, 0, x_274);
lean_inc(x_262);
lean_inc_ref(x_221);
if (lean_is_scalar(x_428)) {
 x_435 = lean_alloc_ctor(4, 2, 0);
} else {
 x_435 = x_428;
 lean_ctor_set_tag(x_435, 4);
}
lean_ctor_set(x_435, 0, x_221);
lean_ctor_set(x_435, 1, x_262);
x_436 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_436, 0, x_433);
lean_ctor_set(x_436, 1, x_263);
lean_ctor_set(x_436, 2, x_435);
lean_inc(x_214);
lean_inc_ref(x_225);
lean_inc(x_227);
lean_inc_ref(x_215);
lean_inc(x_220);
lean_inc_ref(x_219);
lean_inc(x_223);
lean_inc(x_222);
x_437 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_436, x_222, x_223, x_219, x_220, x_215, x_227, x_225, x_214, x_427);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_438 = lean_ctor_get(x_437, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_439 = x_437;
} else {
 lean_dec_ref(x_437);
 x_439 = lean_box(0);
}
x_440 = l_Int_Linear_Poly_mul(x_218, x_267);
lean_dec(x_267);
x_441 = lean_int_neg(x_228);
lean_dec(x_228);
x_442 = l_Int_Linear_Poly_mul(x_268, x_441);
lean_dec(x_441);
x_443 = l_Int_Linear_Poly_combine(x_440, x_442);
lean_inc(x_262);
if (lean_is_scalar(x_439)) {
 x_444 = lean_alloc_ctor(5, 2, 0);
} else {
 x_444 = x_439;
 lean_ctor_set_tag(x_444, 5);
}
lean_ctor_set(x_444, 0, x_221);
lean_ctor_set(x_444, 1, x_262);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 lean_ctor_release(x_262, 2);
 x_445 = x_262;
} else {
 lean_dec_ref(x_262);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(0, 3, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_274);
lean_ctor_set(x_446, 1, x_443);
lean_ctor_set(x_446, 2, x_444);
x_1 = x_446;
x_2 = x_222;
x_3 = x_223;
x_4 = x_219;
x_5 = x_220;
x_6 = x_215;
x_7 = x_227;
x_8 = x_225;
x_9 = x_214;
x_10 = x_438;
goto _start;
}
else
{
lean_dec(x_274);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec(x_262);
lean_dec(x_228);
lean_dec(x_227);
lean_dec_ref(x_225);
lean_dec(x_223);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec_ref(x_215);
lean_dec(x_214);
return x_437;
}
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; uint8_t x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_448 = lean_ctor_get(x_278, 0);
x_449 = lean_ctor_get(x_278, 1);
x_450 = lean_ctor_get(x_278, 2);
x_451 = lean_ctor_get(x_278, 3);
x_452 = lean_ctor_get(x_278, 4);
x_453 = lean_ctor_get(x_278, 5);
x_454 = lean_ctor_get(x_278, 6);
x_455 = lean_ctor_get(x_278, 7);
x_456 = lean_ctor_get_uint8(x_278, sizeof(void*)*18);
x_457 = lean_ctor_get(x_278, 8);
x_458 = lean_ctor_get(x_278, 9);
x_459 = lean_ctor_get(x_278, 10);
x_460 = lean_ctor_get(x_278, 11);
x_461 = lean_ctor_get(x_278, 12);
x_462 = lean_ctor_get(x_278, 13);
x_463 = lean_ctor_get(x_278, 15);
x_464 = lean_ctor_get(x_278, 16);
x_465 = lean_ctor_get(x_278, 17);
lean_inc(x_465);
lean_inc(x_464);
lean_inc(x_463);
lean_inc(x_462);
lean_inc(x_461);
lean_inc(x_460);
lean_inc(x_459);
lean_inc(x_458);
lean_inc(x_457);
lean_inc(x_455);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_278);
x_466 = lean_ctor_get(x_279, 0);
lean_inc_ref(x_466);
x_467 = lean_ctor_get(x_279, 2);
lean_inc_ref(x_467);
x_468 = lean_ctor_get(x_279, 3);
lean_inc_ref(x_468);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 lean_ctor_release(x_279, 3);
 x_469 = x_279;
} else {
 lean_dec_ref(x_279);
 x_469 = lean_box(0);
}
x_470 = lean_ctor_get(x_280, 0);
lean_inc_ref(x_470);
x_471 = lean_ctor_get(x_280, 1);
lean_inc_ref(x_471);
x_472 = lean_ctor_get(x_280, 2);
lean_inc_ref(x_472);
x_473 = lean_ctor_get(x_280, 3);
lean_inc_ref(x_473);
x_474 = lean_ctor_get(x_280, 4);
lean_inc_ref(x_474);
x_475 = lean_ctor_get(x_280, 5);
lean_inc_ref(x_475);
x_476 = lean_ctor_get(x_280, 6);
lean_inc_ref(x_476);
x_477 = lean_ctor_get(x_280, 7);
lean_inc_ref(x_477);
x_478 = lean_ctor_get(x_280, 8);
lean_inc_ref(x_478);
x_479 = lean_ctor_get(x_280, 9);
lean_inc_ref(x_479);
x_480 = lean_ctor_get(x_280, 10);
lean_inc_ref(x_480);
x_481 = lean_ctor_get(x_280, 11);
lean_inc(x_481);
x_482 = lean_ctor_get(x_280, 12);
lean_inc_ref(x_482);
x_483 = lean_ctor_get(x_280, 13);
lean_inc_ref(x_483);
x_484 = lean_ctor_get(x_280, 14);
lean_inc(x_484);
x_485 = lean_ctor_get_uint8(x_280, sizeof(void*)*22);
x_486 = lean_ctor_get(x_280, 15);
lean_inc(x_486);
x_487 = lean_ctor_get(x_280, 16);
lean_inc_ref(x_487);
x_488 = lean_ctor_get(x_280, 17);
lean_inc_ref(x_488);
x_489 = lean_ctor_get(x_280, 18);
lean_inc_ref(x_489);
x_490 = lean_ctor_get(x_280, 19);
lean_inc_ref(x_490);
x_491 = lean_ctor_get(x_280, 20);
lean_inc_ref(x_491);
x_492 = lean_ctor_get_uint8(x_280, sizeof(void*)*22 + 1);
x_493 = lean_ctor_get(x_280, 21);
lean_inc_ref(x_493);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 lean_ctor_release(x_280, 2);
 lean_ctor_release(x_280, 3);
 lean_ctor_release(x_280, 4);
 lean_ctor_release(x_280, 5);
 lean_ctor_release(x_280, 6);
 lean_ctor_release(x_280, 7);
 lean_ctor_release(x_280, 8);
 lean_ctor_release(x_280, 9);
 lean_ctor_release(x_280, 10);
 lean_ctor_release(x_280, 11);
 lean_ctor_release(x_280, 12);
 lean_ctor_release(x_280, 13);
 lean_ctor_release(x_280, 14);
 lean_ctor_release(x_280, 15);
 lean_ctor_release(x_280, 16);
 lean_ctor_release(x_280, 17);
 lean_ctor_release(x_280, 18);
 lean_ctor_release(x_280, 19);
 lean_ctor_release(x_280, 20);
 lean_ctor_release(x_280, 21);
 x_494 = x_280;
} else {
 lean_dec_ref(x_280);
 x_494 = lean_box(0);
}
x_495 = lean_box(0);
x_496 = l_Lean_PersistentArray_set___redArg(x_476, x_224, x_495);
if (lean_is_scalar(x_494)) {
 x_497 = lean_alloc_ctor(0, 22, 2);
} else {
 x_497 = x_494;
}
lean_ctor_set(x_497, 0, x_470);
lean_ctor_set(x_497, 1, x_471);
lean_ctor_set(x_497, 2, x_472);
lean_ctor_set(x_497, 3, x_473);
lean_ctor_set(x_497, 4, x_474);
lean_ctor_set(x_497, 5, x_475);
lean_ctor_set(x_497, 6, x_496);
lean_ctor_set(x_497, 7, x_477);
lean_ctor_set(x_497, 8, x_478);
lean_ctor_set(x_497, 9, x_479);
lean_ctor_set(x_497, 10, x_480);
lean_ctor_set(x_497, 11, x_481);
lean_ctor_set(x_497, 12, x_482);
lean_ctor_set(x_497, 13, x_483);
lean_ctor_set(x_497, 14, x_484);
lean_ctor_set(x_497, 15, x_486);
lean_ctor_set(x_497, 16, x_487);
lean_ctor_set(x_497, 17, x_488);
lean_ctor_set(x_497, 18, x_489);
lean_ctor_set(x_497, 19, x_490);
lean_ctor_set(x_497, 20, x_491);
lean_ctor_set(x_497, 21, x_493);
lean_ctor_set_uint8(x_497, sizeof(void*)*22, x_485);
lean_ctor_set_uint8(x_497, sizeof(void*)*22 + 1, x_492);
if (lean_is_scalar(x_469)) {
 x_498 = lean_alloc_ctor(0, 4, 0);
} else {
 x_498 = x_469;
}
lean_ctor_set(x_498, 0, x_466);
lean_ctor_set(x_498, 1, x_497);
lean_ctor_set(x_498, 2, x_467);
lean_ctor_set(x_498, 3, x_468);
x_499 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_499, 0, x_448);
lean_ctor_set(x_499, 1, x_449);
lean_ctor_set(x_499, 2, x_450);
lean_ctor_set(x_499, 3, x_451);
lean_ctor_set(x_499, 4, x_452);
lean_ctor_set(x_499, 5, x_453);
lean_ctor_set(x_499, 6, x_454);
lean_ctor_set(x_499, 7, x_455);
lean_ctor_set(x_499, 8, x_457);
lean_ctor_set(x_499, 9, x_458);
lean_ctor_set(x_499, 10, x_459);
lean_ctor_set(x_499, 11, x_460);
lean_ctor_set(x_499, 12, x_461);
lean_ctor_set(x_499, 13, x_462);
lean_ctor_set(x_499, 14, x_498);
lean_ctor_set(x_499, 15, x_463);
lean_ctor_set(x_499, 16, x_464);
lean_ctor_set(x_499, 17, x_465);
lean_ctor_set_uint8(x_499, sizeof(void*)*18, x_456);
x_500 = lean_st_ref_set(x_222, x_499, x_281);
x_501 = lean_ctor_get(x_500, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_502 = x_500;
} else {
 lean_dec_ref(x_500);
 x_502 = lean_box(0);
}
x_503 = lean_int_mul(x_275, x_266);
lean_dec(x_275);
lean_inc_ref(x_218);
x_504 = l_Int_Linear_Poly_mul(x_218, x_503);
lean_dec(x_503);
x_505 = lean_int_mul(x_276, x_217);
lean_dec(x_276);
lean_inc_ref(x_268);
x_506 = l_Int_Linear_Poly_mul(x_268, x_505);
lean_dec(x_505);
x_507 = lean_int_mul(x_217, x_266);
lean_dec(x_217);
x_508 = l_Int_Linear_Poly_combine(x_504, x_506);
lean_inc(x_274);
lean_ctor_set(x_263, 2, x_508);
lean_ctor_set(x_263, 1, x_224);
lean_ctor_set(x_263, 0, x_274);
lean_inc(x_262);
lean_inc_ref(x_221);
if (lean_is_scalar(x_502)) {
 x_509 = lean_alloc_ctor(4, 2, 0);
} else {
 x_509 = x_502;
 lean_ctor_set_tag(x_509, 4);
}
lean_ctor_set(x_509, 0, x_221);
lean_ctor_set(x_509, 1, x_262);
x_510 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_263);
lean_ctor_set(x_510, 2, x_509);
lean_inc(x_214);
lean_inc_ref(x_225);
lean_inc(x_227);
lean_inc_ref(x_215);
lean_inc(x_220);
lean_inc_ref(x_219);
lean_inc(x_223);
lean_inc(x_222);
x_511 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_510, x_222, x_223, x_219, x_220, x_215, x_227, x_225, x_214, x_501);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_512 = lean_ctor_get(x_511, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_513 = x_511;
} else {
 lean_dec_ref(x_511);
 x_513 = lean_box(0);
}
x_514 = l_Int_Linear_Poly_mul(x_218, x_267);
lean_dec(x_267);
x_515 = lean_int_neg(x_228);
lean_dec(x_228);
x_516 = l_Int_Linear_Poly_mul(x_268, x_515);
lean_dec(x_515);
x_517 = l_Int_Linear_Poly_combine(x_514, x_516);
lean_inc(x_262);
if (lean_is_scalar(x_513)) {
 x_518 = lean_alloc_ctor(5, 2, 0);
} else {
 x_518 = x_513;
 lean_ctor_set_tag(x_518, 5);
}
lean_ctor_set(x_518, 0, x_221);
lean_ctor_set(x_518, 1, x_262);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 lean_ctor_release(x_262, 2);
 x_519 = x_262;
} else {
 lean_dec_ref(x_262);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_519)) {
 x_520 = lean_alloc_ctor(0, 3, 0);
} else {
 x_520 = x_519;
}
lean_ctor_set(x_520, 0, x_274);
lean_ctor_set(x_520, 1, x_517);
lean_ctor_set(x_520, 2, x_518);
x_1 = x_520;
x_2 = x_222;
x_3 = x_223;
x_4 = x_219;
x_5 = x_220;
x_6 = x_215;
x_7 = x_227;
x_8 = x_225;
x_9 = x_214;
x_10 = x_512;
goto _start;
}
else
{
lean_dec(x_274);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec(x_262);
lean_dec(x_228);
lean_dec(x_227);
lean_dec_ref(x_225);
lean_dec(x_223);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec_ref(x_215);
lean_dec(x_214);
return x_511;
}
}
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; uint8_t x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; uint8_t x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; uint8_t x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_522 = lean_ctor_get(x_262, 0);
x_523 = lean_ctor_get(x_263, 0);
x_524 = lean_ctor_get(x_263, 2);
lean_inc(x_524);
lean_inc(x_523);
lean_dec(x_263);
x_525 = lean_int_mul(x_228, x_522);
x_526 = lean_int_mul(x_523, x_217);
x_527 = l_Lean_Meta_Grind_Arith_gcdExt(x_525, x_526);
lean_dec(x_526);
lean_dec(x_525);
x_528 = lean_ctor_get(x_527, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 0);
lean_inc(x_529);
lean_dec_ref(x_527);
x_530 = lean_ctor_get(x_528, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_528, 1);
lean_inc(x_531);
lean_dec(x_528);
x_532 = lean_st_ref_take(x_222, x_226);
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_533, 14);
lean_inc_ref(x_534);
x_535 = lean_ctor_get(x_534, 1);
lean_inc_ref(x_535);
x_536 = lean_ctor_get(x_532, 1);
lean_inc(x_536);
lean_dec_ref(x_532);
x_537 = lean_ctor_get(x_533, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_533, 1);
lean_inc_ref(x_538);
x_539 = lean_ctor_get(x_533, 2);
lean_inc(x_539);
x_540 = lean_ctor_get(x_533, 3);
lean_inc_ref(x_540);
x_541 = lean_ctor_get(x_533, 4);
lean_inc_ref(x_541);
x_542 = lean_ctor_get(x_533, 5);
lean_inc_ref(x_542);
x_543 = lean_ctor_get(x_533, 6);
lean_inc_ref(x_543);
x_544 = lean_ctor_get(x_533, 7);
lean_inc_ref(x_544);
x_545 = lean_ctor_get_uint8(x_533, sizeof(void*)*18);
x_546 = lean_ctor_get(x_533, 8);
lean_inc(x_546);
x_547 = lean_ctor_get(x_533, 9);
lean_inc_ref(x_547);
x_548 = lean_ctor_get(x_533, 10);
lean_inc_ref(x_548);
x_549 = lean_ctor_get(x_533, 11);
lean_inc_ref(x_549);
x_550 = lean_ctor_get(x_533, 12);
lean_inc_ref(x_550);
x_551 = lean_ctor_get(x_533, 13);
lean_inc_ref(x_551);
x_552 = lean_ctor_get(x_533, 15);
lean_inc_ref(x_552);
x_553 = lean_ctor_get(x_533, 16);
lean_inc_ref(x_553);
x_554 = lean_ctor_get(x_533, 17);
lean_inc_ref(x_554);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 lean_ctor_release(x_533, 2);
 lean_ctor_release(x_533, 3);
 lean_ctor_release(x_533, 4);
 lean_ctor_release(x_533, 5);
 lean_ctor_release(x_533, 6);
 lean_ctor_release(x_533, 7);
 lean_ctor_release(x_533, 8);
 lean_ctor_release(x_533, 9);
 lean_ctor_release(x_533, 10);
 lean_ctor_release(x_533, 11);
 lean_ctor_release(x_533, 12);
 lean_ctor_release(x_533, 13);
 lean_ctor_release(x_533, 14);
 lean_ctor_release(x_533, 15);
 lean_ctor_release(x_533, 16);
 lean_ctor_release(x_533, 17);
 x_555 = x_533;
} else {
 lean_dec_ref(x_533);
 x_555 = lean_box(0);
}
x_556 = lean_ctor_get(x_534, 0);
lean_inc_ref(x_556);
x_557 = lean_ctor_get(x_534, 2);
lean_inc_ref(x_557);
x_558 = lean_ctor_get(x_534, 3);
lean_inc_ref(x_558);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 lean_ctor_release(x_534, 2);
 lean_ctor_release(x_534, 3);
 x_559 = x_534;
} else {
 lean_dec_ref(x_534);
 x_559 = lean_box(0);
}
x_560 = lean_ctor_get(x_535, 0);
lean_inc_ref(x_560);
x_561 = lean_ctor_get(x_535, 1);
lean_inc_ref(x_561);
x_562 = lean_ctor_get(x_535, 2);
lean_inc_ref(x_562);
x_563 = lean_ctor_get(x_535, 3);
lean_inc_ref(x_563);
x_564 = lean_ctor_get(x_535, 4);
lean_inc_ref(x_564);
x_565 = lean_ctor_get(x_535, 5);
lean_inc_ref(x_565);
x_566 = lean_ctor_get(x_535, 6);
lean_inc_ref(x_566);
x_567 = lean_ctor_get(x_535, 7);
lean_inc_ref(x_567);
x_568 = lean_ctor_get(x_535, 8);
lean_inc_ref(x_568);
x_569 = lean_ctor_get(x_535, 9);
lean_inc_ref(x_569);
x_570 = lean_ctor_get(x_535, 10);
lean_inc_ref(x_570);
x_571 = lean_ctor_get(x_535, 11);
lean_inc(x_571);
x_572 = lean_ctor_get(x_535, 12);
lean_inc_ref(x_572);
x_573 = lean_ctor_get(x_535, 13);
lean_inc_ref(x_573);
x_574 = lean_ctor_get(x_535, 14);
lean_inc(x_574);
x_575 = lean_ctor_get_uint8(x_535, sizeof(void*)*22);
x_576 = lean_ctor_get(x_535, 15);
lean_inc(x_576);
x_577 = lean_ctor_get(x_535, 16);
lean_inc_ref(x_577);
x_578 = lean_ctor_get(x_535, 17);
lean_inc_ref(x_578);
x_579 = lean_ctor_get(x_535, 18);
lean_inc_ref(x_579);
x_580 = lean_ctor_get(x_535, 19);
lean_inc_ref(x_580);
x_581 = lean_ctor_get(x_535, 20);
lean_inc_ref(x_581);
x_582 = lean_ctor_get_uint8(x_535, sizeof(void*)*22 + 1);
x_583 = lean_ctor_get(x_535, 21);
lean_inc_ref(x_583);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 lean_ctor_release(x_535, 2);
 lean_ctor_release(x_535, 3);
 lean_ctor_release(x_535, 4);
 lean_ctor_release(x_535, 5);
 lean_ctor_release(x_535, 6);
 lean_ctor_release(x_535, 7);
 lean_ctor_release(x_535, 8);
 lean_ctor_release(x_535, 9);
 lean_ctor_release(x_535, 10);
 lean_ctor_release(x_535, 11);
 lean_ctor_release(x_535, 12);
 lean_ctor_release(x_535, 13);
 lean_ctor_release(x_535, 14);
 lean_ctor_release(x_535, 15);
 lean_ctor_release(x_535, 16);
 lean_ctor_release(x_535, 17);
 lean_ctor_release(x_535, 18);
 lean_ctor_release(x_535, 19);
 lean_ctor_release(x_535, 20);
 lean_ctor_release(x_535, 21);
 x_584 = x_535;
} else {
 lean_dec_ref(x_535);
 x_584 = lean_box(0);
}
x_585 = lean_box(0);
x_586 = l_Lean_PersistentArray_set___redArg(x_566, x_224, x_585);
if (lean_is_scalar(x_584)) {
 x_587 = lean_alloc_ctor(0, 22, 2);
} else {
 x_587 = x_584;
}
lean_ctor_set(x_587, 0, x_560);
lean_ctor_set(x_587, 1, x_561);
lean_ctor_set(x_587, 2, x_562);
lean_ctor_set(x_587, 3, x_563);
lean_ctor_set(x_587, 4, x_564);
lean_ctor_set(x_587, 5, x_565);
lean_ctor_set(x_587, 6, x_586);
lean_ctor_set(x_587, 7, x_567);
lean_ctor_set(x_587, 8, x_568);
lean_ctor_set(x_587, 9, x_569);
lean_ctor_set(x_587, 10, x_570);
lean_ctor_set(x_587, 11, x_571);
lean_ctor_set(x_587, 12, x_572);
lean_ctor_set(x_587, 13, x_573);
lean_ctor_set(x_587, 14, x_574);
lean_ctor_set(x_587, 15, x_576);
lean_ctor_set(x_587, 16, x_577);
lean_ctor_set(x_587, 17, x_578);
lean_ctor_set(x_587, 18, x_579);
lean_ctor_set(x_587, 19, x_580);
lean_ctor_set(x_587, 20, x_581);
lean_ctor_set(x_587, 21, x_583);
lean_ctor_set_uint8(x_587, sizeof(void*)*22, x_575);
lean_ctor_set_uint8(x_587, sizeof(void*)*22 + 1, x_582);
if (lean_is_scalar(x_559)) {
 x_588 = lean_alloc_ctor(0, 4, 0);
} else {
 x_588 = x_559;
}
lean_ctor_set(x_588, 0, x_556);
lean_ctor_set(x_588, 1, x_587);
lean_ctor_set(x_588, 2, x_557);
lean_ctor_set(x_588, 3, x_558);
if (lean_is_scalar(x_555)) {
 x_589 = lean_alloc_ctor(0, 18, 1);
} else {
 x_589 = x_555;
}
lean_ctor_set(x_589, 0, x_537);
lean_ctor_set(x_589, 1, x_538);
lean_ctor_set(x_589, 2, x_539);
lean_ctor_set(x_589, 3, x_540);
lean_ctor_set(x_589, 4, x_541);
lean_ctor_set(x_589, 5, x_542);
lean_ctor_set(x_589, 6, x_543);
lean_ctor_set(x_589, 7, x_544);
lean_ctor_set(x_589, 8, x_546);
lean_ctor_set(x_589, 9, x_547);
lean_ctor_set(x_589, 10, x_548);
lean_ctor_set(x_589, 11, x_549);
lean_ctor_set(x_589, 12, x_550);
lean_ctor_set(x_589, 13, x_551);
lean_ctor_set(x_589, 14, x_588);
lean_ctor_set(x_589, 15, x_552);
lean_ctor_set(x_589, 16, x_553);
lean_ctor_set(x_589, 17, x_554);
lean_ctor_set_uint8(x_589, sizeof(void*)*18, x_545);
x_590 = lean_st_ref_set(x_222, x_589, x_536);
x_591 = lean_ctor_get(x_590, 1);
lean_inc(x_591);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 x_592 = x_590;
} else {
 lean_dec_ref(x_590);
 x_592 = lean_box(0);
}
x_593 = lean_int_mul(x_530, x_522);
lean_dec(x_530);
lean_inc_ref(x_218);
x_594 = l_Int_Linear_Poly_mul(x_218, x_593);
lean_dec(x_593);
x_595 = lean_int_mul(x_531, x_217);
lean_dec(x_531);
lean_inc_ref(x_524);
x_596 = l_Int_Linear_Poly_mul(x_524, x_595);
lean_dec(x_595);
x_597 = lean_int_mul(x_217, x_522);
lean_dec(x_217);
x_598 = l_Int_Linear_Poly_combine(x_594, x_596);
lean_inc(x_529);
x_599 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_599, 0, x_529);
lean_ctor_set(x_599, 1, x_224);
lean_ctor_set(x_599, 2, x_598);
lean_inc(x_262);
lean_inc_ref(x_221);
if (lean_is_scalar(x_592)) {
 x_600 = lean_alloc_ctor(4, 2, 0);
} else {
 x_600 = x_592;
 lean_ctor_set_tag(x_600, 4);
}
lean_ctor_set(x_600, 0, x_221);
lean_ctor_set(x_600, 1, x_262);
x_601 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_601, 0, x_597);
lean_ctor_set(x_601, 1, x_599);
lean_ctor_set(x_601, 2, x_600);
lean_inc(x_214);
lean_inc_ref(x_225);
lean_inc(x_227);
lean_inc_ref(x_215);
lean_inc(x_220);
lean_inc_ref(x_219);
lean_inc(x_223);
lean_inc(x_222);
x_602 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_601, x_222, x_223, x_219, x_220, x_215, x_227, x_225, x_214, x_591);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_603 = lean_ctor_get(x_602, 1);
lean_inc(x_603);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_604 = x_602;
} else {
 lean_dec_ref(x_602);
 x_604 = lean_box(0);
}
x_605 = l_Int_Linear_Poly_mul(x_218, x_523);
lean_dec(x_523);
x_606 = lean_int_neg(x_228);
lean_dec(x_228);
x_607 = l_Int_Linear_Poly_mul(x_524, x_606);
lean_dec(x_606);
x_608 = l_Int_Linear_Poly_combine(x_605, x_607);
lean_inc(x_262);
if (lean_is_scalar(x_604)) {
 x_609 = lean_alloc_ctor(5, 2, 0);
} else {
 x_609 = x_604;
 lean_ctor_set_tag(x_609, 5);
}
lean_ctor_set(x_609, 0, x_221);
lean_ctor_set(x_609, 1, x_262);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 lean_ctor_release(x_262, 2);
 x_610 = x_262;
} else {
 lean_dec_ref(x_262);
 x_610 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_611 = lean_alloc_ctor(0, 3, 0);
} else {
 x_611 = x_610;
}
lean_ctor_set(x_611, 0, x_529);
lean_ctor_set(x_611, 1, x_608);
lean_ctor_set(x_611, 2, x_609);
x_1 = x_611;
x_2 = x_222;
x_3 = x_223;
x_4 = x_219;
x_5 = x_220;
x_6 = x_215;
x_7 = x_227;
x_8 = x_225;
x_9 = x_214;
x_10 = x_603;
goto _start;
}
else
{
lean_dec(x_529);
lean_dec_ref(x_524);
lean_dec(x_523);
lean_dec(x_262);
lean_dec(x_228);
lean_dec(x_227);
lean_dec_ref(x_225);
lean_dec(x_223);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec_ref(x_215);
lean_dec(x_214);
return x_602;
}
}
}
}
}
block_647:
{
lean_object* x_635; 
x_635 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_626, x_634);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; uint8_t x_640; 
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_636, 6);
lean_inc_ref(x_637);
lean_dec(x_636);
x_638 = lean_ctor_get(x_635, 1);
lean_inc(x_638);
lean_dec_ref(x_635);
x_639 = lean_ctor_get(x_637, 2);
x_640 = lean_nat_dec_lt(x_622, x_639);
if (x_640 == 0)
{
lean_object* x_641; 
lean_dec_ref(x_637);
x_641 = l_outOfBounds___redArg(x_619);
x_214 = x_633;
x_215 = x_630;
x_216 = x_623;
x_217 = x_625;
x_218 = x_620;
x_219 = x_628;
x_220 = x_629;
x_221 = x_621;
x_222 = x_626;
x_223 = x_627;
x_224 = x_622;
x_225 = x_632;
x_226 = x_638;
x_227 = x_631;
x_228 = x_624;
x_229 = x_641;
goto block_613;
}
else
{
lean_object* x_642; 
x_642 = l_Lean_PersistentArray_get_x21___redArg(x_619, x_637, x_622);
x_214 = x_633;
x_215 = x_630;
x_216 = x_623;
x_217 = x_625;
x_218 = x_620;
x_219 = x_628;
x_220 = x_629;
x_221 = x_621;
x_222 = x_626;
x_223 = x_627;
x_224 = x_622;
x_225 = x_632;
x_226 = x_638;
x_227 = x_631;
x_228 = x_624;
x_229 = x_642;
goto block_613;
}
}
else
{
uint8_t x_643; 
lean_dec(x_633);
lean_dec_ref(x_632);
lean_dec(x_631);
lean_dec_ref(x_630);
lean_dec(x_629);
lean_dec_ref(x_628);
lean_dec(x_627);
lean_dec(x_626);
lean_dec(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec_ref(x_621);
lean_dec_ref(x_620);
x_643 = !lean_is_exclusive(x_635);
if (x_643 == 0)
{
return x_635;
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_644 = lean_ctor_get(x_635, 0);
x_645 = lean_ctor_get(x_635, 1);
lean_inc(x_645);
lean_inc(x_644);
lean_dec(x_635);
x_646 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_646, 0, x_644);
lean_ctor_set(x_646, 1, x_645);
return x_646;
}
}
}
block_749:
{
lean_object* x_657; lean_object* x_658; 
x_657 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_654);
x_658 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_657, x_648, x_649, x_650, x_651, x_652, x_653, x_654, x_655, x_656);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; uint8_t x_663; 
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_658, 1);
lean_inc(x_660);
lean_dec_ref(x_658);
x_661 = lean_ctor_get(x_659, 0);
x_662 = lean_ctor_get(x_659, 1);
lean_inc(x_661);
x_663 = l_Int_Linear_Poly_isUnsatDvd(x_661, x_662);
if (x_663 == 0)
{
uint8_t x_664; 
x_664 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_659);
if (x_664 == 0)
{
lean_dec(x_618);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_665; 
x_665 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_659, x_648, x_649, x_650, x_651, x_652, x_653, x_654, x_655, x_660);
lean_dec(x_655);
lean_dec_ref(x_654);
lean_dec(x_653);
lean_dec_ref(x_652);
lean_dec(x_651);
lean_dec_ref(x_650);
lean_dec(x_649);
lean_dec(x_648);
return x_665;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_inc_ref(x_662);
lean_inc(x_661);
x_666 = lean_ctor_get(x_662, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_662, 1);
lean_inc(x_667);
x_668 = lean_ctor_get(x_662, 2);
lean_inc_ref(x_668);
lean_inc(x_659);
x_669 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_659, x_648, x_660);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; lean_object* x_671; uint8_t x_672; uint8_t x_673; uint8_t x_674; 
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_669, 1);
lean_inc(x_671);
lean_dec_ref(x_669);
x_672 = 0;
x_673 = lean_unbox(x_670);
lean_dec(x_670);
x_674 = l_Lean_instBEqLBool_beq(x_673, x_672);
if (x_674 == 0)
{
x_620 = x_668;
x_621 = x_659;
x_622 = x_667;
x_623 = x_662;
x_624 = x_666;
x_625 = x_661;
x_626 = x_648;
x_627 = x_649;
x_628 = x_650;
x_629 = x_651;
x_630 = x_652;
x_631 = x_653;
x_632 = x_654;
x_633 = x_655;
x_634 = x_671;
goto block_647;
}
else
{
lean_object* x_675; 
x_675 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_667, x_648, x_671);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; 
x_676 = lean_ctor_get(x_675, 1);
lean_inc(x_676);
lean_dec_ref(x_675);
x_620 = x_668;
x_621 = x_659;
x_622 = x_667;
x_623 = x_662;
x_624 = x_666;
x_625 = x_661;
x_626 = x_648;
x_627 = x_649;
x_628 = x_650;
x_629 = x_651;
x_630 = x_652;
x_631 = x_653;
x_632 = x_654;
x_633 = x_655;
x_634 = x_676;
goto block_647;
}
else
{
lean_dec_ref(x_668);
lean_dec(x_667);
lean_dec(x_666);
lean_dec_ref(x_662);
lean_dec(x_661);
lean_dec(x_659);
lean_dec(x_655);
lean_dec_ref(x_654);
lean_dec(x_653);
lean_dec_ref(x_652);
lean_dec(x_651);
lean_dec_ref(x_650);
lean_dec(x_649);
lean_dec(x_648);
return x_675;
}
}
}
else
{
uint8_t x_677; 
lean_dec_ref(x_668);
lean_dec(x_667);
lean_dec(x_666);
lean_dec_ref(x_662);
lean_dec(x_661);
lean_dec(x_659);
lean_dec(x_655);
lean_dec_ref(x_654);
lean_dec(x_653);
lean_dec_ref(x_652);
lean_dec(x_651);
lean_dec_ref(x_650);
lean_dec(x_649);
lean_dec(x_648);
x_677 = !lean_is_exclusive(x_669);
if (x_677 == 0)
{
return x_669;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_678 = lean_ctor_get(x_669, 0);
x_679 = lean_ctor_get(x_669, 1);
lean_inc(x_679);
lean_inc(x_678);
lean_dec(x_669);
x_680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_680, 0, x_678);
lean_ctor_set(x_680, 1, x_679);
return x_680;
}
}
}
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; 
lean_dec(x_651);
lean_dec_ref(x_650);
lean_dec(x_649);
x_681 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_682 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_681, x_654, x_660);
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
x_684 = lean_unbox(x_683);
lean_dec(x_683);
if (x_684 == 0)
{
lean_object* x_685; 
lean_dec(x_659);
lean_dec(x_655);
lean_dec_ref(x_654);
lean_dec(x_653);
lean_dec_ref(x_652);
lean_dec(x_648);
lean_dec(x_618);
x_685 = lean_ctor_get(x_682, 1);
lean_inc(x_685);
lean_dec_ref(x_682);
x_188 = x_685;
goto block_191;
}
else
{
uint8_t x_686; 
x_686 = !lean_is_exclusive(x_682);
if (x_686 == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_687 = lean_ctor_get(x_682, 1);
x_688 = lean_ctor_get(x_682, 0);
lean_dec(x_688);
x_689 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_659, x_648, x_687);
lean_dec(x_648);
if (lean_obj_tag(x_689) == 0)
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_690 = lean_ctor_get(x_689, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_689, 1);
lean_inc(x_691);
lean_dec_ref(x_689);
x_692 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_682, 7);
lean_ctor_set(x_682, 1, x_690);
lean_ctor_set(x_682, 0, x_692);
if (lean_is_scalar(x_618)) {
 x_693 = lean_alloc_ctor(7, 2, 0);
} else {
 x_693 = x_618;
 lean_ctor_set_tag(x_693, 7);
}
lean_ctor_set(x_693, 0, x_682);
lean_ctor_set(x_693, 1, x_692);
x_694 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_681, x_693, x_652, x_653, x_654, x_655, x_691);
lean_dec(x_655);
lean_dec_ref(x_654);
lean_dec(x_653);
lean_dec_ref(x_652);
x_695 = lean_ctor_get(x_694, 1);
lean_inc(x_695);
lean_dec_ref(x_694);
x_188 = x_695;
goto block_191;
}
else
{
uint8_t x_696; 
lean_free_object(x_682);
lean_dec(x_655);
lean_dec_ref(x_654);
lean_dec(x_653);
lean_dec_ref(x_652);
lean_dec(x_618);
x_696 = !lean_is_exclusive(x_689);
if (x_696 == 0)
{
return x_689;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_697 = lean_ctor_get(x_689, 0);
x_698 = lean_ctor_get(x_689, 1);
lean_inc(x_698);
lean_inc(x_697);
lean_dec(x_689);
x_699 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_699, 0, x_697);
lean_ctor_set(x_699, 1, x_698);
return x_699;
}
}
}
else
{
lean_object* x_700; lean_object* x_701; 
x_700 = lean_ctor_get(x_682, 1);
lean_inc(x_700);
lean_dec(x_682);
x_701 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_659, x_648, x_700);
lean_dec(x_648);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
lean_dec_ref(x_701);
x_704 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_705 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_702);
if (lean_is_scalar(x_618)) {
 x_706 = lean_alloc_ctor(7, 2, 0);
} else {
 x_706 = x_618;
 lean_ctor_set_tag(x_706, 7);
}
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_704);
x_707 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_681, x_706, x_652, x_653, x_654, x_655, x_703);
lean_dec(x_655);
lean_dec_ref(x_654);
lean_dec(x_653);
lean_dec_ref(x_652);
x_708 = lean_ctor_get(x_707, 1);
lean_inc(x_708);
lean_dec_ref(x_707);
x_188 = x_708;
goto block_191;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_dec(x_655);
lean_dec_ref(x_654);
lean_dec(x_653);
lean_dec_ref(x_652);
lean_dec(x_618);
x_709 = lean_ctor_get(x_701, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_701, 1);
lean_inc(x_710);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 lean_ctor_release(x_701, 1);
 x_711 = x_701;
} else {
 lean_dec_ref(x_701);
 x_711 = lean_box(0);
}
if (lean_is_scalar(x_711)) {
 x_712 = lean_alloc_ctor(1, 2, 0);
} else {
 x_712 = x_711;
}
lean_ctor_set(x_712, 0, x_709);
lean_ctor_set(x_712, 1, x_710);
return x_712;
}
}
}
}
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; uint8_t x_716; 
x_713 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_714 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_713, x_654, x_660);
x_715 = lean_ctor_get(x_714, 0);
lean_inc(x_715);
x_716 = lean_unbox(x_715);
lean_dec(x_715);
if (x_716 == 0)
{
lean_object* x_717; 
lean_dec(x_618);
x_717 = lean_ctor_get(x_714, 1);
lean_inc(x_717);
lean_dec_ref(x_714);
x_169 = x_659;
x_170 = x_648;
x_171 = x_649;
x_172 = x_650;
x_173 = x_651;
x_174 = x_652;
x_175 = x_653;
x_176 = x_654;
x_177 = x_655;
x_178 = x_717;
goto block_187;
}
else
{
uint8_t x_718; 
x_718 = !lean_is_exclusive(x_714);
if (x_718 == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_719 = lean_ctor_get(x_714, 1);
x_720 = lean_ctor_get(x_714, 0);
lean_dec(x_720);
lean_inc(x_659);
x_721 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_659, x_648, x_719);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec_ref(x_721);
x_724 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_714, 7);
lean_ctor_set(x_714, 1, x_722);
lean_ctor_set(x_714, 0, x_724);
if (lean_is_scalar(x_618)) {
 x_725 = lean_alloc_ctor(7, 2, 0);
} else {
 x_725 = x_618;
 lean_ctor_set_tag(x_725, 7);
}
lean_ctor_set(x_725, 0, x_714);
lean_ctor_set(x_725, 1, x_724);
x_726 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_713, x_725, x_652, x_653, x_654, x_655, x_723);
x_727 = lean_ctor_get(x_726, 1);
lean_inc(x_727);
lean_dec_ref(x_726);
x_169 = x_659;
x_170 = x_648;
x_171 = x_649;
x_172 = x_650;
x_173 = x_651;
x_174 = x_652;
x_175 = x_653;
x_176 = x_654;
x_177 = x_655;
x_178 = x_727;
goto block_187;
}
else
{
uint8_t x_728; 
lean_free_object(x_714);
lean_dec(x_659);
lean_dec(x_655);
lean_dec_ref(x_654);
lean_dec(x_653);
lean_dec_ref(x_652);
lean_dec(x_651);
lean_dec_ref(x_650);
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_618);
x_728 = !lean_is_exclusive(x_721);
if (x_728 == 0)
{
return x_721;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_729 = lean_ctor_get(x_721, 0);
x_730 = lean_ctor_get(x_721, 1);
lean_inc(x_730);
lean_inc(x_729);
lean_dec(x_721);
x_731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_731, 0, x_729);
lean_ctor_set(x_731, 1, x_730);
return x_731;
}
}
}
else
{
lean_object* x_732; lean_object* x_733; 
x_732 = lean_ctor_get(x_714, 1);
lean_inc(x_732);
lean_dec(x_714);
lean_inc(x_659);
x_733 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_659, x_648, x_732);
if (lean_obj_tag(x_733) == 0)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_734 = lean_ctor_get(x_733, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_733, 1);
lean_inc(x_735);
lean_dec_ref(x_733);
x_736 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_737 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_734);
if (lean_is_scalar(x_618)) {
 x_738 = lean_alloc_ctor(7, 2, 0);
} else {
 x_738 = x_618;
 lean_ctor_set_tag(x_738, 7);
}
lean_ctor_set(x_738, 0, x_737);
lean_ctor_set(x_738, 1, x_736);
x_739 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_713, x_738, x_652, x_653, x_654, x_655, x_735);
x_740 = lean_ctor_get(x_739, 1);
lean_inc(x_740);
lean_dec_ref(x_739);
x_169 = x_659;
x_170 = x_648;
x_171 = x_649;
x_172 = x_650;
x_173 = x_651;
x_174 = x_652;
x_175 = x_653;
x_176 = x_654;
x_177 = x_655;
x_178 = x_740;
goto block_187;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
lean_dec(x_659);
lean_dec(x_655);
lean_dec_ref(x_654);
lean_dec(x_653);
lean_dec_ref(x_652);
lean_dec(x_651);
lean_dec_ref(x_650);
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_618);
x_741 = lean_ctor_get(x_733, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_733, 1);
lean_inc(x_742);
if (lean_is_exclusive(x_733)) {
 lean_ctor_release(x_733, 0);
 lean_ctor_release(x_733, 1);
 x_743 = x_733;
} else {
 lean_dec_ref(x_733);
 x_743 = lean_box(0);
}
if (lean_is_scalar(x_743)) {
 x_744 = lean_alloc_ctor(1, 2, 0);
} else {
 x_744 = x_743;
}
lean_ctor_set(x_744, 0, x_741);
lean_ctor_set(x_744, 1, x_742);
return x_744;
}
}
}
}
}
else
{
uint8_t x_745; 
lean_dec(x_655);
lean_dec_ref(x_654);
lean_dec(x_653);
lean_dec_ref(x_652);
lean_dec(x_651);
lean_dec_ref(x_650);
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_618);
x_745 = !lean_is_exclusive(x_658);
if (x_745 == 0)
{
return x_658;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_746 = lean_ctor_get(x_658, 0);
x_747 = lean_ctor_get(x_658, 1);
lean_inc(x_747);
lean_inc(x_746);
lean_dec(x_658);
x_748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
return x_748;
}
}
}
}
else
{
uint8_t x_763; 
lean_free_object(x_8);
lean_dec_ref(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_763 = !lean_is_exclusive(x_208);
if (x_763 == 0)
{
lean_object* x_764; lean_object* x_765; 
x_764 = lean_ctor_get(x_208, 0);
lean_dec(x_764);
x_765 = lean_box(0);
lean_ctor_set(x_208, 0, x_765);
return x_208;
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; 
x_766 = lean_ctor_get(x_208, 1);
lean_inc(x_766);
lean_dec(x_208);
x_767 = lean_box(0);
x_768 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_768, 0, x_767);
lean_ctor_set(x_768, 1, x_766);
return x_768;
}
}
}
else
{
uint8_t x_769; 
lean_free_object(x_8);
lean_dec_ref(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_769 = !lean_is_exclusive(x_208);
if (x_769 == 0)
{
return x_208;
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_770 = lean_ctor_get(x_208, 0);
x_771 = lean_ctor_get(x_208, 1);
lean_inc(x_771);
lean_inc(x_770);
lean_dec(x_208);
x_772 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_772, 0, x_770);
lean_ctor_set(x_772, 1, x_771);
return x_772;
}
}
}
else
{
lean_object* x_773; 
lean_free_object(x_8);
lean_dec_ref(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_773 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_198, x_10);
return x_773;
}
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; uint8_t x_786; lean_object* x_787; uint8_t x_788; lean_object* x_789; uint8_t x_790; 
x_774 = lean_ctor_get(x_8, 0);
x_775 = lean_ctor_get(x_8, 1);
x_776 = lean_ctor_get(x_8, 2);
x_777 = lean_ctor_get(x_8, 3);
x_778 = lean_ctor_get(x_8, 4);
x_779 = lean_ctor_get(x_8, 5);
x_780 = lean_ctor_get(x_8, 6);
x_781 = lean_ctor_get(x_8, 7);
x_782 = lean_ctor_get(x_8, 8);
x_783 = lean_ctor_get(x_8, 9);
x_784 = lean_ctor_get(x_8, 10);
x_785 = lean_ctor_get(x_8, 11);
x_786 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_787 = lean_ctor_get(x_8, 12);
x_788 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_789 = lean_ctor_get(x_8, 13);
lean_inc(x_789);
lean_inc(x_787);
lean_inc(x_785);
lean_inc(x_784);
lean_inc(x_783);
lean_inc(x_782);
lean_inc(x_781);
lean_inc(x_780);
lean_inc(x_779);
lean_inc(x_778);
lean_inc(x_777);
lean_inc(x_776);
lean_inc(x_775);
lean_inc(x_774);
lean_dec(x_8);
x_790 = lean_nat_dec_eq(x_777, x_778);
if (x_790 == 0)
{
lean_object* x_791; 
x_791 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
if (lean_obj_tag(x_791) == 0)
{
lean_object* x_792; uint8_t x_793; 
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
x_793 = lean_unbox(x_792);
lean_dec(x_792);
if (x_793 == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; uint8_t x_1039; 
x_794 = lean_ctor_get(x_791, 1);
lean_inc(x_794);
lean_dec_ref(x_791);
x_795 = lean_unsigned_to_nat(1u);
x_796 = lean_nat_add(x_777, x_795);
lean_dec(x_777);
x_797 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_797, 0, x_774);
lean_ctor_set(x_797, 1, x_775);
lean_ctor_set(x_797, 2, x_776);
lean_ctor_set(x_797, 3, x_796);
lean_ctor_set(x_797, 4, x_778);
lean_ctor_set(x_797, 5, x_779);
lean_ctor_set(x_797, 6, x_780);
lean_ctor_set(x_797, 7, x_781);
lean_ctor_set(x_797, 8, x_782);
lean_ctor_set(x_797, 9, x_783);
lean_ctor_set(x_797, 10, x_784);
lean_ctor_set(x_797, 11, x_785);
lean_ctor_set(x_797, 12, x_787);
lean_ctor_set(x_797, 13, x_789);
lean_ctor_set_uint8(x_797, sizeof(void*)*14, x_786);
lean_ctor_set_uint8(x_797, sizeof(void*)*14 + 1, x_788);
x_929 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_930 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_929, x_797, x_794);
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_930, 1);
lean_inc(x_932);
if (lean_is_exclusive(x_930)) {
 lean_ctor_release(x_930, 0);
 lean_ctor_release(x_930, 1);
 x_933 = x_930;
} else {
 lean_dec_ref(x_930);
 x_933 = lean_box(0);
}
x_934 = lean_box(0);
x_1039 = lean_unbox(x_931);
lean_dec(x_931);
if (x_1039 == 0)
{
x_963 = x_2;
x_964 = x_3;
x_965 = x_4;
x_966 = x_5;
x_967 = x_6;
x_968 = x_7;
x_969 = x_797;
x_970 = x_9;
x_971 = x_932;
goto block_1038;
}
else
{
lean_object* x_1040; 
lean_inc_ref(x_1);
x_1040 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_932);
if (lean_obj_tag(x_1040) == 0)
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
x_1041 = lean_ctor_get(x_1040, 0);
lean_inc(x_1041);
x_1042 = lean_ctor_get(x_1040, 1);
lean_inc(x_1042);
lean_dec_ref(x_1040);
x_1043 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_1044 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1044, 0, x_1043);
lean_ctor_set(x_1044, 1, x_1041);
x_1045 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1045, 0, x_1044);
lean_ctor_set(x_1045, 1, x_1043);
x_1046 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_929, x_1045, x_6, x_7, x_797, x_9, x_1042);
x_1047 = lean_ctor_get(x_1046, 1);
lean_inc(x_1047);
lean_dec_ref(x_1046);
x_963 = x_2;
x_964 = x_3;
x_965 = x_4;
x_966 = x_5;
x_967 = x_6;
x_968 = x_7;
x_969 = x_797;
x_970 = x_9;
x_971 = x_1047;
goto block_1038;
}
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
lean_dec(x_933);
lean_dec_ref(x_797);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1048 = lean_ctor_get(x_1040, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1040, 1);
lean_inc(x_1049);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 lean_ctor_release(x_1040, 1);
 x_1050 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1050 = lean_box(0);
}
if (lean_is_scalar(x_1050)) {
 x_1051 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1051 = x_1050;
}
lean_ctor_set(x_1051, 0, x_1048);
lean_ctor_set(x_1051, 1, x_1049);
return x_1051;
}
}
block_928:
{
if (lean_obj_tag(x_813) == 0)
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; uint8_t x_817; 
lean_dec(x_812);
lean_dec(x_807);
lean_dec(x_804);
lean_dec_ref(x_803);
lean_dec_ref(x_802);
lean_dec(x_801);
x_814 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_815 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_814, x_809, x_810);
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
x_817 = lean_unbox(x_816);
lean_dec(x_816);
if (x_817 == 0)
{
lean_object* x_818; 
x_818 = lean_ctor_get(x_815, 1);
lean_inc(x_818);
lean_dec_ref(x_815);
x_11 = x_805;
x_12 = x_808;
x_13 = x_800;
x_14 = x_806;
x_15 = x_799;
x_16 = x_811;
x_17 = x_809;
x_18 = x_798;
x_19 = x_818;
goto block_168;
}
else
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_819 = lean_ctor_get(x_815, 1);
lean_inc(x_819);
if (lean_is_exclusive(x_815)) {
 lean_ctor_release(x_815, 0);
 lean_ctor_release(x_815, 1);
 x_820 = x_815;
} else {
 lean_dec_ref(x_815);
 x_820 = lean_box(0);
}
lean_inc_ref(x_805);
x_821 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_805, x_806, x_819);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_822 = lean_ctor_get(x_821, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_821, 1);
lean_inc(x_823);
lean_dec_ref(x_821);
x_824 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_820)) {
 x_825 = lean_alloc_ctor(7, 2, 0);
} else {
 x_825 = x_820;
 lean_ctor_set_tag(x_825, 7);
}
lean_ctor_set(x_825, 0, x_824);
lean_ctor_set(x_825, 1, x_822);
x_826 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_826, 0, x_825);
lean_ctor_set(x_826, 1, x_824);
x_827 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_814, x_826, x_799, x_811, x_809, x_798, x_823);
x_828 = lean_ctor_get(x_827, 1);
lean_inc(x_828);
lean_dec_ref(x_827);
x_11 = x_805;
x_12 = x_808;
x_13 = x_800;
x_14 = x_806;
x_15 = x_799;
x_16 = x_811;
x_17 = x_809;
x_18 = x_798;
x_19 = x_828;
goto block_168;
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
lean_dec(x_820);
lean_dec(x_811);
lean_dec_ref(x_809);
lean_dec(x_808);
lean_dec(x_806);
lean_dec_ref(x_805);
lean_dec_ref(x_800);
lean_dec_ref(x_799);
lean_dec(x_798);
x_829 = lean_ctor_get(x_821, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_821, 1);
lean_inc(x_830);
if (lean_is_exclusive(x_821)) {
 lean_ctor_release(x_821, 0);
 lean_ctor_release(x_821, 1);
 x_831 = x_821;
} else {
 lean_dec_ref(x_821);
 x_831 = lean_box(0);
}
if (lean_is_scalar(x_831)) {
 x_832 = lean_alloc_ctor(1, 2, 0);
} else {
 x_832 = x_831;
}
lean_ctor_set(x_832, 0, x_829);
lean_ctor_set(x_832, 1, x_830);
return x_832;
}
}
}
else
{
lean_object* x_833; lean_object* x_834; 
lean_dec_ref(x_800);
x_833 = lean_ctor_get(x_813, 0);
lean_inc(x_833);
lean_dec_ref(x_813);
x_834 = lean_ctor_get(x_833, 1);
lean_inc_ref(x_834);
if (lean_obj_tag(x_834) == 0)
{
lean_object* x_835; 
lean_dec_ref(x_834);
lean_dec(x_812);
lean_dec(x_808);
lean_dec_ref(x_805);
lean_dec_ref(x_802);
lean_dec(x_801);
x_835 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_833, x_806, x_807, x_803, x_804, x_799, x_811, x_809, x_798, x_810);
lean_dec(x_798);
lean_dec_ref(x_809);
lean_dec(x_811);
lean_dec_ref(x_799);
lean_dec(x_804);
lean_dec_ref(x_803);
lean_dec(x_807);
lean_dec(x_806);
return x_835;
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; uint8_t x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; uint8_t x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; uint8_t x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
x_836 = lean_ctor_get(x_833, 0);
x_837 = lean_ctor_get(x_834, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_834, 2);
lean_inc_ref(x_838);
if (lean_is_exclusive(x_834)) {
 lean_ctor_release(x_834, 0);
 lean_ctor_release(x_834, 1);
 lean_ctor_release(x_834, 2);
 x_839 = x_834;
} else {
 lean_dec_ref(x_834);
 x_839 = lean_box(0);
}
x_840 = lean_int_mul(x_812, x_836);
x_841 = lean_int_mul(x_837, x_801);
x_842 = l_Lean_Meta_Grind_Arith_gcdExt(x_840, x_841);
lean_dec(x_841);
lean_dec(x_840);
x_843 = lean_ctor_get(x_842, 1);
lean_inc(x_843);
x_844 = lean_ctor_get(x_842, 0);
lean_inc(x_844);
lean_dec_ref(x_842);
x_845 = lean_ctor_get(x_843, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_843, 1);
lean_inc(x_846);
lean_dec(x_843);
x_847 = lean_st_ref_take(x_806, x_810);
x_848 = lean_ctor_get(x_847, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_848, 14);
lean_inc_ref(x_849);
x_850 = lean_ctor_get(x_849, 1);
lean_inc_ref(x_850);
x_851 = lean_ctor_get(x_847, 1);
lean_inc(x_851);
lean_dec_ref(x_847);
x_852 = lean_ctor_get(x_848, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_848, 1);
lean_inc_ref(x_853);
x_854 = lean_ctor_get(x_848, 2);
lean_inc(x_854);
x_855 = lean_ctor_get(x_848, 3);
lean_inc_ref(x_855);
x_856 = lean_ctor_get(x_848, 4);
lean_inc_ref(x_856);
x_857 = lean_ctor_get(x_848, 5);
lean_inc_ref(x_857);
x_858 = lean_ctor_get(x_848, 6);
lean_inc_ref(x_858);
x_859 = lean_ctor_get(x_848, 7);
lean_inc_ref(x_859);
x_860 = lean_ctor_get_uint8(x_848, sizeof(void*)*18);
x_861 = lean_ctor_get(x_848, 8);
lean_inc(x_861);
x_862 = lean_ctor_get(x_848, 9);
lean_inc_ref(x_862);
x_863 = lean_ctor_get(x_848, 10);
lean_inc_ref(x_863);
x_864 = lean_ctor_get(x_848, 11);
lean_inc_ref(x_864);
x_865 = lean_ctor_get(x_848, 12);
lean_inc_ref(x_865);
x_866 = lean_ctor_get(x_848, 13);
lean_inc_ref(x_866);
x_867 = lean_ctor_get(x_848, 15);
lean_inc_ref(x_867);
x_868 = lean_ctor_get(x_848, 16);
lean_inc_ref(x_868);
x_869 = lean_ctor_get(x_848, 17);
lean_inc_ref(x_869);
if (lean_is_exclusive(x_848)) {
 lean_ctor_release(x_848, 0);
 lean_ctor_release(x_848, 1);
 lean_ctor_release(x_848, 2);
 lean_ctor_release(x_848, 3);
 lean_ctor_release(x_848, 4);
 lean_ctor_release(x_848, 5);
 lean_ctor_release(x_848, 6);
 lean_ctor_release(x_848, 7);
 lean_ctor_release(x_848, 8);
 lean_ctor_release(x_848, 9);
 lean_ctor_release(x_848, 10);
 lean_ctor_release(x_848, 11);
 lean_ctor_release(x_848, 12);
 lean_ctor_release(x_848, 13);
 lean_ctor_release(x_848, 14);
 lean_ctor_release(x_848, 15);
 lean_ctor_release(x_848, 16);
 lean_ctor_release(x_848, 17);
 x_870 = x_848;
} else {
 lean_dec_ref(x_848);
 x_870 = lean_box(0);
}
x_871 = lean_ctor_get(x_849, 0);
lean_inc_ref(x_871);
x_872 = lean_ctor_get(x_849, 2);
lean_inc_ref(x_872);
x_873 = lean_ctor_get(x_849, 3);
lean_inc_ref(x_873);
if (lean_is_exclusive(x_849)) {
 lean_ctor_release(x_849, 0);
 lean_ctor_release(x_849, 1);
 lean_ctor_release(x_849, 2);
 lean_ctor_release(x_849, 3);
 x_874 = x_849;
} else {
 lean_dec_ref(x_849);
 x_874 = lean_box(0);
}
x_875 = lean_ctor_get(x_850, 0);
lean_inc_ref(x_875);
x_876 = lean_ctor_get(x_850, 1);
lean_inc_ref(x_876);
x_877 = lean_ctor_get(x_850, 2);
lean_inc_ref(x_877);
x_878 = lean_ctor_get(x_850, 3);
lean_inc_ref(x_878);
x_879 = lean_ctor_get(x_850, 4);
lean_inc_ref(x_879);
x_880 = lean_ctor_get(x_850, 5);
lean_inc_ref(x_880);
x_881 = lean_ctor_get(x_850, 6);
lean_inc_ref(x_881);
x_882 = lean_ctor_get(x_850, 7);
lean_inc_ref(x_882);
x_883 = lean_ctor_get(x_850, 8);
lean_inc_ref(x_883);
x_884 = lean_ctor_get(x_850, 9);
lean_inc_ref(x_884);
x_885 = lean_ctor_get(x_850, 10);
lean_inc_ref(x_885);
x_886 = lean_ctor_get(x_850, 11);
lean_inc(x_886);
x_887 = lean_ctor_get(x_850, 12);
lean_inc_ref(x_887);
x_888 = lean_ctor_get(x_850, 13);
lean_inc_ref(x_888);
x_889 = lean_ctor_get(x_850, 14);
lean_inc(x_889);
x_890 = lean_ctor_get_uint8(x_850, sizeof(void*)*22);
x_891 = lean_ctor_get(x_850, 15);
lean_inc(x_891);
x_892 = lean_ctor_get(x_850, 16);
lean_inc_ref(x_892);
x_893 = lean_ctor_get(x_850, 17);
lean_inc_ref(x_893);
x_894 = lean_ctor_get(x_850, 18);
lean_inc_ref(x_894);
x_895 = lean_ctor_get(x_850, 19);
lean_inc_ref(x_895);
x_896 = lean_ctor_get(x_850, 20);
lean_inc_ref(x_896);
x_897 = lean_ctor_get_uint8(x_850, sizeof(void*)*22 + 1);
x_898 = lean_ctor_get(x_850, 21);
lean_inc_ref(x_898);
if (lean_is_exclusive(x_850)) {
 lean_ctor_release(x_850, 0);
 lean_ctor_release(x_850, 1);
 lean_ctor_release(x_850, 2);
 lean_ctor_release(x_850, 3);
 lean_ctor_release(x_850, 4);
 lean_ctor_release(x_850, 5);
 lean_ctor_release(x_850, 6);
 lean_ctor_release(x_850, 7);
 lean_ctor_release(x_850, 8);
 lean_ctor_release(x_850, 9);
 lean_ctor_release(x_850, 10);
 lean_ctor_release(x_850, 11);
 lean_ctor_release(x_850, 12);
 lean_ctor_release(x_850, 13);
 lean_ctor_release(x_850, 14);
 lean_ctor_release(x_850, 15);
 lean_ctor_release(x_850, 16);
 lean_ctor_release(x_850, 17);
 lean_ctor_release(x_850, 18);
 lean_ctor_release(x_850, 19);
 lean_ctor_release(x_850, 20);
 lean_ctor_release(x_850, 21);
 x_899 = x_850;
} else {
 lean_dec_ref(x_850);
 x_899 = lean_box(0);
}
x_900 = lean_box(0);
x_901 = l_Lean_PersistentArray_set___redArg(x_881, x_808, x_900);
if (lean_is_scalar(x_899)) {
 x_902 = lean_alloc_ctor(0, 22, 2);
} else {
 x_902 = x_899;
}
lean_ctor_set(x_902, 0, x_875);
lean_ctor_set(x_902, 1, x_876);
lean_ctor_set(x_902, 2, x_877);
lean_ctor_set(x_902, 3, x_878);
lean_ctor_set(x_902, 4, x_879);
lean_ctor_set(x_902, 5, x_880);
lean_ctor_set(x_902, 6, x_901);
lean_ctor_set(x_902, 7, x_882);
lean_ctor_set(x_902, 8, x_883);
lean_ctor_set(x_902, 9, x_884);
lean_ctor_set(x_902, 10, x_885);
lean_ctor_set(x_902, 11, x_886);
lean_ctor_set(x_902, 12, x_887);
lean_ctor_set(x_902, 13, x_888);
lean_ctor_set(x_902, 14, x_889);
lean_ctor_set(x_902, 15, x_891);
lean_ctor_set(x_902, 16, x_892);
lean_ctor_set(x_902, 17, x_893);
lean_ctor_set(x_902, 18, x_894);
lean_ctor_set(x_902, 19, x_895);
lean_ctor_set(x_902, 20, x_896);
lean_ctor_set(x_902, 21, x_898);
lean_ctor_set_uint8(x_902, sizeof(void*)*22, x_890);
lean_ctor_set_uint8(x_902, sizeof(void*)*22 + 1, x_897);
if (lean_is_scalar(x_874)) {
 x_903 = lean_alloc_ctor(0, 4, 0);
} else {
 x_903 = x_874;
}
lean_ctor_set(x_903, 0, x_871);
lean_ctor_set(x_903, 1, x_902);
lean_ctor_set(x_903, 2, x_872);
lean_ctor_set(x_903, 3, x_873);
if (lean_is_scalar(x_870)) {
 x_904 = lean_alloc_ctor(0, 18, 1);
} else {
 x_904 = x_870;
}
lean_ctor_set(x_904, 0, x_852);
lean_ctor_set(x_904, 1, x_853);
lean_ctor_set(x_904, 2, x_854);
lean_ctor_set(x_904, 3, x_855);
lean_ctor_set(x_904, 4, x_856);
lean_ctor_set(x_904, 5, x_857);
lean_ctor_set(x_904, 6, x_858);
lean_ctor_set(x_904, 7, x_859);
lean_ctor_set(x_904, 8, x_861);
lean_ctor_set(x_904, 9, x_862);
lean_ctor_set(x_904, 10, x_863);
lean_ctor_set(x_904, 11, x_864);
lean_ctor_set(x_904, 12, x_865);
lean_ctor_set(x_904, 13, x_866);
lean_ctor_set(x_904, 14, x_903);
lean_ctor_set(x_904, 15, x_867);
lean_ctor_set(x_904, 16, x_868);
lean_ctor_set(x_904, 17, x_869);
lean_ctor_set_uint8(x_904, sizeof(void*)*18, x_860);
x_905 = lean_st_ref_set(x_806, x_904, x_851);
x_906 = lean_ctor_get(x_905, 1);
lean_inc(x_906);
if (lean_is_exclusive(x_905)) {
 lean_ctor_release(x_905, 0);
 lean_ctor_release(x_905, 1);
 x_907 = x_905;
} else {
 lean_dec_ref(x_905);
 x_907 = lean_box(0);
}
x_908 = lean_int_mul(x_845, x_836);
lean_dec(x_845);
lean_inc_ref(x_802);
x_909 = l_Int_Linear_Poly_mul(x_802, x_908);
lean_dec(x_908);
x_910 = lean_int_mul(x_846, x_801);
lean_dec(x_846);
lean_inc_ref(x_838);
x_911 = l_Int_Linear_Poly_mul(x_838, x_910);
lean_dec(x_910);
x_912 = lean_int_mul(x_801, x_836);
lean_dec(x_801);
x_913 = l_Int_Linear_Poly_combine(x_909, x_911);
lean_inc(x_844);
if (lean_is_scalar(x_839)) {
 x_914 = lean_alloc_ctor(1, 3, 0);
} else {
 x_914 = x_839;
}
lean_ctor_set(x_914, 0, x_844);
lean_ctor_set(x_914, 1, x_808);
lean_ctor_set(x_914, 2, x_913);
lean_inc(x_833);
lean_inc_ref(x_805);
if (lean_is_scalar(x_907)) {
 x_915 = lean_alloc_ctor(4, 2, 0);
} else {
 x_915 = x_907;
 lean_ctor_set_tag(x_915, 4);
}
lean_ctor_set(x_915, 0, x_805);
lean_ctor_set(x_915, 1, x_833);
x_916 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_916, 0, x_912);
lean_ctor_set(x_916, 1, x_914);
lean_ctor_set(x_916, 2, x_915);
lean_inc(x_798);
lean_inc_ref(x_809);
lean_inc(x_811);
lean_inc_ref(x_799);
lean_inc(x_804);
lean_inc_ref(x_803);
lean_inc(x_807);
lean_inc(x_806);
x_917 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_916, x_806, x_807, x_803, x_804, x_799, x_811, x_809, x_798, x_906);
if (lean_obj_tag(x_917) == 0)
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_918 = lean_ctor_get(x_917, 1);
lean_inc(x_918);
if (lean_is_exclusive(x_917)) {
 lean_ctor_release(x_917, 0);
 lean_ctor_release(x_917, 1);
 x_919 = x_917;
} else {
 lean_dec_ref(x_917);
 x_919 = lean_box(0);
}
x_920 = l_Int_Linear_Poly_mul(x_802, x_837);
lean_dec(x_837);
x_921 = lean_int_neg(x_812);
lean_dec(x_812);
x_922 = l_Int_Linear_Poly_mul(x_838, x_921);
lean_dec(x_921);
x_923 = l_Int_Linear_Poly_combine(x_920, x_922);
lean_inc(x_833);
if (lean_is_scalar(x_919)) {
 x_924 = lean_alloc_ctor(5, 2, 0);
} else {
 x_924 = x_919;
 lean_ctor_set_tag(x_924, 5);
}
lean_ctor_set(x_924, 0, x_805);
lean_ctor_set(x_924, 1, x_833);
if (lean_is_exclusive(x_833)) {
 lean_ctor_release(x_833, 0);
 lean_ctor_release(x_833, 1);
 lean_ctor_release(x_833, 2);
 x_925 = x_833;
} else {
 lean_dec_ref(x_833);
 x_925 = lean_box(0);
}
if (lean_is_scalar(x_925)) {
 x_926 = lean_alloc_ctor(0, 3, 0);
} else {
 x_926 = x_925;
}
lean_ctor_set(x_926, 0, x_844);
lean_ctor_set(x_926, 1, x_923);
lean_ctor_set(x_926, 2, x_924);
x_1 = x_926;
x_2 = x_806;
x_3 = x_807;
x_4 = x_803;
x_5 = x_804;
x_6 = x_799;
x_7 = x_811;
x_8 = x_809;
x_9 = x_798;
x_10 = x_918;
goto _start;
}
else
{
lean_dec(x_844);
lean_dec_ref(x_838);
lean_dec(x_837);
lean_dec(x_833);
lean_dec(x_812);
lean_dec(x_811);
lean_dec_ref(x_809);
lean_dec(x_807);
lean_dec(x_806);
lean_dec_ref(x_805);
lean_dec(x_804);
lean_dec_ref(x_803);
lean_dec_ref(x_802);
lean_dec_ref(x_799);
lean_dec(x_798);
return x_917;
}
}
}
}
block_962:
{
lean_object* x_950; 
x_950 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_941, x_949);
if (lean_obj_tag(x_950) == 0)
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; uint8_t x_955; 
x_951 = lean_ctor_get(x_950, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_951, 6);
lean_inc_ref(x_952);
lean_dec(x_951);
x_953 = lean_ctor_get(x_950, 1);
lean_inc(x_953);
lean_dec_ref(x_950);
x_954 = lean_ctor_get(x_952, 2);
x_955 = lean_nat_dec_lt(x_937, x_954);
if (x_955 == 0)
{
lean_object* x_956; 
lean_dec_ref(x_952);
x_956 = l_outOfBounds___redArg(x_934);
x_798 = x_948;
x_799 = x_945;
x_800 = x_938;
x_801 = x_940;
x_802 = x_935;
x_803 = x_943;
x_804 = x_944;
x_805 = x_936;
x_806 = x_941;
x_807 = x_942;
x_808 = x_937;
x_809 = x_947;
x_810 = x_953;
x_811 = x_946;
x_812 = x_939;
x_813 = x_956;
goto block_928;
}
else
{
lean_object* x_957; 
x_957 = l_Lean_PersistentArray_get_x21___redArg(x_934, x_952, x_937);
x_798 = x_948;
x_799 = x_945;
x_800 = x_938;
x_801 = x_940;
x_802 = x_935;
x_803 = x_943;
x_804 = x_944;
x_805 = x_936;
x_806 = x_941;
x_807 = x_942;
x_808 = x_937;
x_809 = x_947;
x_810 = x_953;
x_811 = x_946;
x_812 = x_939;
x_813 = x_957;
goto block_928;
}
}
else
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; 
lean_dec(x_948);
lean_dec_ref(x_947);
lean_dec(x_946);
lean_dec_ref(x_945);
lean_dec(x_944);
lean_dec_ref(x_943);
lean_dec(x_942);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_939);
lean_dec_ref(x_938);
lean_dec(x_937);
lean_dec_ref(x_936);
lean_dec_ref(x_935);
x_958 = lean_ctor_get(x_950, 0);
lean_inc(x_958);
x_959 = lean_ctor_get(x_950, 1);
lean_inc(x_959);
if (lean_is_exclusive(x_950)) {
 lean_ctor_release(x_950, 0);
 lean_ctor_release(x_950, 1);
 x_960 = x_950;
} else {
 lean_dec_ref(x_950);
 x_960 = lean_box(0);
}
if (lean_is_scalar(x_960)) {
 x_961 = lean_alloc_ctor(1, 2, 0);
} else {
 x_961 = x_960;
}
lean_ctor_set(x_961, 0, x_958);
lean_ctor_set(x_961, 1, x_959);
return x_961;
}
}
block_1038:
{
lean_object* x_972; lean_object* x_973; 
x_972 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_969);
x_973 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_972, x_963, x_964, x_965, x_966, x_967, x_968, x_969, x_970, x_971);
if (lean_obj_tag(x_973) == 0)
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; uint8_t x_978; 
x_974 = lean_ctor_get(x_973, 0);
lean_inc(x_974);
x_975 = lean_ctor_get(x_973, 1);
lean_inc(x_975);
lean_dec_ref(x_973);
x_976 = lean_ctor_get(x_974, 0);
x_977 = lean_ctor_get(x_974, 1);
lean_inc(x_976);
x_978 = l_Int_Linear_Poly_isUnsatDvd(x_976, x_977);
if (x_978 == 0)
{
uint8_t x_979; 
x_979 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_974);
if (x_979 == 0)
{
lean_dec(x_933);
if (lean_obj_tag(x_977) == 0)
{
lean_object* x_980; 
x_980 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_974, x_963, x_964, x_965, x_966, x_967, x_968, x_969, x_970, x_975);
lean_dec(x_970);
lean_dec_ref(x_969);
lean_dec(x_968);
lean_dec_ref(x_967);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec(x_963);
return x_980;
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
lean_inc_ref(x_977);
lean_inc(x_976);
x_981 = lean_ctor_get(x_977, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_977, 1);
lean_inc(x_982);
x_983 = lean_ctor_get(x_977, 2);
lean_inc_ref(x_983);
lean_inc(x_974);
x_984 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_974, x_963, x_975);
if (lean_obj_tag(x_984) == 0)
{
lean_object* x_985; lean_object* x_986; uint8_t x_987; uint8_t x_988; uint8_t x_989; 
x_985 = lean_ctor_get(x_984, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_984, 1);
lean_inc(x_986);
lean_dec_ref(x_984);
x_987 = 0;
x_988 = lean_unbox(x_985);
lean_dec(x_985);
x_989 = l_Lean_instBEqLBool_beq(x_988, x_987);
if (x_989 == 0)
{
x_935 = x_983;
x_936 = x_974;
x_937 = x_982;
x_938 = x_977;
x_939 = x_981;
x_940 = x_976;
x_941 = x_963;
x_942 = x_964;
x_943 = x_965;
x_944 = x_966;
x_945 = x_967;
x_946 = x_968;
x_947 = x_969;
x_948 = x_970;
x_949 = x_986;
goto block_962;
}
else
{
lean_object* x_990; 
x_990 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_982, x_963, x_986);
if (lean_obj_tag(x_990) == 0)
{
lean_object* x_991; 
x_991 = lean_ctor_get(x_990, 1);
lean_inc(x_991);
lean_dec_ref(x_990);
x_935 = x_983;
x_936 = x_974;
x_937 = x_982;
x_938 = x_977;
x_939 = x_981;
x_940 = x_976;
x_941 = x_963;
x_942 = x_964;
x_943 = x_965;
x_944 = x_966;
x_945 = x_967;
x_946 = x_968;
x_947 = x_969;
x_948 = x_970;
x_949 = x_991;
goto block_962;
}
else
{
lean_dec_ref(x_983);
lean_dec(x_982);
lean_dec(x_981);
lean_dec_ref(x_977);
lean_dec(x_976);
lean_dec(x_974);
lean_dec(x_970);
lean_dec_ref(x_969);
lean_dec(x_968);
lean_dec_ref(x_967);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec(x_963);
return x_990;
}
}
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; 
lean_dec_ref(x_983);
lean_dec(x_982);
lean_dec(x_981);
lean_dec_ref(x_977);
lean_dec(x_976);
lean_dec(x_974);
lean_dec(x_970);
lean_dec_ref(x_969);
lean_dec(x_968);
lean_dec_ref(x_967);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec(x_963);
x_992 = lean_ctor_get(x_984, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_984, 1);
lean_inc(x_993);
if (lean_is_exclusive(x_984)) {
 lean_ctor_release(x_984, 0);
 lean_ctor_release(x_984, 1);
 x_994 = x_984;
} else {
 lean_dec_ref(x_984);
 x_994 = lean_box(0);
}
if (lean_is_scalar(x_994)) {
 x_995 = lean_alloc_ctor(1, 2, 0);
} else {
 x_995 = x_994;
}
lean_ctor_set(x_995, 0, x_992);
lean_ctor_set(x_995, 1, x_993);
return x_995;
}
}
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; uint8_t x_999; 
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
x_996 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_997 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_996, x_969, x_975);
x_998 = lean_ctor_get(x_997, 0);
lean_inc(x_998);
x_999 = lean_unbox(x_998);
lean_dec(x_998);
if (x_999 == 0)
{
lean_object* x_1000; 
lean_dec(x_974);
lean_dec(x_970);
lean_dec_ref(x_969);
lean_dec(x_968);
lean_dec_ref(x_967);
lean_dec(x_963);
lean_dec(x_933);
x_1000 = lean_ctor_get(x_997, 1);
lean_inc(x_1000);
lean_dec_ref(x_997);
x_188 = x_1000;
goto block_191;
}
else
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; 
x_1001 = lean_ctor_get(x_997, 1);
lean_inc(x_1001);
if (lean_is_exclusive(x_997)) {
 lean_ctor_release(x_997, 0);
 lean_ctor_release(x_997, 1);
 x_1002 = x_997;
} else {
 lean_dec_ref(x_997);
 x_1002 = lean_box(0);
}
x_1003 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_974, x_963, x_1001);
lean_dec(x_963);
if (lean_obj_tag(x_1003) == 0)
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
x_1004 = lean_ctor_get(x_1003, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_1003, 1);
lean_inc(x_1005);
lean_dec_ref(x_1003);
x_1006 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_1002)) {
 x_1007 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1007 = x_1002;
 lean_ctor_set_tag(x_1007, 7);
}
lean_ctor_set(x_1007, 0, x_1006);
lean_ctor_set(x_1007, 1, x_1004);
if (lean_is_scalar(x_933)) {
 x_1008 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1008 = x_933;
 lean_ctor_set_tag(x_1008, 7);
}
lean_ctor_set(x_1008, 0, x_1007);
lean_ctor_set(x_1008, 1, x_1006);
x_1009 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_996, x_1008, x_967, x_968, x_969, x_970, x_1005);
lean_dec(x_970);
lean_dec_ref(x_969);
lean_dec(x_968);
lean_dec_ref(x_967);
x_1010 = lean_ctor_get(x_1009, 1);
lean_inc(x_1010);
lean_dec_ref(x_1009);
x_188 = x_1010;
goto block_191;
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; 
lean_dec(x_1002);
lean_dec(x_970);
lean_dec_ref(x_969);
lean_dec(x_968);
lean_dec_ref(x_967);
lean_dec(x_933);
x_1011 = lean_ctor_get(x_1003, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_1003, 1);
lean_inc(x_1012);
if (lean_is_exclusive(x_1003)) {
 lean_ctor_release(x_1003, 0);
 lean_ctor_release(x_1003, 1);
 x_1013 = x_1003;
} else {
 lean_dec_ref(x_1003);
 x_1013 = lean_box(0);
}
if (lean_is_scalar(x_1013)) {
 x_1014 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1014 = x_1013;
}
lean_ctor_set(x_1014, 0, x_1011);
lean_ctor_set(x_1014, 1, x_1012);
return x_1014;
}
}
}
}
else
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; uint8_t x_1018; 
x_1015 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_1016 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_1015, x_969, x_975);
x_1017 = lean_ctor_get(x_1016, 0);
lean_inc(x_1017);
x_1018 = lean_unbox(x_1017);
lean_dec(x_1017);
if (x_1018 == 0)
{
lean_object* x_1019; 
lean_dec(x_933);
x_1019 = lean_ctor_get(x_1016, 1);
lean_inc(x_1019);
lean_dec_ref(x_1016);
x_169 = x_974;
x_170 = x_963;
x_171 = x_964;
x_172 = x_965;
x_173 = x_966;
x_174 = x_967;
x_175 = x_968;
x_176 = x_969;
x_177 = x_970;
x_178 = x_1019;
goto block_187;
}
else
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; 
x_1020 = lean_ctor_get(x_1016, 1);
lean_inc(x_1020);
if (lean_is_exclusive(x_1016)) {
 lean_ctor_release(x_1016, 0);
 lean_ctor_release(x_1016, 1);
 x_1021 = x_1016;
} else {
 lean_dec_ref(x_1016);
 x_1021 = lean_box(0);
}
lean_inc(x_974);
x_1022 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_974, x_963, x_1020);
if (lean_obj_tag(x_1022) == 0)
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
x_1023 = lean_ctor_get(x_1022, 0);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_1022, 1);
lean_inc(x_1024);
lean_dec_ref(x_1022);
x_1025 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_1021)) {
 x_1026 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1026 = x_1021;
 lean_ctor_set_tag(x_1026, 7);
}
lean_ctor_set(x_1026, 0, x_1025);
lean_ctor_set(x_1026, 1, x_1023);
if (lean_is_scalar(x_933)) {
 x_1027 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1027 = x_933;
 lean_ctor_set_tag(x_1027, 7);
}
lean_ctor_set(x_1027, 0, x_1026);
lean_ctor_set(x_1027, 1, x_1025);
x_1028 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_1015, x_1027, x_967, x_968, x_969, x_970, x_1024);
x_1029 = lean_ctor_get(x_1028, 1);
lean_inc(x_1029);
lean_dec_ref(x_1028);
x_169 = x_974;
x_170 = x_963;
x_171 = x_964;
x_172 = x_965;
x_173 = x_966;
x_174 = x_967;
x_175 = x_968;
x_176 = x_969;
x_177 = x_970;
x_178 = x_1029;
goto block_187;
}
else
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
lean_dec(x_1021);
lean_dec(x_974);
lean_dec(x_970);
lean_dec_ref(x_969);
lean_dec(x_968);
lean_dec_ref(x_967);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec(x_963);
lean_dec(x_933);
x_1030 = lean_ctor_get(x_1022, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1022, 1);
lean_inc(x_1031);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1032 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1032 = lean_box(0);
}
if (lean_is_scalar(x_1032)) {
 x_1033 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1033 = x_1032;
}
lean_ctor_set(x_1033, 0, x_1030);
lean_ctor_set(x_1033, 1, x_1031);
return x_1033;
}
}
}
}
else
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
lean_dec(x_970);
lean_dec_ref(x_969);
lean_dec(x_968);
lean_dec_ref(x_967);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec(x_963);
lean_dec(x_933);
x_1034 = lean_ctor_get(x_973, 0);
lean_inc(x_1034);
x_1035 = lean_ctor_get(x_973, 1);
lean_inc(x_1035);
if (lean_is_exclusive(x_973)) {
 lean_ctor_release(x_973, 0);
 lean_ctor_release(x_973, 1);
 x_1036 = x_973;
} else {
 lean_dec_ref(x_973);
 x_1036 = lean_box(0);
}
if (lean_is_scalar(x_1036)) {
 x_1037 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1037 = x_1036;
}
lean_ctor_set(x_1037, 0, x_1034);
lean_ctor_set(x_1037, 1, x_1035);
return x_1037;
}
}
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
lean_dec_ref(x_789);
lean_dec(x_787);
lean_dec(x_785);
lean_dec(x_784);
lean_dec(x_783);
lean_dec(x_782);
lean_dec(x_781);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_776);
lean_dec_ref(x_775);
lean_dec_ref(x_774);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1052 = lean_ctor_get(x_791, 1);
lean_inc(x_1052);
if (lean_is_exclusive(x_791)) {
 lean_ctor_release(x_791, 0);
 lean_ctor_release(x_791, 1);
 x_1053 = x_791;
} else {
 lean_dec_ref(x_791);
 x_1053 = lean_box(0);
}
x_1054 = lean_box(0);
if (lean_is_scalar(x_1053)) {
 x_1055 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1055 = x_1053;
}
lean_ctor_set(x_1055, 0, x_1054);
lean_ctor_set(x_1055, 1, x_1052);
return x_1055;
}
}
else
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
lean_dec_ref(x_789);
lean_dec(x_787);
lean_dec(x_785);
lean_dec(x_784);
lean_dec(x_783);
lean_dec(x_782);
lean_dec(x_781);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_776);
lean_dec_ref(x_775);
lean_dec_ref(x_774);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1056 = lean_ctor_get(x_791, 0);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_791, 1);
lean_inc(x_1057);
if (lean_is_exclusive(x_791)) {
 lean_ctor_release(x_791, 0);
 lean_ctor_release(x_791, 1);
 x_1058 = x_791;
} else {
 lean_dec_ref(x_791);
 x_1058 = lean_box(0);
}
if (lean_is_scalar(x_1058)) {
 x_1059 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1059 = x_1058;
}
lean_ctor_set(x_1059, 0, x_1056);
lean_ctor_set(x_1059, 1, x_1057);
return x_1059;
}
}
else
{
lean_object* x_1060; 
lean_dec_ref(x_789);
lean_dec(x_787);
lean_dec(x_785);
lean_dec(x_784);
lean_dec(x_783);
lean_dec(x_782);
lean_dec(x_781);
lean_dec(x_780);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_776);
lean_dec_ref(x_775);
lean_dec_ref(x_774);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1060 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_779, x_10);
return x_1060;
}
}
block_168:
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
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_74 = lean_ctor_get(x_24, 0);
x_75 = lean_ctor_get(x_24, 2);
x_76 = lean_ctor_get(x_24, 3);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_24);
x_77 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_25, 4);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_25, 5);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_25, 6);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_25, 7);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_25, 8);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_25, 9);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_25, 10);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_25, 11);
lean_inc(x_88);
x_89 = lean_ctor_get(x_25, 12);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_25, 13);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_25, 14);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_25, sizeof(void*)*22);
x_93 = lean_ctor_get(x_25, 15);
lean_inc(x_93);
x_94 = lean_ctor_get(x_25, 16);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_25, 17);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_25, 18);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_25, 19);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_25, 20);
lean_inc_ref(x_98);
x_99 = lean_ctor_get_uint8(x_25, sizeof(void*)*22 + 1);
x_100 = lean_ctor_get(x_25, 21);
lean_inc_ref(x_100);
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
 x_101 = x_25;
} else {
 lean_dec_ref(x_25);
 x_101 = lean_box(0);
}
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_11);
x_103 = l_Lean_PersistentArray_set___redArg(x_83, x_12, x_102);
lean_dec(x_12);
if (lean_is_scalar(x_101)) {
 x_104 = lean_alloc_ctor(0, 22, 2);
} else {
 x_104 = x_101;
}
lean_ctor_set(x_104, 0, x_77);
lean_ctor_set(x_104, 1, x_78);
lean_ctor_set(x_104, 2, x_79);
lean_ctor_set(x_104, 3, x_80);
lean_ctor_set(x_104, 4, x_81);
lean_ctor_set(x_104, 5, x_82);
lean_ctor_set(x_104, 6, x_103);
lean_ctor_set(x_104, 7, x_84);
lean_ctor_set(x_104, 8, x_85);
lean_ctor_set(x_104, 9, x_86);
lean_ctor_set(x_104, 10, x_87);
lean_ctor_set(x_104, 11, x_88);
lean_ctor_set(x_104, 12, x_89);
lean_ctor_set(x_104, 13, x_90);
lean_ctor_set(x_104, 14, x_91);
lean_ctor_set(x_104, 15, x_93);
lean_ctor_set(x_104, 16, x_94);
lean_ctor_set(x_104, 17, x_95);
lean_ctor_set(x_104, 18, x_96);
lean_ctor_set(x_104, 19, x_97);
lean_ctor_set(x_104, 20, x_98);
lean_ctor_set(x_104, 21, x_100);
lean_ctor_set_uint8(x_104, sizeof(void*)*22, x_92);
lean_ctor_set_uint8(x_104, sizeof(void*)*22 + 1, x_99);
x_105 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_105, 0, x_74);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_75);
lean_ctor_set(x_105, 3, x_76);
lean_ctor_set(x_23, 14, x_105);
x_106 = lean_st_ref_set(x_14, x_23, x_26);
lean_dec(x_14);
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
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_111 = lean_ctor_get(x_23, 0);
x_112 = lean_ctor_get(x_23, 1);
x_113 = lean_ctor_get(x_23, 2);
x_114 = lean_ctor_get(x_23, 3);
x_115 = lean_ctor_get(x_23, 4);
x_116 = lean_ctor_get(x_23, 5);
x_117 = lean_ctor_get(x_23, 6);
x_118 = lean_ctor_get(x_23, 7);
x_119 = lean_ctor_get_uint8(x_23, sizeof(void*)*18);
x_120 = lean_ctor_get(x_23, 8);
x_121 = lean_ctor_get(x_23, 9);
x_122 = lean_ctor_get(x_23, 10);
x_123 = lean_ctor_get(x_23, 11);
x_124 = lean_ctor_get(x_23, 12);
x_125 = lean_ctor_get(x_23, 13);
x_126 = lean_ctor_get(x_23, 15);
x_127 = lean_ctor_get(x_23, 16);
x_128 = lean_ctor_get(x_23, 17);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_23);
x_129 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_24, 3);
lean_inc_ref(x_131);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 x_132 = x_24;
} else {
 lean_dec_ref(x_24);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_25, 4);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_25, 5);
lean_inc_ref(x_138);
x_139 = lean_ctor_get(x_25, 6);
lean_inc_ref(x_139);
x_140 = lean_ctor_get(x_25, 7);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_25, 8);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_25, 9);
lean_inc_ref(x_142);
x_143 = lean_ctor_get(x_25, 10);
lean_inc_ref(x_143);
x_144 = lean_ctor_get(x_25, 11);
lean_inc(x_144);
x_145 = lean_ctor_get(x_25, 12);
lean_inc_ref(x_145);
x_146 = lean_ctor_get(x_25, 13);
lean_inc_ref(x_146);
x_147 = lean_ctor_get(x_25, 14);
lean_inc(x_147);
x_148 = lean_ctor_get_uint8(x_25, sizeof(void*)*22);
x_149 = lean_ctor_get(x_25, 15);
lean_inc(x_149);
x_150 = lean_ctor_get(x_25, 16);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_25, 17);
lean_inc_ref(x_151);
x_152 = lean_ctor_get(x_25, 18);
lean_inc_ref(x_152);
x_153 = lean_ctor_get(x_25, 19);
lean_inc_ref(x_153);
x_154 = lean_ctor_get(x_25, 20);
lean_inc_ref(x_154);
x_155 = lean_ctor_get_uint8(x_25, sizeof(void*)*22 + 1);
x_156 = lean_ctor_get(x_25, 21);
lean_inc_ref(x_156);
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
 x_157 = x_25;
} else {
 lean_dec_ref(x_25);
 x_157 = lean_box(0);
}
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_11);
x_159 = l_Lean_PersistentArray_set___redArg(x_139, x_12, x_158);
lean_dec(x_12);
if (lean_is_scalar(x_157)) {
 x_160 = lean_alloc_ctor(0, 22, 2);
} else {
 x_160 = x_157;
}
lean_ctor_set(x_160, 0, x_133);
lean_ctor_set(x_160, 1, x_134);
lean_ctor_set(x_160, 2, x_135);
lean_ctor_set(x_160, 3, x_136);
lean_ctor_set(x_160, 4, x_137);
lean_ctor_set(x_160, 5, x_138);
lean_ctor_set(x_160, 6, x_159);
lean_ctor_set(x_160, 7, x_140);
lean_ctor_set(x_160, 8, x_141);
lean_ctor_set(x_160, 9, x_142);
lean_ctor_set(x_160, 10, x_143);
lean_ctor_set(x_160, 11, x_144);
lean_ctor_set(x_160, 12, x_145);
lean_ctor_set(x_160, 13, x_146);
lean_ctor_set(x_160, 14, x_147);
lean_ctor_set(x_160, 15, x_149);
lean_ctor_set(x_160, 16, x_150);
lean_ctor_set(x_160, 17, x_151);
lean_ctor_set(x_160, 18, x_152);
lean_ctor_set(x_160, 19, x_153);
lean_ctor_set(x_160, 20, x_154);
lean_ctor_set(x_160, 21, x_156);
lean_ctor_set_uint8(x_160, sizeof(void*)*22, x_148);
lean_ctor_set_uint8(x_160, sizeof(void*)*22 + 1, x_155);
if (lean_is_scalar(x_132)) {
 x_161 = lean_alloc_ctor(0, 4, 0);
} else {
 x_161 = x_132;
}
lean_ctor_set(x_161, 0, x_129);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set(x_161, 2, x_130);
lean_ctor_set(x_161, 3, x_131);
x_162 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_162, 0, x_111);
lean_ctor_set(x_162, 1, x_112);
lean_ctor_set(x_162, 2, x_113);
lean_ctor_set(x_162, 3, x_114);
lean_ctor_set(x_162, 4, x_115);
lean_ctor_set(x_162, 5, x_116);
lean_ctor_set(x_162, 6, x_117);
lean_ctor_set(x_162, 7, x_118);
lean_ctor_set(x_162, 8, x_120);
lean_ctor_set(x_162, 9, x_121);
lean_ctor_set(x_162, 10, x_122);
lean_ctor_set(x_162, 11, x_123);
lean_ctor_set(x_162, 12, x_124);
lean_ctor_set(x_162, 13, x_125);
lean_ctor_set(x_162, 14, x_161);
lean_ctor_set(x_162, 15, x_126);
lean_ctor_set(x_162, 16, x_127);
lean_ctor_set(x_162, 17, x_128);
lean_ctor_set_uint8(x_162, sizeof(void*)*18, x_119);
x_163 = lean_st_ref_set(x_14, x_162, x_26);
lean_dec(x_14);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
x_166 = lean_box(0);
if (lean_is_scalar(x_165)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_165;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_164);
return x_167;
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
block_187:
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_169);
x_180 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_179, x_170, x_171, x_172, x_173, x_174, x_175, x_176, x_177, x_178);
if (lean_obj_tag(x_180) == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_180, 0);
lean_dec(x_182);
x_183 = lean_box(0);
lean_ctor_set(x_180, 0, x_183);
return x_180;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_180, 1);
lean_inc(x_184);
lean_dec(x_180);
x_185 = lean_box(0);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
else
{
return x_180;
}
}
block_191:
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
return x_190;
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

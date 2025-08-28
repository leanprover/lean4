// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Simp.Arith.Int Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing Lean.Meta.NatInstTesters
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
uint8_t l_Lean_beqLBool____x40_Lean_Data_LBool_27903016____hygCtx___hyg_13_(uint8_t, uint8_t);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_187; uint8_t x_191; 
x_191 = !lean_is_exclusive(x_8);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_192 = lean_ctor_get(x_8, 0);
x_193 = lean_ctor_get(x_8, 1);
x_194 = lean_ctor_get(x_8, 2);
x_195 = lean_ctor_get(x_8, 3);
x_196 = lean_ctor_get(x_8, 4);
x_197 = lean_ctor_get(x_8, 5);
x_198 = lean_ctor_get(x_8, 6);
x_199 = lean_ctor_get(x_8, 7);
x_200 = lean_ctor_get(x_8, 8);
x_201 = lean_ctor_get(x_8, 9);
x_202 = lean_ctor_get(x_8, 10);
x_203 = lean_ctor_get(x_8, 11);
x_204 = lean_ctor_get(x_8, 12);
x_205 = lean_ctor_get(x_8, 13);
x_206 = lean_nat_dec_eq(x_195, x_196);
if (x_206 == 0)
{
lean_object* x_207; 
x_207 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; uint8_t x_747; 
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
lean_dec_ref(x_207);
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_nat_add(x_195, x_211);
lean_dec(x_195);
lean_ctor_set(x_8, 3, x_212);
x_611 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_612 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_611, x_8, x_210);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_615 = x_612;
} else {
 lean_dec_ref(x_612);
 x_615 = lean_box(0);
}
x_616 = lean_box(0);
x_747 = lean_unbox(x_613);
lean_dec(x_613);
if (x_747 == 0)
{
x_645 = x_2;
x_646 = x_3;
x_647 = x_4;
x_648 = x_5;
x_649 = x_6;
x_650 = x_7;
x_651 = x_8;
x_652 = x_9;
x_653 = x_614;
goto block_746;
}
else
{
lean_object* x_748; 
lean_inc_ref(x_1);
x_748 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_614);
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_748, 1);
lean_inc(x_750);
lean_dec_ref(x_748);
x_751 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_752 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_752, 0, x_751);
lean_ctor_set(x_752, 1, x_749);
x_753 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_753, 0, x_752);
lean_ctor_set(x_753, 1, x_751);
x_754 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_611, x_753, x_6, x_7, x_8, x_9, x_750);
x_755 = lean_ctor_get(x_754, 1);
lean_inc(x_755);
lean_dec_ref(x_754);
x_645 = x_2;
x_646 = x_3;
x_647 = x_4;
x_648 = x_5;
x_649 = x_6;
x_650 = x_7;
x_651 = x_8;
x_652 = x_9;
x_653 = x_755;
goto block_746;
}
else
{
uint8_t x_756; 
lean_dec(x_615);
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_756 = !lean_is_exclusive(x_748);
if (x_756 == 0)
{
return x_748;
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_757 = lean_ctor_get(x_748, 0);
x_758 = lean_ctor_get(x_748, 1);
lean_inc(x_758);
lean_inc(x_757);
lean_dec(x_748);
x_759 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_759, 0, x_757);
lean_ctor_set(x_759, 1, x_758);
return x_759;
}
}
}
block_610:
{
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_216);
lean_dec_ref(x_215);
x_229 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_230 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_229, x_220, x_227);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_unbox(x_231);
lean_dec(x_231);
if (x_232 == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec_ref(x_230);
x_11 = x_213;
x_12 = x_223;
x_13 = x_214;
x_14 = x_217;
x_15 = x_225;
x_16 = x_224;
x_17 = x_220;
x_18 = x_226;
x_19 = x_233;
goto block_167;
}
else
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_230);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_230, 1);
x_236 = lean_ctor_get(x_230, 0);
lean_dec(x_236);
lean_inc_ref(x_223);
x_237 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_223, x_217, x_235);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec_ref(x_237);
x_240 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_230, 7);
lean_ctor_set(x_230, 1, x_238);
lean_ctor_set(x_230, 0, x_240);
x_241 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_241, 0, x_230);
lean_ctor_set(x_241, 1, x_240);
x_242 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_229, x_241, x_225, x_224, x_220, x_226, x_239);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec_ref(x_242);
x_11 = x_213;
x_12 = x_223;
x_13 = x_214;
x_14 = x_217;
x_15 = x_225;
x_16 = x_224;
x_17 = x_220;
x_18 = x_226;
x_19 = x_243;
goto block_167;
}
else
{
uint8_t x_244; 
lean_free_object(x_230);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec_ref(x_220);
lean_dec(x_217);
lean_dec_ref(x_214);
lean_dec(x_213);
x_244 = !lean_is_exclusive(x_237);
if (x_244 == 0)
{
return x_237;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_237, 0);
x_246 = lean_ctor_get(x_237, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_237);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
}
else
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_230, 1);
lean_inc(x_248);
lean_dec(x_230);
lean_inc_ref(x_223);
x_249 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_223, x_217, x_248);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec_ref(x_249);
x_252 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_253 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_250);
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_252);
x_255 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_229, x_254, x_225, x_224, x_220, x_226, x_251);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
lean_dec_ref(x_255);
x_11 = x_213;
x_12 = x_223;
x_13 = x_214;
x_14 = x_217;
x_15 = x_225;
x_16 = x_224;
x_17 = x_220;
x_18 = x_226;
x_19 = x_256;
goto block_167;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec_ref(x_220);
lean_dec(x_217);
lean_dec_ref(x_214);
lean_dec(x_213);
x_257 = lean_ctor_get(x_249, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_249, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_259 = x_249;
} else {
 lean_dec_ref(x_249);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
}
}
else
{
lean_object* x_261; lean_object* x_262; 
lean_dec_ref(x_214);
x_261 = lean_ctor_get(x_228, 0);
lean_inc(x_261);
lean_dec_ref(x_228);
x_262 = lean_ctor_get(x_261, 1);
lean_inc_ref(x_262);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; 
lean_dec_ref(x_262);
lean_dec_ref(x_223);
lean_dec(x_219);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec(x_213);
x_263 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_261, x_217, x_222, x_221, x_218, x_225, x_224, x_220, x_226, x_227);
lean_dec(x_226);
lean_dec_ref(x_220);
lean_dec(x_224);
lean_dec_ref(x_225);
lean_dec(x_218);
lean_dec_ref(x_221);
lean_dec(x_222);
lean_dec(x_217);
return x_263;
}
else
{
uint8_t x_264; 
x_264 = !lean_is_exclusive(x_262);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_265 = lean_ctor_get(x_261, 0);
x_266 = lean_ctor_get(x_262, 0);
x_267 = lean_ctor_get(x_262, 2);
x_268 = lean_ctor_get(x_262, 1);
lean_dec(x_268);
x_269 = lean_int_mul(x_216, x_265);
x_270 = lean_int_mul(x_266, x_219);
x_271 = l_Lean_Meta_Grind_Arith_gcdExt(x_269, x_270);
lean_dec(x_270);
lean_dec(x_269);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 0);
lean_inc(x_273);
lean_dec_ref(x_271);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_272, 1);
lean_inc(x_275);
lean_dec(x_272);
x_276 = lean_st_ref_take(x_217, x_227);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_277, 14);
lean_inc_ref(x_278);
x_279 = lean_ctor_get(x_278, 1);
lean_inc_ref(x_279);
x_280 = lean_ctor_get(x_276, 1);
lean_inc(x_280);
lean_dec_ref(x_276);
x_281 = !lean_is_exclusive(x_277);
if (x_281 == 0)
{
lean_object* x_282; uint8_t x_283; 
x_282 = lean_ctor_get(x_277, 14);
lean_dec(x_282);
x_283 = !lean_is_exclusive(x_278);
if (x_283 == 0)
{
lean_object* x_284; uint8_t x_285; 
x_284 = lean_ctor_get(x_278, 1);
lean_dec(x_284);
x_285 = !lean_is_exclusive(x_279);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_286 = lean_ctor_get(x_279, 6);
x_287 = lean_box(0);
x_288 = l_Lean_PersistentArray_set___redArg(x_286, x_213, x_287);
lean_ctor_set(x_279, 6, x_288);
x_289 = lean_st_ref_set(x_217, x_277, x_280);
x_290 = !lean_is_exclusive(x_289);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_291 = lean_ctor_get(x_289, 1);
x_292 = lean_ctor_get(x_289, 0);
lean_dec(x_292);
x_293 = lean_int_mul(x_274, x_265);
lean_dec(x_274);
lean_inc_ref(x_215);
x_294 = l_Int_Linear_Poly_mul(x_215, x_293);
lean_dec(x_293);
x_295 = lean_int_mul(x_275, x_219);
lean_dec(x_275);
lean_inc_ref(x_267);
x_296 = l_Int_Linear_Poly_mul(x_267, x_295);
lean_dec(x_295);
x_297 = lean_int_mul(x_219, x_265);
lean_dec(x_219);
x_298 = l_Int_Linear_Poly_combine(x_294, x_296);
lean_inc(x_273);
lean_ctor_set(x_262, 2, x_298);
lean_ctor_set(x_262, 1, x_213);
lean_ctor_set(x_262, 0, x_273);
lean_inc(x_261);
lean_inc_ref(x_223);
lean_ctor_set_tag(x_289, 4);
lean_ctor_set(x_289, 1, x_261);
lean_ctor_set(x_289, 0, x_223);
x_299 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_262);
lean_ctor_set(x_299, 2, x_289);
lean_inc(x_226);
lean_inc_ref(x_220);
lean_inc(x_224);
lean_inc_ref(x_225);
lean_inc(x_218);
lean_inc_ref(x_221);
lean_inc(x_222);
lean_inc(x_217);
x_300 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_299, x_217, x_222, x_221, x_218, x_225, x_224, x_220, x_226, x_291);
if (lean_obj_tag(x_300) == 0)
{
uint8_t x_301; 
x_301 = !lean_is_exclusive(x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_302 = lean_ctor_get(x_300, 1);
x_303 = lean_ctor_get(x_300, 0);
lean_dec(x_303);
x_304 = l_Int_Linear_Poly_mul(x_215, x_266);
lean_dec(x_266);
x_305 = lean_int_neg(x_216);
lean_dec(x_216);
x_306 = l_Int_Linear_Poly_mul(x_267, x_305);
lean_dec(x_305);
x_307 = l_Int_Linear_Poly_combine(x_304, x_306);
lean_inc(x_261);
lean_ctor_set_tag(x_300, 5);
lean_ctor_set(x_300, 1, x_261);
lean_ctor_set(x_300, 0, x_223);
x_308 = !lean_is_exclusive(x_261);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_261, 2);
lean_dec(x_309);
x_310 = lean_ctor_get(x_261, 1);
lean_dec(x_310);
x_311 = lean_ctor_get(x_261, 0);
lean_dec(x_311);
lean_ctor_set(x_261, 2, x_300);
lean_ctor_set(x_261, 1, x_307);
lean_ctor_set(x_261, 0, x_273);
x_1 = x_261;
x_2 = x_217;
x_3 = x_222;
x_4 = x_221;
x_5 = x_218;
x_6 = x_225;
x_7 = x_224;
x_8 = x_220;
x_9 = x_226;
x_10 = x_302;
goto _start;
}
else
{
lean_object* x_313; 
lean_dec(x_261);
x_313 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_313, 0, x_273);
lean_ctor_set(x_313, 1, x_307);
lean_ctor_set(x_313, 2, x_300);
x_1 = x_313;
x_2 = x_217;
x_3 = x_222;
x_4 = x_221;
x_5 = x_218;
x_6 = x_225;
x_7 = x_224;
x_8 = x_220;
x_9 = x_226;
x_10 = x_302;
goto _start;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_315 = lean_ctor_get(x_300, 1);
lean_inc(x_315);
lean_dec(x_300);
x_316 = l_Int_Linear_Poly_mul(x_215, x_266);
lean_dec(x_266);
x_317 = lean_int_neg(x_216);
lean_dec(x_216);
x_318 = l_Int_Linear_Poly_mul(x_267, x_317);
lean_dec(x_317);
x_319 = l_Int_Linear_Poly_combine(x_316, x_318);
lean_inc(x_261);
x_320 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_320, 0, x_223);
lean_ctor_set(x_320, 1, x_261);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 x_321 = x_261;
} else {
 lean_dec_ref(x_261);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(0, 3, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_273);
lean_ctor_set(x_322, 1, x_319);
lean_ctor_set(x_322, 2, x_320);
x_1 = x_322;
x_2 = x_217;
x_3 = x_222;
x_4 = x_221;
x_5 = x_218;
x_6 = x_225;
x_7 = x_224;
x_8 = x_220;
x_9 = x_226;
x_10 = x_315;
goto _start;
}
}
else
{
lean_dec(x_273);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec(x_261);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec_ref(x_220);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec_ref(x_215);
return x_300;
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_324 = lean_ctor_get(x_289, 1);
lean_inc(x_324);
lean_dec(x_289);
x_325 = lean_int_mul(x_274, x_265);
lean_dec(x_274);
lean_inc_ref(x_215);
x_326 = l_Int_Linear_Poly_mul(x_215, x_325);
lean_dec(x_325);
x_327 = lean_int_mul(x_275, x_219);
lean_dec(x_275);
lean_inc_ref(x_267);
x_328 = l_Int_Linear_Poly_mul(x_267, x_327);
lean_dec(x_327);
x_329 = lean_int_mul(x_219, x_265);
lean_dec(x_219);
x_330 = l_Int_Linear_Poly_combine(x_326, x_328);
lean_inc(x_273);
lean_ctor_set(x_262, 2, x_330);
lean_ctor_set(x_262, 1, x_213);
lean_ctor_set(x_262, 0, x_273);
lean_inc(x_261);
lean_inc_ref(x_223);
x_331 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_331, 0, x_223);
lean_ctor_set(x_331, 1, x_261);
x_332 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_262);
lean_ctor_set(x_332, 2, x_331);
lean_inc(x_226);
lean_inc_ref(x_220);
lean_inc(x_224);
lean_inc_ref(x_225);
lean_inc(x_218);
lean_inc_ref(x_221);
lean_inc(x_222);
lean_inc(x_217);
x_333 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_332, x_217, x_222, x_221, x_218, x_225, x_224, x_220, x_226, x_324);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_335 = x_333;
} else {
 lean_dec_ref(x_333);
 x_335 = lean_box(0);
}
x_336 = l_Int_Linear_Poly_mul(x_215, x_266);
lean_dec(x_266);
x_337 = lean_int_neg(x_216);
lean_dec(x_216);
x_338 = l_Int_Linear_Poly_mul(x_267, x_337);
lean_dec(x_337);
x_339 = l_Int_Linear_Poly_combine(x_336, x_338);
lean_inc(x_261);
if (lean_is_scalar(x_335)) {
 x_340 = lean_alloc_ctor(5, 2, 0);
} else {
 x_340 = x_335;
 lean_ctor_set_tag(x_340, 5);
}
lean_ctor_set(x_340, 0, x_223);
lean_ctor_set(x_340, 1, x_261);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 x_341 = x_261;
} else {
 lean_dec_ref(x_261);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(0, 3, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_273);
lean_ctor_set(x_342, 1, x_339);
lean_ctor_set(x_342, 2, x_340);
x_1 = x_342;
x_2 = x_217;
x_3 = x_222;
x_4 = x_221;
x_5 = x_218;
x_6 = x_225;
x_7 = x_224;
x_8 = x_220;
x_9 = x_226;
x_10 = x_334;
goto _start;
}
else
{
lean_dec(x_273);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec(x_261);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec_ref(x_220);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec_ref(x_215);
return x_333;
}
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_344 = lean_ctor_get(x_279, 0);
x_345 = lean_ctor_get(x_279, 1);
x_346 = lean_ctor_get(x_279, 2);
x_347 = lean_ctor_get(x_279, 3);
x_348 = lean_ctor_get(x_279, 4);
x_349 = lean_ctor_get(x_279, 5);
x_350 = lean_ctor_get(x_279, 6);
x_351 = lean_ctor_get(x_279, 7);
x_352 = lean_ctor_get(x_279, 8);
x_353 = lean_ctor_get(x_279, 9);
x_354 = lean_ctor_get(x_279, 10);
x_355 = lean_ctor_get(x_279, 11);
x_356 = lean_ctor_get(x_279, 12);
x_357 = lean_ctor_get(x_279, 13);
x_358 = lean_ctor_get(x_279, 14);
x_359 = lean_ctor_get_uint8(x_279, sizeof(void*)*22);
x_360 = lean_ctor_get(x_279, 15);
x_361 = lean_ctor_get(x_279, 16);
x_362 = lean_ctor_get(x_279, 17);
x_363 = lean_ctor_get(x_279, 18);
x_364 = lean_ctor_get(x_279, 19);
x_365 = lean_ctor_get(x_279, 20);
x_366 = lean_ctor_get_uint8(x_279, sizeof(void*)*22 + 1);
x_367 = lean_ctor_get(x_279, 21);
lean_inc(x_367);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
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
lean_inc(x_344);
lean_dec(x_279);
x_368 = lean_box(0);
x_369 = l_Lean_PersistentArray_set___redArg(x_350, x_213, x_368);
x_370 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_370, 0, x_344);
lean_ctor_set(x_370, 1, x_345);
lean_ctor_set(x_370, 2, x_346);
lean_ctor_set(x_370, 3, x_347);
lean_ctor_set(x_370, 4, x_348);
lean_ctor_set(x_370, 5, x_349);
lean_ctor_set(x_370, 6, x_369);
lean_ctor_set(x_370, 7, x_351);
lean_ctor_set(x_370, 8, x_352);
lean_ctor_set(x_370, 9, x_353);
lean_ctor_set(x_370, 10, x_354);
lean_ctor_set(x_370, 11, x_355);
lean_ctor_set(x_370, 12, x_356);
lean_ctor_set(x_370, 13, x_357);
lean_ctor_set(x_370, 14, x_358);
lean_ctor_set(x_370, 15, x_360);
lean_ctor_set(x_370, 16, x_361);
lean_ctor_set(x_370, 17, x_362);
lean_ctor_set(x_370, 18, x_363);
lean_ctor_set(x_370, 19, x_364);
lean_ctor_set(x_370, 20, x_365);
lean_ctor_set(x_370, 21, x_367);
lean_ctor_set_uint8(x_370, sizeof(void*)*22, x_359);
lean_ctor_set_uint8(x_370, sizeof(void*)*22 + 1, x_366);
lean_ctor_set(x_278, 1, x_370);
x_371 = lean_st_ref_set(x_217, x_277, x_280);
x_372 = lean_ctor_get(x_371, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_373 = x_371;
} else {
 lean_dec_ref(x_371);
 x_373 = lean_box(0);
}
x_374 = lean_int_mul(x_274, x_265);
lean_dec(x_274);
lean_inc_ref(x_215);
x_375 = l_Int_Linear_Poly_mul(x_215, x_374);
lean_dec(x_374);
x_376 = lean_int_mul(x_275, x_219);
lean_dec(x_275);
lean_inc_ref(x_267);
x_377 = l_Int_Linear_Poly_mul(x_267, x_376);
lean_dec(x_376);
x_378 = lean_int_mul(x_219, x_265);
lean_dec(x_219);
x_379 = l_Int_Linear_Poly_combine(x_375, x_377);
lean_inc(x_273);
lean_ctor_set(x_262, 2, x_379);
lean_ctor_set(x_262, 1, x_213);
lean_ctor_set(x_262, 0, x_273);
lean_inc(x_261);
lean_inc_ref(x_223);
if (lean_is_scalar(x_373)) {
 x_380 = lean_alloc_ctor(4, 2, 0);
} else {
 x_380 = x_373;
 lean_ctor_set_tag(x_380, 4);
}
lean_ctor_set(x_380, 0, x_223);
lean_ctor_set(x_380, 1, x_261);
x_381 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_381, 0, x_378);
lean_ctor_set(x_381, 1, x_262);
lean_ctor_set(x_381, 2, x_380);
lean_inc(x_226);
lean_inc_ref(x_220);
lean_inc(x_224);
lean_inc_ref(x_225);
lean_inc(x_218);
lean_inc_ref(x_221);
lean_inc(x_222);
lean_inc(x_217);
x_382 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_381, x_217, x_222, x_221, x_218, x_225, x_224, x_220, x_226, x_372);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_384 = x_382;
} else {
 lean_dec_ref(x_382);
 x_384 = lean_box(0);
}
x_385 = l_Int_Linear_Poly_mul(x_215, x_266);
lean_dec(x_266);
x_386 = lean_int_neg(x_216);
lean_dec(x_216);
x_387 = l_Int_Linear_Poly_mul(x_267, x_386);
lean_dec(x_386);
x_388 = l_Int_Linear_Poly_combine(x_385, x_387);
lean_inc(x_261);
if (lean_is_scalar(x_384)) {
 x_389 = lean_alloc_ctor(5, 2, 0);
} else {
 x_389 = x_384;
 lean_ctor_set_tag(x_389, 5);
}
lean_ctor_set(x_389, 0, x_223);
lean_ctor_set(x_389, 1, x_261);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 x_390 = x_261;
} else {
 lean_dec_ref(x_261);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(0, 3, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_273);
lean_ctor_set(x_391, 1, x_388);
lean_ctor_set(x_391, 2, x_389);
x_1 = x_391;
x_2 = x_217;
x_3 = x_222;
x_4 = x_221;
x_5 = x_218;
x_6 = x_225;
x_7 = x_224;
x_8 = x_220;
x_9 = x_226;
x_10 = x_383;
goto _start;
}
else
{
lean_dec(x_273);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec(x_261);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec_ref(x_220);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec_ref(x_215);
return x_382;
}
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_393 = lean_ctor_get(x_278, 0);
x_394 = lean_ctor_get(x_278, 2);
x_395 = lean_ctor_get(x_278, 3);
lean_inc(x_395);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_278);
x_396 = lean_ctor_get(x_279, 0);
lean_inc_ref(x_396);
x_397 = lean_ctor_get(x_279, 1);
lean_inc_ref(x_397);
x_398 = lean_ctor_get(x_279, 2);
lean_inc_ref(x_398);
x_399 = lean_ctor_get(x_279, 3);
lean_inc_ref(x_399);
x_400 = lean_ctor_get(x_279, 4);
lean_inc_ref(x_400);
x_401 = lean_ctor_get(x_279, 5);
lean_inc_ref(x_401);
x_402 = lean_ctor_get(x_279, 6);
lean_inc_ref(x_402);
x_403 = lean_ctor_get(x_279, 7);
lean_inc_ref(x_403);
x_404 = lean_ctor_get(x_279, 8);
lean_inc_ref(x_404);
x_405 = lean_ctor_get(x_279, 9);
lean_inc_ref(x_405);
x_406 = lean_ctor_get(x_279, 10);
lean_inc_ref(x_406);
x_407 = lean_ctor_get(x_279, 11);
lean_inc(x_407);
x_408 = lean_ctor_get(x_279, 12);
lean_inc_ref(x_408);
x_409 = lean_ctor_get(x_279, 13);
lean_inc_ref(x_409);
x_410 = lean_ctor_get(x_279, 14);
lean_inc(x_410);
x_411 = lean_ctor_get_uint8(x_279, sizeof(void*)*22);
x_412 = lean_ctor_get(x_279, 15);
lean_inc(x_412);
x_413 = lean_ctor_get(x_279, 16);
lean_inc_ref(x_413);
x_414 = lean_ctor_get(x_279, 17);
lean_inc_ref(x_414);
x_415 = lean_ctor_get(x_279, 18);
lean_inc_ref(x_415);
x_416 = lean_ctor_get(x_279, 19);
lean_inc_ref(x_416);
x_417 = lean_ctor_get(x_279, 20);
lean_inc_ref(x_417);
x_418 = lean_ctor_get_uint8(x_279, sizeof(void*)*22 + 1);
x_419 = lean_ctor_get(x_279, 21);
lean_inc_ref(x_419);
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
 lean_ctor_release(x_279, 17);
 lean_ctor_release(x_279, 18);
 lean_ctor_release(x_279, 19);
 lean_ctor_release(x_279, 20);
 lean_ctor_release(x_279, 21);
 x_420 = x_279;
} else {
 lean_dec_ref(x_279);
 x_420 = lean_box(0);
}
x_421 = lean_box(0);
x_422 = l_Lean_PersistentArray_set___redArg(x_402, x_213, x_421);
if (lean_is_scalar(x_420)) {
 x_423 = lean_alloc_ctor(0, 22, 2);
} else {
 x_423 = x_420;
}
lean_ctor_set(x_423, 0, x_396);
lean_ctor_set(x_423, 1, x_397);
lean_ctor_set(x_423, 2, x_398);
lean_ctor_set(x_423, 3, x_399);
lean_ctor_set(x_423, 4, x_400);
lean_ctor_set(x_423, 5, x_401);
lean_ctor_set(x_423, 6, x_422);
lean_ctor_set(x_423, 7, x_403);
lean_ctor_set(x_423, 8, x_404);
lean_ctor_set(x_423, 9, x_405);
lean_ctor_set(x_423, 10, x_406);
lean_ctor_set(x_423, 11, x_407);
lean_ctor_set(x_423, 12, x_408);
lean_ctor_set(x_423, 13, x_409);
lean_ctor_set(x_423, 14, x_410);
lean_ctor_set(x_423, 15, x_412);
lean_ctor_set(x_423, 16, x_413);
lean_ctor_set(x_423, 17, x_414);
lean_ctor_set(x_423, 18, x_415);
lean_ctor_set(x_423, 19, x_416);
lean_ctor_set(x_423, 20, x_417);
lean_ctor_set(x_423, 21, x_419);
lean_ctor_set_uint8(x_423, sizeof(void*)*22, x_411);
lean_ctor_set_uint8(x_423, sizeof(void*)*22 + 1, x_418);
x_424 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_424, 0, x_393);
lean_ctor_set(x_424, 1, x_423);
lean_ctor_set(x_424, 2, x_394);
lean_ctor_set(x_424, 3, x_395);
lean_ctor_set(x_277, 14, x_424);
x_425 = lean_st_ref_set(x_217, x_277, x_280);
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 x_427 = x_425;
} else {
 lean_dec_ref(x_425);
 x_427 = lean_box(0);
}
x_428 = lean_int_mul(x_274, x_265);
lean_dec(x_274);
lean_inc_ref(x_215);
x_429 = l_Int_Linear_Poly_mul(x_215, x_428);
lean_dec(x_428);
x_430 = lean_int_mul(x_275, x_219);
lean_dec(x_275);
lean_inc_ref(x_267);
x_431 = l_Int_Linear_Poly_mul(x_267, x_430);
lean_dec(x_430);
x_432 = lean_int_mul(x_219, x_265);
lean_dec(x_219);
x_433 = l_Int_Linear_Poly_combine(x_429, x_431);
lean_inc(x_273);
lean_ctor_set(x_262, 2, x_433);
lean_ctor_set(x_262, 1, x_213);
lean_ctor_set(x_262, 0, x_273);
lean_inc(x_261);
lean_inc_ref(x_223);
if (lean_is_scalar(x_427)) {
 x_434 = lean_alloc_ctor(4, 2, 0);
} else {
 x_434 = x_427;
 lean_ctor_set_tag(x_434, 4);
}
lean_ctor_set(x_434, 0, x_223);
lean_ctor_set(x_434, 1, x_261);
x_435 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_435, 0, x_432);
lean_ctor_set(x_435, 1, x_262);
lean_ctor_set(x_435, 2, x_434);
lean_inc(x_226);
lean_inc_ref(x_220);
lean_inc(x_224);
lean_inc_ref(x_225);
lean_inc(x_218);
lean_inc_ref(x_221);
lean_inc(x_222);
lean_inc(x_217);
x_436 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_435, x_217, x_222, x_221, x_218, x_225, x_224, x_220, x_226, x_426);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_437 = lean_ctor_get(x_436, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_438 = x_436;
} else {
 lean_dec_ref(x_436);
 x_438 = lean_box(0);
}
x_439 = l_Int_Linear_Poly_mul(x_215, x_266);
lean_dec(x_266);
x_440 = lean_int_neg(x_216);
lean_dec(x_216);
x_441 = l_Int_Linear_Poly_mul(x_267, x_440);
lean_dec(x_440);
x_442 = l_Int_Linear_Poly_combine(x_439, x_441);
lean_inc(x_261);
if (lean_is_scalar(x_438)) {
 x_443 = lean_alloc_ctor(5, 2, 0);
} else {
 x_443 = x_438;
 lean_ctor_set_tag(x_443, 5);
}
lean_ctor_set(x_443, 0, x_223);
lean_ctor_set(x_443, 1, x_261);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 x_444 = x_261;
} else {
 lean_dec_ref(x_261);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(0, 3, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_273);
lean_ctor_set(x_445, 1, x_442);
lean_ctor_set(x_445, 2, x_443);
x_1 = x_445;
x_2 = x_217;
x_3 = x_222;
x_4 = x_221;
x_5 = x_218;
x_6 = x_225;
x_7 = x_224;
x_8 = x_220;
x_9 = x_226;
x_10 = x_437;
goto _start;
}
else
{
lean_dec(x_273);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec(x_261);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec_ref(x_220);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec_ref(x_215);
return x_436;
}
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_447 = lean_ctor_get(x_277, 0);
x_448 = lean_ctor_get(x_277, 1);
x_449 = lean_ctor_get(x_277, 2);
x_450 = lean_ctor_get(x_277, 3);
x_451 = lean_ctor_get(x_277, 4);
x_452 = lean_ctor_get(x_277, 5);
x_453 = lean_ctor_get(x_277, 6);
x_454 = lean_ctor_get(x_277, 7);
x_455 = lean_ctor_get_uint8(x_277, sizeof(void*)*17);
x_456 = lean_ctor_get(x_277, 8);
x_457 = lean_ctor_get(x_277, 9);
x_458 = lean_ctor_get(x_277, 10);
x_459 = lean_ctor_get(x_277, 11);
x_460 = lean_ctor_get(x_277, 12);
x_461 = lean_ctor_get(x_277, 13);
x_462 = lean_ctor_get(x_277, 15);
x_463 = lean_ctor_get(x_277, 16);
lean_inc(x_463);
lean_inc(x_462);
lean_inc(x_461);
lean_inc(x_460);
lean_inc(x_459);
lean_inc(x_458);
lean_inc(x_457);
lean_inc(x_456);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
lean_inc(x_449);
lean_inc(x_448);
lean_inc(x_447);
lean_dec(x_277);
x_464 = lean_ctor_get(x_278, 0);
lean_inc_ref(x_464);
x_465 = lean_ctor_get(x_278, 2);
lean_inc_ref(x_465);
x_466 = lean_ctor_get(x_278, 3);
lean_inc_ref(x_466);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 lean_ctor_release(x_278, 2);
 lean_ctor_release(x_278, 3);
 x_467 = x_278;
} else {
 lean_dec_ref(x_278);
 x_467 = lean_box(0);
}
x_468 = lean_ctor_get(x_279, 0);
lean_inc_ref(x_468);
x_469 = lean_ctor_get(x_279, 1);
lean_inc_ref(x_469);
x_470 = lean_ctor_get(x_279, 2);
lean_inc_ref(x_470);
x_471 = lean_ctor_get(x_279, 3);
lean_inc_ref(x_471);
x_472 = lean_ctor_get(x_279, 4);
lean_inc_ref(x_472);
x_473 = lean_ctor_get(x_279, 5);
lean_inc_ref(x_473);
x_474 = lean_ctor_get(x_279, 6);
lean_inc_ref(x_474);
x_475 = lean_ctor_get(x_279, 7);
lean_inc_ref(x_475);
x_476 = lean_ctor_get(x_279, 8);
lean_inc_ref(x_476);
x_477 = lean_ctor_get(x_279, 9);
lean_inc_ref(x_477);
x_478 = lean_ctor_get(x_279, 10);
lean_inc_ref(x_478);
x_479 = lean_ctor_get(x_279, 11);
lean_inc(x_479);
x_480 = lean_ctor_get(x_279, 12);
lean_inc_ref(x_480);
x_481 = lean_ctor_get(x_279, 13);
lean_inc_ref(x_481);
x_482 = lean_ctor_get(x_279, 14);
lean_inc(x_482);
x_483 = lean_ctor_get_uint8(x_279, sizeof(void*)*22);
x_484 = lean_ctor_get(x_279, 15);
lean_inc(x_484);
x_485 = lean_ctor_get(x_279, 16);
lean_inc_ref(x_485);
x_486 = lean_ctor_get(x_279, 17);
lean_inc_ref(x_486);
x_487 = lean_ctor_get(x_279, 18);
lean_inc_ref(x_487);
x_488 = lean_ctor_get(x_279, 19);
lean_inc_ref(x_488);
x_489 = lean_ctor_get(x_279, 20);
lean_inc_ref(x_489);
x_490 = lean_ctor_get_uint8(x_279, sizeof(void*)*22 + 1);
x_491 = lean_ctor_get(x_279, 21);
lean_inc_ref(x_491);
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
 lean_ctor_release(x_279, 17);
 lean_ctor_release(x_279, 18);
 lean_ctor_release(x_279, 19);
 lean_ctor_release(x_279, 20);
 lean_ctor_release(x_279, 21);
 x_492 = x_279;
} else {
 lean_dec_ref(x_279);
 x_492 = lean_box(0);
}
x_493 = lean_box(0);
x_494 = l_Lean_PersistentArray_set___redArg(x_474, x_213, x_493);
if (lean_is_scalar(x_492)) {
 x_495 = lean_alloc_ctor(0, 22, 2);
} else {
 x_495 = x_492;
}
lean_ctor_set(x_495, 0, x_468);
lean_ctor_set(x_495, 1, x_469);
lean_ctor_set(x_495, 2, x_470);
lean_ctor_set(x_495, 3, x_471);
lean_ctor_set(x_495, 4, x_472);
lean_ctor_set(x_495, 5, x_473);
lean_ctor_set(x_495, 6, x_494);
lean_ctor_set(x_495, 7, x_475);
lean_ctor_set(x_495, 8, x_476);
lean_ctor_set(x_495, 9, x_477);
lean_ctor_set(x_495, 10, x_478);
lean_ctor_set(x_495, 11, x_479);
lean_ctor_set(x_495, 12, x_480);
lean_ctor_set(x_495, 13, x_481);
lean_ctor_set(x_495, 14, x_482);
lean_ctor_set(x_495, 15, x_484);
lean_ctor_set(x_495, 16, x_485);
lean_ctor_set(x_495, 17, x_486);
lean_ctor_set(x_495, 18, x_487);
lean_ctor_set(x_495, 19, x_488);
lean_ctor_set(x_495, 20, x_489);
lean_ctor_set(x_495, 21, x_491);
lean_ctor_set_uint8(x_495, sizeof(void*)*22, x_483);
lean_ctor_set_uint8(x_495, sizeof(void*)*22 + 1, x_490);
if (lean_is_scalar(x_467)) {
 x_496 = lean_alloc_ctor(0, 4, 0);
} else {
 x_496 = x_467;
}
lean_ctor_set(x_496, 0, x_464);
lean_ctor_set(x_496, 1, x_495);
lean_ctor_set(x_496, 2, x_465);
lean_ctor_set(x_496, 3, x_466);
x_497 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_497, 0, x_447);
lean_ctor_set(x_497, 1, x_448);
lean_ctor_set(x_497, 2, x_449);
lean_ctor_set(x_497, 3, x_450);
lean_ctor_set(x_497, 4, x_451);
lean_ctor_set(x_497, 5, x_452);
lean_ctor_set(x_497, 6, x_453);
lean_ctor_set(x_497, 7, x_454);
lean_ctor_set(x_497, 8, x_456);
lean_ctor_set(x_497, 9, x_457);
lean_ctor_set(x_497, 10, x_458);
lean_ctor_set(x_497, 11, x_459);
lean_ctor_set(x_497, 12, x_460);
lean_ctor_set(x_497, 13, x_461);
lean_ctor_set(x_497, 14, x_496);
lean_ctor_set(x_497, 15, x_462);
lean_ctor_set(x_497, 16, x_463);
lean_ctor_set_uint8(x_497, sizeof(void*)*17, x_455);
x_498 = lean_st_ref_set(x_217, x_497, x_280);
x_499 = lean_ctor_get(x_498, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_500 = x_498;
} else {
 lean_dec_ref(x_498);
 x_500 = lean_box(0);
}
x_501 = lean_int_mul(x_274, x_265);
lean_dec(x_274);
lean_inc_ref(x_215);
x_502 = l_Int_Linear_Poly_mul(x_215, x_501);
lean_dec(x_501);
x_503 = lean_int_mul(x_275, x_219);
lean_dec(x_275);
lean_inc_ref(x_267);
x_504 = l_Int_Linear_Poly_mul(x_267, x_503);
lean_dec(x_503);
x_505 = lean_int_mul(x_219, x_265);
lean_dec(x_219);
x_506 = l_Int_Linear_Poly_combine(x_502, x_504);
lean_inc(x_273);
lean_ctor_set(x_262, 2, x_506);
lean_ctor_set(x_262, 1, x_213);
lean_ctor_set(x_262, 0, x_273);
lean_inc(x_261);
lean_inc_ref(x_223);
if (lean_is_scalar(x_500)) {
 x_507 = lean_alloc_ctor(4, 2, 0);
} else {
 x_507 = x_500;
 lean_ctor_set_tag(x_507, 4);
}
lean_ctor_set(x_507, 0, x_223);
lean_ctor_set(x_507, 1, x_261);
x_508 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_262);
lean_ctor_set(x_508, 2, x_507);
lean_inc(x_226);
lean_inc_ref(x_220);
lean_inc(x_224);
lean_inc_ref(x_225);
lean_inc(x_218);
lean_inc_ref(x_221);
lean_inc(x_222);
lean_inc(x_217);
x_509 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_508, x_217, x_222, x_221, x_218, x_225, x_224, x_220, x_226, x_499);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_510 = lean_ctor_get(x_509, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_511 = x_509;
} else {
 lean_dec_ref(x_509);
 x_511 = lean_box(0);
}
x_512 = l_Int_Linear_Poly_mul(x_215, x_266);
lean_dec(x_266);
x_513 = lean_int_neg(x_216);
lean_dec(x_216);
x_514 = l_Int_Linear_Poly_mul(x_267, x_513);
lean_dec(x_513);
x_515 = l_Int_Linear_Poly_combine(x_512, x_514);
lean_inc(x_261);
if (lean_is_scalar(x_511)) {
 x_516 = lean_alloc_ctor(5, 2, 0);
} else {
 x_516 = x_511;
 lean_ctor_set_tag(x_516, 5);
}
lean_ctor_set(x_516, 0, x_223);
lean_ctor_set(x_516, 1, x_261);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 x_517 = x_261;
} else {
 lean_dec_ref(x_261);
 x_517 = lean_box(0);
}
if (lean_is_scalar(x_517)) {
 x_518 = lean_alloc_ctor(0, 3, 0);
} else {
 x_518 = x_517;
}
lean_ctor_set(x_518, 0, x_273);
lean_ctor_set(x_518, 1, x_515);
lean_ctor_set(x_518, 2, x_516);
x_1 = x_518;
x_2 = x_217;
x_3 = x_222;
x_4 = x_221;
x_5 = x_218;
x_6 = x_225;
x_7 = x_224;
x_8 = x_220;
x_9 = x_226;
x_10 = x_510;
goto _start;
}
else
{
lean_dec(x_273);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec(x_261);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec_ref(x_220);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec_ref(x_215);
return x_509;
}
}
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; uint8_t x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_520 = lean_ctor_get(x_261, 0);
x_521 = lean_ctor_get(x_262, 0);
x_522 = lean_ctor_get(x_262, 2);
lean_inc(x_522);
lean_inc(x_521);
lean_dec(x_262);
x_523 = lean_int_mul(x_216, x_520);
x_524 = lean_int_mul(x_521, x_219);
x_525 = l_Lean_Meta_Grind_Arith_gcdExt(x_523, x_524);
lean_dec(x_524);
lean_dec(x_523);
x_526 = lean_ctor_get(x_525, 1);
lean_inc(x_526);
x_527 = lean_ctor_get(x_525, 0);
lean_inc(x_527);
lean_dec_ref(x_525);
x_528 = lean_ctor_get(x_526, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_526, 1);
lean_inc(x_529);
lean_dec(x_526);
x_530 = lean_st_ref_take(x_217, x_227);
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_531, 14);
lean_inc_ref(x_532);
x_533 = lean_ctor_get(x_532, 1);
lean_inc_ref(x_533);
x_534 = lean_ctor_get(x_530, 1);
lean_inc(x_534);
lean_dec_ref(x_530);
x_535 = lean_ctor_get(x_531, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_531, 1);
lean_inc_ref(x_536);
x_537 = lean_ctor_get(x_531, 2);
lean_inc(x_537);
x_538 = lean_ctor_get(x_531, 3);
lean_inc_ref(x_538);
x_539 = lean_ctor_get(x_531, 4);
lean_inc_ref(x_539);
x_540 = lean_ctor_get(x_531, 5);
lean_inc_ref(x_540);
x_541 = lean_ctor_get(x_531, 6);
lean_inc_ref(x_541);
x_542 = lean_ctor_get(x_531, 7);
lean_inc_ref(x_542);
x_543 = lean_ctor_get_uint8(x_531, sizeof(void*)*17);
x_544 = lean_ctor_get(x_531, 8);
lean_inc(x_544);
x_545 = lean_ctor_get(x_531, 9);
lean_inc_ref(x_545);
x_546 = lean_ctor_get(x_531, 10);
lean_inc_ref(x_546);
x_547 = lean_ctor_get(x_531, 11);
lean_inc_ref(x_547);
x_548 = lean_ctor_get(x_531, 12);
lean_inc_ref(x_548);
x_549 = lean_ctor_get(x_531, 13);
lean_inc_ref(x_549);
x_550 = lean_ctor_get(x_531, 15);
lean_inc_ref(x_550);
x_551 = lean_ctor_get(x_531, 16);
lean_inc_ref(x_551);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 lean_ctor_release(x_531, 2);
 lean_ctor_release(x_531, 3);
 lean_ctor_release(x_531, 4);
 lean_ctor_release(x_531, 5);
 lean_ctor_release(x_531, 6);
 lean_ctor_release(x_531, 7);
 lean_ctor_release(x_531, 8);
 lean_ctor_release(x_531, 9);
 lean_ctor_release(x_531, 10);
 lean_ctor_release(x_531, 11);
 lean_ctor_release(x_531, 12);
 lean_ctor_release(x_531, 13);
 lean_ctor_release(x_531, 14);
 lean_ctor_release(x_531, 15);
 lean_ctor_release(x_531, 16);
 x_552 = x_531;
} else {
 lean_dec_ref(x_531);
 x_552 = lean_box(0);
}
x_553 = lean_ctor_get(x_532, 0);
lean_inc_ref(x_553);
x_554 = lean_ctor_get(x_532, 2);
lean_inc_ref(x_554);
x_555 = lean_ctor_get(x_532, 3);
lean_inc_ref(x_555);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 lean_ctor_release(x_532, 2);
 lean_ctor_release(x_532, 3);
 x_556 = x_532;
} else {
 lean_dec_ref(x_532);
 x_556 = lean_box(0);
}
x_557 = lean_ctor_get(x_533, 0);
lean_inc_ref(x_557);
x_558 = lean_ctor_get(x_533, 1);
lean_inc_ref(x_558);
x_559 = lean_ctor_get(x_533, 2);
lean_inc_ref(x_559);
x_560 = lean_ctor_get(x_533, 3);
lean_inc_ref(x_560);
x_561 = lean_ctor_get(x_533, 4);
lean_inc_ref(x_561);
x_562 = lean_ctor_get(x_533, 5);
lean_inc_ref(x_562);
x_563 = lean_ctor_get(x_533, 6);
lean_inc_ref(x_563);
x_564 = lean_ctor_get(x_533, 7);
lean_inc_ref(x_564);
x_565 = lean_ctor_get(x_533, 8);
lean_inc_ref(x_565);
x_566 = lean_ctor_get(x_533, 9);
lean_inc_ref(x_566);
x_567 = lean_ctor_get(x_533, 10);
lean_inc_ref(x_567);
x_568 = lean_ctor_get(x_533, 11);
lean_inc(x_568);
x_569 = lean_ctor_get(x_533, 12);
lean_inc_ref(x_569);
x_570 = lean_ctor_get(x_533, 13);
lean_inc_ref(x_570);
x_571 = lean_ctor_get(x_533, 14);
lean_inc(x_571);
x_572 = lean_ctor_get_uint8(x_533, sizeof(void*)*22);
x_573 = lean_ctor_get(x_533, 15);
lean_inc(x_573);
x_574 = lean_ctor_get(x_533, 16);
lean_inc_ref(x_574);
x_575 = lean_ctor_get(x_533, 17);
lean_inc_ref(x_575);
x_576 = lean_ctor_get(x_533, 18);
lean_inc_ref(x_576);
x_577 = lean_ctor_get(x_533, 19);
lean_inc_ref(x_577);
x_578 = lean_ctor_get(x_533, 20);
lean_inc_ref(x_578);
x_579 = lean_ctor_get_uint8(x_533, sizeof(void*)*22 + 1);
x_580 = lean_ctor_get(x_533, 21);
lean_inc_ref(x_580);
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
 lean_ctor_release(x_533, 18);
 lean_ctor_release(x_533, 19);
 lean_ctor_release(x_533, 20);
 lean_ctor_release(x_533, 21);
 x_581 = x_533;
} else {
 lean_dec_ref(x_533);
 x_581 = lean_box(0);
}
x_582 = lean_box(0);
x_583 = l_Lean_PersistentArray_set___redArg(x_563, x_213, x_582);
if (lean_is_scalar(x_581)) {
 x_584 = lean_alloc_ctor(0, 22, 2);
} else {
 x_584 = x_581;
}
lean_ctor_set(x_584, 0, x_557);
lean_ctor_set(x_584, 1, x_558);
lean_ctor_set(x_584, 2, x_559);
lean_ctor_set(x_584, 3, x_560);
lean_ctor_set(x_584, 4, x_561);
lean_ctor_set(x_584, 5, x_562);
lean_ctor_set(x_584, 6, x_583);
lean_ctor_set(x_584, 7, x_564);
lean_ctor_set(x_584, 8, x_565);
lean_ctor_set(x_584, 9, x_566);
lean_ctor_set(x_584, 10, x_567);
lean_ctor_set(x_584, 11, x_568);
lean_ctor_set(x_584, 12, x_569);
lean_ctor_set(x_584, 13, x_570);
lean_ctor_set(x_584, 14, x_571);
lean_ctor_set(x_584, 15, x_573);
lean_ctor_set(x_584, 16, x_574);
lean_ctor_set(x_584, 17, x_575);
lean_ctor_set(x_584, 18, x_576);
lean_ctor_set(x_584, 19, x_577);
lean_ctor_set(x_584, 20, x_578);
lean_ctor_set(x_584, 21, x_580);
lean_ctor_set_uint8(x_584, sizeof(void*)*22, x_572);
lean_ctor_set_uint8(x_584, sizeof(void*)*22 + 1, x_579);
if (lean_is_scalar(x_556)) {
 x_585 = lean_alloc_ctor(0, 4, 0);
} else {
 x_585 = x_556;
}
lean_ctor_set(x_585, 0, x_553);
lean_ctor_set(x_585, 1, x_584);
lean_ctor_set(x_585, 2, x_554);
lean_ctor_set(x_585, 3, x_555);
if (lean_is_scalar(x_552)) {
 x_586 = lean_alloc_ctor(0, 17, 1);
} else {
 x_586 = x_552;
}
lean_ctor_set(x_586, 0, x_535);
lean_ctor_set(x_586, 1, x_536);
lean_ctor_set(x_586, 2, x_537);
lean_ctor_set(x_586, 3, x_538);
lean_ctor_set(x_586, 4, x_539);
lean_ctor_set(x_586, 5, x_540);
lean_ctor_set(x_586, 6, x_541);
lean_ctor_set(x_586, 7, x_542);
lean_ctor_set(x_586, 8, x_544);
lean_ctor_set(x_586, 9, x_545);
lean_ctor_set(x_586, 10, x_546);
lean_ctor_set(x_586, 11, x_547);
lean_ctor_set(x_586, 12, x_548);
lean_ctor_set(x_586, 13, x_549);
lean_ctor_set(x_586, 14, x_585);
lean_ctor_set(x_586, 15, x_550);
lean_ctor_set(x_586, 16, x_551);
lean_ctor_set_uint8(x_586, sizeof(void*)*17, x_543);
x_587 = lean_st_ref_set(x_217, x_586, x_534);
x_588 = lean_ctor_get(x_587, 1);
lean_inc(x_588);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_589 = x_587;
} else {
 lean_dec_ref(x_587);
 x_589 = lean_box(0);
}
x_590 = lean_int_mul(x_528, x_520);
lean_dec(x_528);
lean_inc_ref(x_215);
x_591 = l_Int_Linear_Poly_mul(x_215, x_590);
lean_dec(x_590);
x_592 = lean_int_mul(x_529, x_219);
lean_dec(x_529);
lean_inc_ref(x_522);
x_593 = l_Int_Linear_Poly_mul(x_522, x_592);
lean_dec(x_592);
x_594 = lean_int_mul(x_219, x_520);
lean_dec(x_219);
x_595 = l_Int_Linear_Poly_combine(x_591, x_593);
lean_inc(x_527);
x_596 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_596, 0, x_527);
lean_ctor_set(x_596, 1, x_213);
lean_ctor_set(x_596, 2, x_595);
lean_inc(x_261);
lean_inc_ref(x_223);
if (lean_is_scalar(x_589)) {
 x_597 = lean_alloc_ctor(4, 2, 0);
} else {
 x_597 = x_589;
 lean_ctor_set_tag(x_597, 4);
}
lean_ctor_set(x_597, 0, x_223);
lean_ctor_set(x_597, 1, x_261);
x_598 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_598, 0, x_594);
lean_ctor_set(x_598, 1, x_596);
lean_ctor_set(x_598, 2, x_597);
lean_inc(x_226);
lean_inc_ref(x_220);
lean_inc(x_224);
lean_inc_ref(x_225);
lean_inc(x_218);
lean_inc_ref(x_221);
lean_inc(x_222);
lean_inc(x_217);
x_599 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_598, x_217, x_222, x_221, x_218, x_225, x_224, x_220, x_226, x_588);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_600 = lean_ctor_get(x_599, 1);
lean_inc(x_600);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 lean_ctor_release(x_599, 1);
 x_601 = x_599;
} else {
 lean_dec_ref(x_599);
 x_601 = lean_box(0);
}
x_602 = l_Int_Linear_Poly_mul(x_215, x_521);
lean_dec(x_521);
x_603 = lean_int_neg(x_216);
lean_dec(x_216);
x_604 = l_Int_Linear_Poly_mul(x_522, x_603);
lean_dec(x_603);
x_605 = l_Int_Linear_Poly_combine(x_602, x_604);
lean_inc(x_261);
if (lean_is_scalar(x_601)) {
 x_606 = lean_alloc_ctor(5, 2, 0);
} else {
 x_606 = x_601;
 lean_ctor_set_tag(x_606, 5);
}
lean_ctor_set(x_606, 0, x_223);
lean_ctor_set(x_606, 1, x_261);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 x_607 = x_261;
} else {
 lean_dec_ref(x_261);
 x_607 = lean_box(0);
}
if (lean_is_scalar(x_607)) {
 x_608 = lean_alloc_ctor(0, 3, 0);
} else {
 x_608 = x_607;
}
lean_ctor_set(x_608, 0, x_527);
lean_ctor_set(x_608, 1, x_605);
lean_ctor_set(x_608, 2, x_606);
x_1 = x_608;
x_2 = x_217;
x_3 = x_222;
x_4 = x_221;
x_5 = x_218;
x_6 = x_225;
x_7 = x_224;
x_8 = x_220;
x_9 = x_226;
x_10 = x_600;
goto _start;
}
else
{
lean_dec(x_527);
lean_dec_ref(x_522);
lean_dec(x_521);
lean_dec(x_261);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec_ref(x_220);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec_ref(x_215);
return x_599;
}
}
}
}
}
block_644:
{
lean_object* x_632; 
x_632 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_623, x_631);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; uint8_t x_637; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_633, 6);
lean_inc_ref(x_634);
lean_dec(x_633);
x_635 = lean_ctor_get(x_632, 1);
lean_inc(x_635);
lean_dec_ref(x_632);
x_636 = lean_ctor_get(x_634, 2);
x_637 = lean_nat_dec_lt(x_617, x_636);
if (x_637 == 0)
{
lean_object* x_638; 
lean_dec_ref(x_634);
x_638 = l_outOfBounds___redArg(x_616);
x_213 = x_617;
x_214 = x_620;
x_215 = x_621;
x_216 = x_622;
x_217 = x_623;
x_218 = x_626;
x_219 = x_618;
x_220 = x_629;
x_221 = x_625;
x_222 = x_624;
x_223 = x_619;
x_224 = x_628;
x_225 = x_627;
x_226 = x_630;
x_227 = x_635;
x_228 = x_638;
goto block_610;
}
else
{
lean_object* x_639; 
x_639 = l_Lean_PersistentArray_get_x21___redArg(x_616, x_634, x_617);
x_213 = x_617;
x_214 = x_620;
x_215 = x_621;
x_216 = x_622;
x_217 = x_623;
x_218 = x_626;
x_219 = x_618;
x_220 = x_629;
x_221 = x_625;
x_222 = x_624;
x_223 = x_619;
x_224 = x_628;
x_225 = x_627;
x_226 = x_630;
x_227 = x_635;
x_228 = x_639;
goto block_610;
}
}
else
{
uint8_t x_640; 
lean_dec(x_630);
lean_dec_ref(x_629);
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_622);
lean_dec_ref(x_621);
lean_dec_ref(x_620);
lean_dec_ref(x_619);
lean_dec(x_618);
lean_dec(x_617);
x_640 = !lean_is_exclusive(x_632);
if (x_640 == 0)
{
return x_632;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_632, 0);
x_642 = lean_ctor_get(x_632, 1);
lean_inc(x_642);
lean_inc(x_641);
lean_dec(x_632);
x_643 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_643, 0, x_641);
lean_ctor_set(x_643, 1, x_642);
return x_643;
}
}
}
block_746:
{
lean_object* x_654; lean_object* x_655; 
x_654 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_651);
x_655 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_654, x_645, x_646, x_647, x_648, x_649, x_650, x_651, x_652, x_653);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; uint8_t x_660; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
lean_dec_ref(x_655);
x_658 = lean_ctor_get(x_656, 0);
x_659 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
x_660 = l_Int_Linear_Poly_isUnsatDvd(x_658, x_659);
if (x_660 == 0)
{
uint8_t x_661; 
x_661 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_656);
if (x_661 == 0)
{
lean_dec(x_615);
if (lean_obj_tag(x_659) == 0)
{
lean_object* x_662; 
x_662 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_656, x_645, x_646, x_647, x_648, x_649, x_650, x_651, x_652, x_657);
lean_dec(x_652);
lean_dec_ref(x_651);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec(x_645);
return x_662;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
lean_inc_ref(x_659);
lean_inc(x_658);
x_663 = lean_ctor_get(x_659, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_659, 1);
lean_inc(x_664);
x_665 = lean_ctor_get(x_659, 2);
lean_inc_ref(x_665);
lean_inc(x_656);
x_666 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_656, x_645, x_657);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; lean_object* x_668; uint8_t x_669; uint8_t x_670; uint8_t x_671; 
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_666, 1);
lean_inc(x_668);
lean_dec_ref(x_666);
x_669 = 0;
x_670 = lean_unbox(x_667);
lean_dec(x_667);
x_671 = l_Lean_beqLBool____x40_Lean_Data_LBool_27903016____hygCtx___hyg_13_(x_670, x_669);
if (x_671 == 0)
{
x_617 = x_664;
x_618 = x_658;
x_619 = x_656;
x_620 = x_659;
x_621 = x_665;
x_622 = x_663;
x_623 = x_645;
x_624 = x_646;
x_625 = x_647;
x_626 = x_648;
x_627 = x_649;
x_628 = x_650;
x_629 = x_651;
x_630 = x_652;
x_631 = x_668;
goto block_644;
}
else
{
lean_object* x_672; 
x_672 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_664, x_645, x_668);
if (lean_obj_tag(x_672) == 0)
{
lean_object* x_673; 
x_673 = lean_ctor_get(x_672, 1);
lean_inc(x_673);
lean_dec_ref(x_672);
x_617 = x_664;
x_618 = x_658;
x_619 = x_656;
x_620 = x_659;
x_621 = x_665;
x_622 = x_663;
x_623 = x_645;
x_624 = x_646;
x_625 = x_647;
x_626 = x_648;
x_627 = x_649;
x_628 = x_650;
x_629 = x_651;
x_630 = x_652;
x_631 = x_673;
goto block_644;
}
else
{
lean_dec_ref(x_665);
lean_dec(x_664);
lean_dec(x_663);
lean_dec_ref(x_659);
lean_dec(x_658);
lean_dec(x_656);
lean_dec(x_652);
lean_dec_ref(x_651);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec(x_645);
return x_672;
}
}
}
else
{
uint8_t x_674; 
lean_dec_ref(x_665);
lean_dec(x_664);
lean_dec(x_663);
lean_dec_ref(x_659);
lean_dec(x_658);
lean_dec(x_656);
lean_dec(x_652);
lean_dec_ref(x_651);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec(x_645);
x_674 = !lean_is_exclusive(x_666);
if (x_674 == 0)
{
return x_666;
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_675 = lean_ctor_get(x_666, 0);
x_676 = lean_ctor_get(x_666, 1);
lean_inc(x_676);
lean_inc(x_675);
lean_dec(x_666);
x_677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_677, 0, x_675);
lean_ctor_set(x_677, 1, x_676);
return x_677;
}
}
}
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; uint8_t x_681; 
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_646);
x_678 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_679 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_678, x_651, x_657);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_unbox(x_680);
lean_dec(x_680);
if (x_681 == 0)
{
lean_object* x_682; 
lean_dec(x_656);
lean_dec(x_652);
lean_dec_ref(x_651);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_645);
lean_dec(x_615);
x_682 = lean_ctor_get(x_679, 1);
lean_inc(x_682);
lean_dec_ref(x_679);
x_187 = x_682;
goto block_190;
}
else
{
uint8_t x_683; 
x_683 = !lean_is_exclusive(x_679);
if (x_683 == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_684 = lean_ctor_get(x_679, 1);
x_685 = lean_ctor_get(x_679, 0);
lean_dec(x_685);
x_686 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_656, x_645, x_684);
lean_dec(x_645);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
lean_dec_ref(x_686);
x_689 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_679, 7);
lean_ctor_set(x_679, 1, x_687);
lean_ctor_set(x_679, 0, x_689);
if (lean_is_scalar(x_615)) {
 x_690 = lean_alloc_ctor(7, 2, 0);
} else {
 x_690 = x_615;
 lean_ctor_set_tag(x_690, 7);
}
lean_ctor_set(x_690, 0, x_679);
lean_ctor_set(x_690, 1, x_689);
x_691 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_678, x_690, x_649, x_650, x_651, x_652, x_688);
lean_dec(x_652);
lean_dec_ref(x_651);
lean_dec(x_650);
lean_dec_ref(x_649);
x_692 = lean_ctor_get(x_691, 1);
lean_inc(x_692);
lean_dec_ref(x_691);
x_187 = x_692;
goto block_190;
}
else
{
uint8_t x_693; 
lean_free_object(x_679);
lean_dec(x_652);
lean_dec_ref(x_651);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_615);
x_693 = !lean_is_exclusive(x_686);
if (x_693 == 0)
{
return x_686;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_694 = lean_ctor_get(x_686, 0);
x_695 = lean_ctor_get(x_686, 1);
lean_inc(x_695);
lean_inc(x_694);
lean_dec(x_686);
x_696 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_696, 0, x_694);
lean_ctor_set(x_696, 1, x_695);
return x_696;
}
}
}
else
{
lean_object* x_697; lean_object* x_698; 
x_697 = lean_ctor_get(x_679, 1);
lean_inc(x_697);
lean_dec(x_679);
x_698 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_656, x_645, x_697);
lean_dec(x_645);
if (lean_obj_tag(x_698) == 0)
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
x_699 = lean_ctor_get(x_698, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_698, 1);
lean_inc(x_700);
lean_dec_ref(x_698);
x_701 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_702 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_702, 0, x_701);
lean_ctor_set(x_702, 1, x_699);
if (lean_is_scalar(x_615)) {
 x_703 = lean_alloc_ctor(7, 2, 0);
} else {
 x_703 = x_615;
 lean_ctor_set_tag(x_703, 7);
}
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_701);
x_704 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_678, x_703, x_649, x_650, x_651, x_652, x_700);
lean_dec(x_652);
lean_dec_ref(x_651);
lean_dec(x_650);
lean_dec_ref(x_649);
x_705 = lean_ctor_get(x_704, 1);
lean_inc(x_705);
lean_dec_ref(x_704);
x_187 = x_705;
goto block_190;
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
lean_dec(x_652);
lean_dec_ref(x_651);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_615);
x_706 = lean_ctor_get(x_698, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_698, 1);
lean_inc(x_707);
if (lean_is_exclusive(x_698)) {
 lean_ctor_release(x_698, 0);
 lean_ctor_release(x_698, 1);
 x_708 = x_698;
} else {
 lean_dec_ref(x_698);
 x_708 = lean_box(0);
}
if (lean_is_scalar(x_708)) {
 x_709 = lean_alloc_ctor(1, 2, 0);
} else {
 x_709 = x_708;
}
lean_ctor_set(x_709, 0, x_706);
lean_ctor_set(x_709, 1, x_707);
return x_709;
}
}
}
}
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; uint8_t x_713; 
x_710 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_711 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_710, x_651, x_657);
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_unbox(x_712);
lean_dec(x_712);
if (x_713 == 0)
{
lean_object* x_714; 
lean_dec(x_615);
x_714 = lean_ctor_get(x_711, 1);
lean_inc(x_714);
lean_dec_ref(x_711);
x_168 = x_656;
x_169 = x_645;
x_170 = x_646;
x_171 = x_647;
x_172 = x_648;
x_173 = x_649;
x_174 = x_650;
x_175 = x_651;
x_176 = x_652;
x_177 = x_714;
goto block_186;
}
else
{
uint8_t x_715; 
x_715 = !lean_is_exclusive(x_711);
if (x_715 == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_716 = lean_ctor_get(x_711, 1);
x_717 = lean_ctor_get(x_711, 0);
lean_dec(x_717);
lean_inc(x_656);
x_718 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_656, x_645, x_716);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
lean_dec_ref(x_718);
x_721 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_711, 7);
lean_ctor_set(x_711, 1, x_719);
lean_ctor_set(x_711, 0, x_721);
if (lean_is_scalar(x_615)) {
 x_722 = lean_alloc_ctor(7, 2, 0);
} else {
 x_722 = x_615;
 lean_ctor_set_tag(x_722, 7);
}
lean_ctor_set(x_722, 0, x_711);
lean_ctor_set(x_722, 1, x_721);
x_723 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_710, x_722, x_649, x_650, x_651, x_652, x_720);
x_724 = lean_ctor_get(x_723, 1);
lean_inc(x_724);
lean_dec_ref(x_723);
x_168 = x_656;
x_169 = x_645;
x_170 = x_646;
x_171 = x_647;
x_172 = x_648;
x_173 = x_649;
x_174 = x_650;
x_175 = x_651;
x_176 = x_652;
x_177 = x_724;
goto block_186;
}
else
{
uint8_t x_725; 
lean_free_object(x_711);
lean_dec(x_656);
lean_dec(x_652);
lean_dec_ref(x_651);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec(x_645);
lean_dec(x_615);
x_725 = !lean_is_exclusive(x_718);
if (x_725 == 0)
{
return x_718;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_726 = lean_ctor_get(x_718, 0);
x_727 = lean_ctor_get(x_718, 1);
lean_inc(x_727);
lean_inc(x_726);
lean_dec(x_718);
x_728 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_728, 0, x_726);
lean_ctor_set(x_728, 1, x_727);
return x_728;
}
}
}
else
{
lean_object* x_729; lean_object* x_730; 
x_729 = lean_ctor_get(x_711, 1);
lean_inc(x_729);
lean_dec(x_711);
lean_inc(x_656);
x_730 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_656, x_645, x_729);
if (lean_obj_tag(x_730) == 0)
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
lean_dec_ref(x_730);
x_733 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_734 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_731);
if (lean_is_scalar(x_615)) {
 x_735 = lean_alloc_ctor(7, 2, 0);
} else {
 x_735 = x_615;
 lean_ctor_set_tag(x_735, 7);
}
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_733);
x_736 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_710, x_735, x_649, x_650, x_651, x_652, x_732);
x_737 = lean_ctor_get(x_736, 1);
lean_inc(x_737);
lean_dec_ref(x_736);
x_168 = x_656;
x_169 = x_645;
x_170 = x_646;
x_171 = x_647;
x_172 = x_648;
x_173 = x_649;
x_174 = x_650;
x_175 = x_651;
x_176 = x_652;
x_177 = x_737;
goto block_186;
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; 
lean_dec(x_656);
lean_dec(x_652);
lean_dec_ref(x_651);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec(x_645);
lean_dec(x_615);
x_738 = lean_ctor_get(x_730, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_730, 1);
lean_inc(x_739);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_740 = x_730;
} else {
 lean_dec_ref(x_730);
 x_740 = lean_box(0);
}
if (lean_is_scalar(x_740)) {
 x_741 = lean_alloc_ctor(1, 2, 0);
} else {
 x_741 = x_740;
}
lean_ctor_set(x_741, 0, x_738);
lean_ctor_set(x_741, 1, x_739);
return x_741;
}
}
}
}
}
else
{
uint8_t x_742; 
lean_dec(x_652);
lean_dec_ref(x_651);
lean_dec(x_650);
lean_dec_ref(x_649);
lean_dec(x_648);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec(x_645);
lean_dec(x_615);
x_742 = !lean_is_exclusive(x_655);
if (x_742 == 0)
{
return x_655;
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_743 = lean_ctor_get(x_655, 0);
x_744 = lean_ctor_get(x_655, 1);
lean_inc(x_744);
lean_inc(x_743);
lean_dec(x_655);
x_745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_745, 0, x_743);
lean_ctor_set(x_745, 1, x_744);
return x_745;
}
}
}
}
else
{
uint8_t x_760; 
lean_free_object(x_8);
lean_dec_ref(x_205);
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
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_760 = !lean_is_exclusive(x_207);
if (x_760 == 0)
{
lean_object* x_761; lean_object* x_762; 
x_761 = lean_ctor_get(x_207, 0);
lean_dec(x_761);
x_762 = lean_box(0);
lean_ctor_set(x_207, 0, x_762);
return x_207;
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_763 = lean_ctor_get(x_207, 1);
lean_inc(x_763);
lean_dec(x_207);
x_764 = lean_box(0);
x_765 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_765, 0, x_764);
lean_ctor_set(x_765, 1, x_763);
return x_765;
}
}
}
else
{
uint8_t x_766; 
lean_free_object(x_8);
lean_dec_ref(x_205);
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
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_766 = !lean_is_exclusive(x_207);
if (x_766 == 0)
{
return x_207;
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_767 = lean_ctor_get(x_207, 0);
x_768 = lean_ctor_get(x_207, 1);
lean_inc(x_768);
lean_inc(x_767);
lean_dec(x_207);
x_769 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_769, 0, x_767);
lean_ctor_set(x_769, 1, x_768);
return x_769;
}
}
}
else
{
lean_object* x_770; 
lean_free_object(x_8);
lean_dec_ref(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_770 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_197, x_10);
return x_770;
}
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; uint8_t x_783; lean_object* x_784; uint8_t x_785; lean_object* x_786; uint8_t x_787; 
x_771 = lean_ctor_get(x_8, 0);
x_772 = lean_ctor_get(x_8, 1);
x_773 = lean_ctor_get(x_8, 2);
x_774 = lean_ctor_get(x_8, 3);
x_775 = lean_ctor_get(x_8, 4);
x_776 = lean_ctor_get(x_8, 5);
x_777 = lean_ctor_get(x_8, 6);
x_778 = lean_ctor_get(x_8, 7);
x_779 = lean_ctor_get(x_8, 8);
x_780 = lean_ctor_get(x_8, 9);
x_781 = lean_ctor_get(x_8, 10);
x_782 = lean_ctor_get(x_8, 11);
x_783 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_784 = lean_ctor_get(x_8, 12);
x_785 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_786 = lean_ctor_get(x_8, 13);
lean_inc(x_786);
lean_inc(x_784);
lean_inc(x_782);
lean_inc(x_781);
lean_inc(x_780);
lean_inc(x_779);
lean_inc(x_778);
lean_inc(x_777);
lean_inc(x_776);
lean_inc(x_775);
lean_inc(x_774);
lean_inc(x_773);
lean_inc(x_772);
lean_inc(x_771);
lean_dec(x_8);
x_787 = lean_nat_dec_eq(x_774, x_775);
if (x_787 == 0)
{
lean_object* x_788; 
x_788 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; uint8_t x_790; 
x_789 = lean_ctor_get(x_788, 0);
lean_inc(x_789);
x_790 = lean_unbox(x_789);
lean_dec(x_789);
if (x_790 == 0)
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; uint8_t x_1035; 
x_791 = lean_ctor_get(x_788, 1);
lean_inc(x_791);
lean_dec_ref(x_788);
x_792 = lean_unsigned_to_nat(1u);
x_793 = lean_nat_add(x_774, x_792);
lean_dec(x_774);
x_794 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_794, 0, x_771);
lean_ctor_set(x_794, 1, x_772);
lean_ctor_set(x_794, 2, x_773);
lean_ctor_set(x_794, 3, x_793);
lean_ctor_set(x_794, 4, x_775);
lean_ctor_set(x_794, 5, x_776);
lean_ctor_set(x_794, 6, x_777);
lean_ctor_set(x_794, 7, x_778);
lean_ctor_set(x_794, 8, x_779);
lean_ctor_set(x_794, 9, x_780);
lean_ctor_set(x_794, 10, x_781);
lean_ctor_set(x_794, 11, x_782);
lean_ctor_set(x_794, 12, x_784);
lean_ctor_set(x_794, 13, x_786);
lean_ctor_set_uint8(x_794, sizeof(void*)*14, x_783);
lean_ctor_set_uint8(x_794, sizeof(void*)*14 + 1, x_785);
x_925 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_926 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_925, x_794, x_791);
x_927 = lean_ctor_get(x_926, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_926, 1);
lean_inc(x_928);
if (lean_is_exclusive(x_926)) {
 lean_ctor_release(x_926, 0);
 lean_ctor_release(x_926, 1);
 x_929 = x_926;
} else {
 lean_dec_ref(x_926);
 x_929 = lean_box(0);
}
x_930 = lean_box(0);
x_1035 = lean_unbox(x_927);
lean_dec(x_927);
if (x_1035 == 0)
{
x_959 = x_2;
x_960 = x_3;
x_961 = x_4;
x_962 = x_5;
x_963 = x_6;
x_964 = x_7;
x_965 = x_794;
x_966 = x_9;
x_967 = x_928;
goto block_1034;
}
else
{
lean_object* x_1036; 
lean_inc_ref(x_1);
x_1036 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_928);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1037 = lean_ctor_get(x_1036, 0);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_1036, 1);
lean_inc(x_1038);
lean_dec_ref(x_1036);
x_1039 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_1040 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1040, 0, x_1039);
lean_ctor_set(x_1040, 1, x_1037);
x_1041 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1041, 0, x_1040);
lean_ctor_set(x_1041, 1, x_1039);
x_1042 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_925, x_1041, x_6, x_7, x_794, x_9, x_1038);
x_1043 = lean_ctor_get(x_1042, 1);
lean_inc(x_1043);
lean_dec_ref(x_1042);
x_959 = x_2;
x_960 = x_3;
x_961 = x_4;
x_962 = x_5;
x_963 = x_6;
x_964 = x_7;
x_965 = x_794;
x_966 = x_9;
x_967 = x_1043;
goto block_1034;
}
else
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
lean_dec(x_929);
lean_dec_ref(x_794);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1044 = lean_ctor_get(x_1036, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1036, 1);
lean_inc(x_1045);
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 lean_ctor_release(x_1036, 1);
 x_1046 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1046 = lean_box(0);
}
if (lean_is_scalar(x_1046)) {
 x_1047 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1047 = x_1046;
}
lean_ctor_set(x_1047, 0, x_1044);
lean_ctor_set(x_1047, 1, x_1045);
return x_1047;
}
}
block_924:
{
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; uint8_t x_814; 
lean_dec(x_804);
lean_dec_ref(x_803);
lean_dec(x_801);
lean_dec(x_800);
lean_dec(x_798);
lean_dec_ref(x_797);
x_811 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_812 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_811, x_802, x_809);
x_813 = lean_ctor_get(x_812, 0);
lean_inc(x_813);
x_814 = lean_unbox(x_813);
lean_dec(x_813);
if (x_814 == 0)
{
lean_object* x_815; 
x_815 = lean_ctor_get(x_812, 1);
lean_inc(x_815);
lean_dec_ref(x_812);
x_11 = x_795;
x_12 = x_805;
x_13 = x_796;
x_14 = x_799;
x_15 = x_807;
x_16 = x_806;
x_17 = x_802;
x_18 = x_808;
x_19 = x_815;
goto block_167;
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_816 = lean_ctor_get(x_812, 1);
lean_inc(x_816);
if (lean_is_exclusive(x_812)) {
 lean_ctor_release(x_812, 0);
 lean_ctor_release(x_812, 1);
 x_817 = x_812;
} else {
 lean_dec_ref(x_812);
 x_817 = lean_box(0);
}
lean_inc_ref(x_805);
x_818 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_805, x_799, x_816);
if (lean_obj_tag(x_818) == 0)
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_819 = lean_ctor_get(x_818, 0);
lean_inc(x_819);
x_820 = lean_ctor_get(x_818, 1);
lean_inc(x_820);
lean_dec_ref(x_818);
x_821 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_817)) {
 x_822 = lean_alloc_ctor(7, 2, 0);
} else {
 x_822 = x_817;
 lean_ctor_set_tag(x_822, 7);
}
lean_ctor_set(x_822, 0, x_821);
lean_ctor_set(x_822, 1, x_819);
x_823 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_823, 0, x_822);
lean_ctor_set(x_823, 1, x_821);
x_824 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_811, x_823, x_807, x_806, x_802, x_808, x_820);
x_825 = lean_ctor_get(x_824, 1);
lean_inc(x_825);
lean_dec_ref(x_824);
x_11 = x_795;
x_12 = x_805;
x_13 = x_796;
x_14 = x_799;
x_15 = x_807;
x_16 = x_806;
x_17 = x_802;
x_18 = x_808;
x_19 = x_825;
goto block_167;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; 
lean_dec(x_817);
lean_dec(x_808);
lean_dec_ref(x_807);
lean_dec(x_806);
lean_dec_ref(x_805);
lean_dec_ref(x_802);
lean_dec(x_799);
lean_dec_ref(x_796);
lean_dec(x_795);
x_826 = lean_ctor_get(x_818, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_818, 1);
lean_inc(x_827);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 lean_ctor_release(x_818, 1);
 x_828 = x_818;
} else {
 lean_dec_ref(x_818);
 x_828 = lean_box(0);
}
if (lean_is_scalar(x_828)) {
 x_829 = lean_alloc_ctor(1, 2, 0);
} else {
 x_829 = x_828;
}
lean_ctor_set(x_829, 0, x_826);
lean_ctor_set(x_829, 1, x_827);
return x_829;
}
}
}
else
{
lean_object* x_830; lean_object* x_831; 
lean_dec_ref(x_796);
x_830 = lean_ctor_get(x_810, 0);
lean_inc(x_830);
lean_dec_ref(x_810);
x_831 = lean_ctor_get(x_830, 1);
lean_inc_ref(x_831);
if (lean_obj_tag(x_831) == 0)
{
lean_object* x_832; 
lean_dec_ref(x_831);
lean_dec_ref(x_805);
lean_dec(x_801);
lean_dec(x_798);
lean_dec_ref(x_797);
lean_dec(x_795);
x_832 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_830, x_799, x_804, x_803, x_800, x_807, x_806, x_802, x_808, x_809);
lean_dec(x_808);
lean_dec_ref(x_802);
lean_dec(x_806);
lean_dec_ref(x_807);
lean_dec(x_800);
lean_dec_ref(x_803);
lean_dec(x_804);
lean_dec(x_799);
return x_832;
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; uint8_t x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; uint8_t x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; uint8_t x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; 
x_833 = lean_ctor_get(x_830, 0);
x_834 = lean_ctor_get(x_831, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_831, 2);
lean_inc_ref(x_835);
if (lean_is_exclusive(x_831)) {
 lean_ctor_release(x_831, 0);
 lean_ctor_release(x_831, 1);
 lean_ctor_release(x_831, 2);
 x_836 = x_831;
} else {
 lean_dec_ref(x_831);
 x_836 = lean_box(0);
}
x_837 = lean_int_mul(x_798, x_833);
x_838 = lean_int_mul(x_834, x_801);
x_839 = l_Lean_Meta_Grind_Arith_gcdExt(x_837, x_838);
lean_dec(x_838);
lean_dec(x_837);
x_840 = lean_ctor_get(x_839, 1);
lean_inc(x_840);
x_841 = lean_ctor_get(x_839, 0);
lean_inc(x_841);
lean_dec_ref(x_839);
x_842 = lean_ctor_get(x_840, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_840, 1);
lean_inc(x_843);
lean_dec(x_840);
x_844 = lean_st_ref_take(x_799, x_809);
x_845 = lean_ctor_get(x_844, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_845, 14);
lean_inc_ref(x_846);
x_847 = lean_ctor_get(x_846, 1);
lean_inc_ref(x_847);
x_848 = lean_ctor_get(x_844, 1);
lean_inc(x_848);
lean_dec_ref(x_844);
x_849 = lean_ctor_get(x_845, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_845, 1);
lean_inc_ref(x_850);
x_851 = lean_ctor_get(x_845, 2);
lean_inc(x_851);
x_852 = lean_ctor_get(x_845, 3);
lean_inc_ref(x_852);
x_853 = lean_ctor_get(x_845, 4);
lean_inc_ref(x_853);
x_854 = lean_ctor_get(x_845, 5);
lean_inc_ref(x_854);
x_855 = lean_ctor_get(x_845, 6);
lean_inc_ref(x_855);
x_856 = lean_ctor_get(x_845, 7);
lean_inc_ref(x_856);
x_857 = lean_ctor_get_uint8(x_845, sizeof(void*)*17);
x_858 = lean_ctor_get(x_845, 8);
lean_inc(x_858);
x_859 = lean_ctor_get(x_845, 9);
lean_inc_ref(x_859);
x_860 = lean_ctor_get(x_845, 10);
lean_inc_ref(x_860);
x_861 = lean_ctor_get(x_845, 11);
lean_inc_ref(x_861);
x_862 = lean_ctor_get(x_845, 12);
lean_inc_ref(x_862);
x_863 = lean_ctor_get(x_845, 13);
lean_inc_ref(x_863);
x_864 = lean_ctor_get(x_845, 15);
lean_inc_ref(x_864);
x_865 = lean_ctor_get(x_845, 16);
lean_inc_ref(x_865);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 lean_ctor_release(x_845, 1);
 lean_ctor_release(x_845, 2);
 lean_ctor_release(x_845, 3);
 lean_ctor_release(x_845, 4);
 lean_ctor_release(x_845, 5);
 lean_ctor_release(x_845, 6);
 lean_ctor_release(x_845, 7);
 lean_ctor_release(x_845, 8);
 lean_ctor_release(x_845, 9);
 lean_ctor_release(x_845, 10);
 lean_ctor_release(x_845, 11);
 lean_ctor_release(x_845, 12);
 lean_ctor_release(x_845, 13);
 lean_ctor_release(x_845, 14);
 lean_ctor_release(x_845, 15);
 lean_ctor_release(x_845, 16);
 x_866 = x_845;
} else {
 lean_dec_ref(x_845);
 x_866 = lean_box(0);
}
x_867 = lean_ctor_get(x_846, 0);
lean_inc_ref(x_867);
x_868 = lean_ctor_get(x_846, 2);
lean_inc_ref(x_868);
x_869 = lean_ctor_get(x_846, 3);
lean_inc_ref(x_869);
if (lean_is_exclusive(x_846)) {
 lean_ctor_release(x_846, 0);
 lean_ctor_release(x_846, 1);
 lean_ctor_release(x_846, 2);
 lean_ctor_release(x_846, 3);
 x_870 = x_846;
} else {
 lean_dec_ref(x_846);
 x_870 = lean_box(0);
}
x_871 = lean_ctor_get(x_847, 0);
lean_inc_ref(x_871);
x_872 = lean_ctor_get(x_847, 1);
lean_inc_ref(x_872);
x_873 = lean_ctor_get(x_847, 2);
lean_inc_ref(x_873);
x_874 = lean_ctor_get(x_847, 3);
lean_inc_ref(x_874);
x_875 = lean_ctor_get(x_847, 4);
lean_inc_ref(x_875);
x_876 = lean_ctor_get(x_847, 5);
lean_inc_ref(x_876);
x_877 = lean_ctor_get(x_847, 6);
lean_inc_ref(x_877);
x_878 = lean_ctor_get(x_847, 7);
lean_inc_ref(x_878);
x_879 = lean_ctor_get(x_847, 8);
lean_inc_ref(x_879);
x_880 = lean_ctor_get(x_847, 9);
lean_inc_ref(x_880);
x_881 = lean_ctor_get(x_847, 10);
lean_inc_ref(x_881);
x_882 = lean_ctor_get(x_847, 11);
lean_inc(x_882);
x_883 = lean_ctor_get(x_847, 12);
lean_inc_ref(x_883);
x_884 = lean_ctor_get(x_847, 13);
lean_inc_ref(x_884);
x_885 = lean_ctor_get(x_847, 14);
lean_inc(x_885);
x_886 = lean_ctor_get_uint8(x_847, sizeof(void*)*22);
x_887 = lean_ctor_get(x_847, 15);
lean_inc(x_887);
x_888 = lean_ctor_get(x_847, 16);
lean_inc_ref(x_888);
x_889 = lean_ctor_get(x_847, 17);
lean_inc_ref(x_889);
x_890 = lean_ctor_get(x_847, 18);
lean_inc_ref(x_890);
x_891 = lean_ctor_get(x_847, 19);
lean_inc_ref(x_891);
x_892 = lean_ctor_get(x_847, 20);
lean_inc_ref(x_892);
x_893 = lean_ctor_get_uint8(x_847, sizeof(void*)*22 + 1);
x_894 = lean_ctor_get(x_847, 21);
lean_inc_ref(x_894);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 lean_ctor_release(x_847, 2);
 lean_ctor_release(x_847, 3);
 lean_ctor_release(x_847, 4);
 lean_ctor_release(x_847, 5);
 lean_ctor_release(x_847, 6);
 lean_ctor_release(x_847, 7);
 lean_ctor_release(x_847, 8);
 lean_ctor_release(x_847, 9);
 lean_ctor_release(x_847, 10);
 lean_ctor_release(x_847, 11);
 lean_ctor_release(x_847, 12);
 lean_ctor_release(x_847, 13);
 lean_ctor_release(x_847, 14);
 lean_ctor_release(x_847, 15);
 lean_ctor_release(x_847, 16);
 lean_ctor_release(x_847, 17);
 lean_ctor_release(x_847, 18);
 lean_ctor_release(x_847, 19);
 lean_ctor_release(x_847, 20);
 lean_ctor_release(x_847, 21);
 x_895 = x_847;
} else {
 lean_dec_ref(x_847);
 x_895 = lean_box(0);
}
x_896 = lean_box(0);
x_897 = l_Lean_PersistentArray_set___redArg(x_877, x_795, x_896);
if (lean_is_scalar(x_895)) {
 x_898 = lean_alloc_ctor(0, 22, 2);
} else {
 x_898 = x_895;
}
lean_ctor_set(x_898, 0, x_871);
lean_ctor_set(x_898, 1, x_872);
lean_ctor_set(x_898, 2, x_873);
lean_ctor_set(x_898, 3, x_874);
lean_ctor_set(x_898, 4, x_875);
lean_ctor_set(x_898, 5, x_876);
lean_ctor_set(x_898, 6, x_897);
lean_ctor_set(x_898, 7, x_878);
lean_ctor_set(x_898, 8, x_879);
lean_ctor_set(x_898, 9, x_880);
lean_ctor_set(x_898, 10, x_881);
lean_ctor_set(x_898, 11, x_882);
lean_ctor_set(x_898, 12, x_883);
lean_ctor_set(x_898, 13, x_884);
lean_ctor_set(x_898, 14, x_885);
lean_ctor_set(x_898, 15, x_887);
lean_ctor_set(x_898, 16, x_888);
lean_ctor_set(x_898, 17, x_889);
lean_ctor_set(x_898, 18, x_890);
lean_ctor_set(x_898, 19, x_891);
lean_ctor_set(x_898, 20, x_892);
lean_ctor_set(x_898, 21, x_894);
lean_ctor_set_uint8(x_898, sizeof(void*)*22, x_886);
lean_ctor_set_uint8(x_898, sizeof(void*)*22 + 1, x_893);
if (lean_is_scalar(x_870)) {
 x_899 = lean_alloc_ctor(0, 4, 0);
} else {
 x_899 = x_870;
}
lean_ctor_set(x_899, 0, x_867);
lean_ctor_set(x_899, 1, x_898);
lean_ctor_set(x_899, 2, x_868);
lean_ctor_set(x_899, 3, x_869);
if (lean_is_scalar(x_866)) {
 x_900 = lean_alloc_ctor(0, 17, 1);
} else {
 x_900 = x_866;
}
lean_ctor_set(x_900, 0, x_849);
lean_ctor_set(x_900, 1, x_850);
lean_ctor_set(x_900, 2, x_851);
lean_ctor_set(x_900, 3, x_852);
lean_ctor_set(x_900, 4, x_853);
lean_ctor_set(x_900, 5, x_854);
lean_ctor_set(x_900, 6, x_855);
lean_ctor_set(x_900, 7, x_856);
lean_ctor_set(x_900, 8, x_858);
lean_ctor_set(x_900, 9, x_859);
lean_ctor_set(x_900, 10, x_860);
lean_ctor_set(x_900, 11, x_861);
lean_ctor_set(x_900, 12, x_862);
lean_ctor_set(x_900, 13, x_863);
lean_ctor_set(x_900, 14, x_899);
lean_ctor_set(x_900, 15, x_864);
lean_ctor_set(x_900, 16, x_865);
lean_ctor_set_uint8(x_900, sizeof(void*)*17, x_857);
x_901 = lean_st_ref_set(x_799, x_900, x_848);
x_902 = lean_ctor_get(x_901, 1);
lean_inc(x_902);
if (lean_is_exclusive(x_901)) {
 lean_ctor_release(x_901, 0);
 lean_ctor_release(x_901, 1);
 x_903 = x_901;
} else {
 lean_dec_ref(x_901);
 x_903 = lean_box(0);
}
x_904 = lean_int_mul(x_842, x_833);
lean_dec(x_842);
lean_inc_ref(x_797);
x_905 = l_Int_Linear_Poly_mul(x_797, x_904);
lean_dec(x_904);
x_906 = lean_int_mul(x_843, x_801);
lean_dec(x_843);
lean_inc_ref(x_835);
x_907 = l_Int_Linear_Poly_mul(x_835, x_906);
lean_dec(x_906);
x_908 = lean_int_mul(x_801, x_833);
lean_dec(x_801);
x_909 = l_Int_Linear_Poly_combine(x_905, x_907);
lean_inc(x_841);
if (lean_is_scalar(x_836)) {
 x_910 = lean_alloc_ctor(1, 3, 0);
} else {
 x_910 = x_836;
}
lean_ctor_set(x_910, 0, x_841);
lean_ctor_set(x_910, 1, x_795);
lean_ctor_set(x_910, 2, x_909);
lean_inc(x_830);
lean_inc_ref(x_805);
if (lean_is_scalar(x_903)) {
 x_911 = lean_alloc_ctor(4, 2, 0);
} else {
 x_911 = x_903;
 lean_ctor_set_tag(x_911, 4);
}
lean_ctor_set(x_911, 0, x_805);
lean_ctor_set(x_911, 1, x_830);
x_912 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_912, 0, x_908);
lean_ctor_set(x_912, 1, x_910);
lean_ctor_set(x_912, 2, x_911);
lean_inc(x_808);
lean_inc_ref(x_802);
lean_inc(x_806);
lean_inc_ref(x_807);
lean_inc(x_800);
lean_inc_ref(x_803);
lean_inc(x_804);
lean_inc(x_799);
x_913 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_912, x_799, x_804, x_803, x_800, x_807, x_806, x_802, x_808, x_902);
if (lean_obj_tag(x_913) == 0)
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_914 = lean_ctor_get(x_913, 1);
lean_inc(x_914);
if (lean_is_exclusive(x_913)) {
 lean_ctor_release(x_913, 0);
 lean_ctor_release(x_913, 1);
 x_915 = x_913;
} else {
 lean_dec_ref(x_913);
 x_915 = lean_box(0);
}
x_916 = l_Int_Linear_Poly_mul(x_797, x_834);
lean_dec(x_834);
x_917 = lean_int_neg(x_798);
lean_dec(x_798);
x_918 = l_Int_Linear_Poly_mul(x_835, x_917);
lean_dec(x_917);
x_919 = l_Int_Linear_Poly_combine(x_916, x_918);
lean_inc(x_830);
if (lean_is_scalar(x_915)) {
 x_920 = lean_alloc_ctor(5, 2, 0);
} else {
 x_920 = x_915;
 lean_ctor_set_tag(x_920, 5);
}
lean_ctor_set(x_920, 0, x_805);
lean_ctor_set(x_920, 1, x_830);
if (lean_is_exclusive(x_830)) {
 lean_ctor_release(x_830, 0);
 lean_ctor_release(x_830, 1);
 lean_ctor_release(x_830, 2);
 x_921 = x_830;
} else {
 lean_dec_ref(x_830);
 x_921 = lean_box(0);
}
if (lean_is_scalar(x_921)) {
 x_922 = lean_alloc_ctor(0, 3, 0);
} else {
 x_922 = x_921;
}
lean_ctor_set(x_922, 0, x_841);
lean_ctor_set(x_922, 1, x_919);
lean_ctor_set(x_922, 2, x_920);
x_1 = x_922;
x_2 = x_799;
x_3 = x_804;
x_4 = x_803;
x_5 = x_800;
x_6 = x_807;
x_7 = x_806;
x_8 = x_802;
x_9 = x_808;
x_10 = x_914;
goto _start;
}
else
{
lean_dec(x_841);
lean_dec_ref(x_835);
lean_dec(x_834);
lean_dec(x_830);
lean_dec(x_808);
lean_dec_ref(x_807);
lean_dec(x_806);
lean_dec_ref(x_805);
lean_dec(x_804);
lean_dec_ref(x_803);
lean_dec_ref(x_802);
lean_dec(x_800);
lean_dec(x_799);
lean_dec(x_798);
lean_dec_ref(x_797);
return x_913;
}
}
}
}
block_958:
{
lean_object* x_946; 
x_946 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_937, x_945);
if (lean_obj_tag(x_946) == 0)
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; uint8_t x_951; 
x_947 = lean_ctor_get(x_946, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_947, 6);
lean_inc_ref(x_948);
lean_dec(x_947);
x_949 = lean_ctor_get(x_946, 1);
lean_inc(x_949);
lean_dec_ref(x_946);
x_950 = lean_ctor_get(x_948, 2);
x_951 = lean_nat_dec_lt(x_931, x_950);
if (x_951 == 0)
{
lean_object* x_952; 
lean_dec_ref(x_948);
x_952 = l_outOfBounds___redArg(x_930);
x_795 = x_931;
x_796 = x_934;
x_797 = x_935;
x_798 = x_936;
x_799 = x_937;
x_800 = x_940;
x_801 = x_932;
x_802 = x_943;
x_803 = x_939;
x_804 = x_938;
x_805 = x_933;
x_806 = x_942;
x_807 = x_941;
x_808 = x_944;
x_809 = x_949;
x_810 = x_952;
goto block_924;
}
else
{
lean_object* x_953; 
x_953 = l_Lean_PersistentArray_get_x21___redArg(x_930, x_948, x_931);
x_795 = x_931;
x_796 = x_934;
x_797 = x_935;
x_798 = x_936;
x_799 = x_937;
x_800 = x_940;
x_801 = x_932;
x_802 = x_943;
x_803 = x_939;
x_804 = x_938;
x_805 = x_933;
x_806 = x_942;
x_807 = x_941;
x_808 = x_944;
x_809 = x_949;
x_810 = x_953;
goto block_924;
}
}
else
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; 
lean_dec(x_944);
lean_dec_ref(x_943);
lean_dec(x_942);
lean_dec_ref(x_941);
lean_dec(x_940);
lean_dec_ref(x_939);
lean_dec(x_938);
lean_dec(x_937);
lean_dec(x_936);
lean_dec_ref(x_935);
lean_dec_ref(x_934);
lean_dec_ref(x_933);
lean_dec(x_932);
lean_dec(x_931);
x_954 = lean_ctor_get(x_946, 0);
lean_inc(x_954);
x_955 = lean_ctor_get(x_946, 1);
lean_inc(x_955);
if (lean_is_exclusive(x_946)) {
 lean_ctor_release(x_946, 0);
 lean_ctor_release(x_946, 1);
 x_956 = x_946;
} else {
 lean_dec_ref(x_946);
 x_956 = lean_box(0);
}
if (lean_is_scalar(x_956)) {
 x_957 = lean_alloc_ctor(1, 2, 0);
} else {
 x_957 = x_956;
}
lean_ctor_set(x_957, 0, x_954);
lean_ctor_set(x_957, 1, x_955);
return x_957;
}
}
block_1034:
{
lean_object* x_968; lean_object* x_969; 
x_968 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_965);
x_969 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_968, x_959, x_960, x_961, x_962, x_963, x_964, x_965, x_966, x_967);
if (lean_obj_tag(x_969) == 0)
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; uint8_t x_974; 
x_970 = lean_ctor_get(x_969, 0);
lean_inc(x_970);
x_971 = lean_ctor_get(x_969, 1);
lean_inc(x_971);
lean_dec_ref(x_969);
x_972 = lean_ctor_get(x_970, 0);
x_973 = lean_ctor_get(x_970, 1);
lean_inc(x_972);
x_974 = l_Int_Linear_Poly_isUnsatDvd(x_972, x_973);
if (x_974 == 0)
{
uint8_t x_975; 
x_975 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_970);
if (x_975 == 0)
{
lean_dec(x_929);
if (lean_obj_tag(x_973) == 0)
{
lean_object* x_976; 
x_976 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_970, x_959, x_960, x_961, x_962, x_963, x_964, x_965, x_966, x_971);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec_ref(x_963);
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec(x_959);
return x_976;
}
else
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
lean_inc_ref(x_973);
lean_inc(x_972);
x_977 = lean_ctor_get(x_973, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_973, 1);
lean_inc(x_978);
x_979 = lean_ctor_get(x_973, 2);
lean_inc_ref(x_979);
lean_inc(x_970);
x_980 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_970, x_959, x_971);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; lean_object* x_982; uint8_t x_983; uint8_t x_984; uint8_t x_985; 
x_981 = lean_ctor_get(x_980, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_980, 1);
lean_inc(x_982);
lean_dec_ref(x_980);
x_983 = 0;
x_984 = lean_unbox(x_981);
lean_dec(x_981);
x_985 = l_Lean_beqLBool____x40_Lean_Data_LBool_27903016____hygCtx___hyg_13_(x_984, x_983);
if (x_985 == 0)
{
x_931 = x_978;
x_932 = x_972;
x_933 = x_970;
x_934 = x_973;
x_935 = x_979;
x_936 = x_977;
x_937 = x_959;
x_938 = x_960;
x_939 = x_961;
x_940 = x_962;
x_941 = x_963;
x_942 = x_964;
x_943 = x_965;
x_944 = x_966;
x_945 = x_982;
goto block_958;
}
else
{
lean_object* x_986; 
x_986 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_978, x_959, x_982);
if (lean_obj_tag(x_986) == 0)
{
lean_object* x_987; 
x_987 = lean_ctor_get(x_986, 1);
lean_inc(x_987);
lean_dec_ref(x_986);
x_931 = x_978;
x_932 = x_972;
x_933 = x_970;
x_934 = x_973;
x_935 = x_979;
x_936 = x_977;
x_937 = x_959;
x_938 = x_960;
x_939 = x_961;
x_940 = x_962;
x_941 = x_963;
x_942 = x_964;
x_943 = x_965;
x_944 = x_966;
x_945 = x_987;
goto block_958;
}
else
{
lean_dec_ref(x_979);
lean_dec(x_978);
lean_dec(x_977);
lean_dec_ref(x_973);
lean_dec(x_972);
lean_dec(x_970);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec_ref(x_963);
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec(x_959);
return x_986;
}
}
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; 
lean_dec_ref(x_979);
lean_dec(x_978);
lean_dec(x_977);
lean_dec_ref(x_973);
lean_dec(x_972);
lean_dec(x_970);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec_ref(x_963);
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec(x_959);
x_988 = lean_ctor_get(x_980, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_980, 1);
lean_inc(x_989);
if (lean_is_exclusive(x_980)) {
 lean_ctor_release(x_980, 0);
 lean_ctor_release(x_980, 1);
 x_990 = x_980;
} else {
 lean_dec_ref(x_980);
 x_990 = lean_box(0);
}
if (lean_is_scalar(x_990)) {
 x_991 = lean_alloc_ctor(1, 2, 0);
} else {
 x_991 = x_990;
}
lean_ctor_set(x_991, 0, x_988);
lean_ctor_set(x_991, 1, x_989);
return x_991;
}
}
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; uint8_t x_995; 
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
x_992 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_993 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_992, x_965, x_971);
x_994 = lean_ctor_get(x_993, 0);
lean_inc(x_994);
x_995 = lean_unbox(x_994);
lean_dec(x_994);
if (x_995 == 0)
{
lean_object* x_996; 
lean_dec(x_970);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec_ref(x_963);
lean_dec(x_959);
lean_dec(x_929);
x_996 = lean_ctor_get(x_993, 1);
lean_inc(x_996);
lean_dec_ref(x_993);
x_187 = x_996;
goto block_190;
}
else
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; 
x_997 = lean_ctor_get(x_993, 1);
lean_inc(x_997);
if (lean_is_exclusive(x_993)) {
 lean_ctor_release(x_993, 0);
 lean_ctor_release(x_993, 1);
 x_998 = x_993;
} else {
 lean_dec_ref(x_993);
 x_998 = lean_box(0);
}
x_999 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_970, x_959, x_997);
lean_dec(x_959);
if (lean_obj_tag(x_999) == 0)
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
x_1000 = lean_ctor_get(x_999, 0);
lean_inc(x_1000);
x_1001 = lean_ctor_get(x_999, 1);
lean_inc(x_1001);
lean_dec_ref(x_999);
x_1002 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_998)) {
 x_1003 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1003 = x_998;
 lean_ctor_set_tag(x_1003, 7);
}
lean_ctor_set(x_1003, 0, x_1002);
lean_ctor_set(x_1003, 1, x_1000);
if (lean_is_scalar(x_929)) {
 x_1004 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1004 = x_929;
 lean_ctor_set_tag(x_1004, 7);
}
lean_ctor_set(x_1004, 0, x_1003);
lean_ctor_set(x_1004, 1, x_1002);
x_1005 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_992, x_1004, x_963, x_964, x_965, x_966, x_1001);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec_ref(x_963);
x_1006 = lean_ctor_get(x_1005, 1);
lean_inc(x_1006);
lean_dec_ref(x_1005);
x_187 = x_1006;
goto block_190;
}
else
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
lean_dec(x_998);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec_ref(x_963);
lean_dec(x_929);
x_1007 = lean_ctor_get(x_999, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_999, 1);
lean_inc(x_1008);
if (lean_is_exclusive(x_999)) {
 lean_ctor_release(x_999, 0);
 lean_ctor_release(x_999, 1);
 x_1009 = x_999;
} else {
 lean_dec_ref(x_999);
 x_1009 = lean_box(0);
}
if (lean_is_scalar(x_1009)) {
 x_1010 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1010 = x_1009;
}
lean_ctor_set(x_1010, 0, x_1007);
lean_ctor_set(x_1010, 1, x_1008);
return x_1010;
}
}
}
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; uint8_t x_1014; 
x_1011 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_1012 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_1011, x_965, x_971);
x_1013 = lean_ctor_get(x_1012, 0);
lean_inc(x_1013);
x_1014 = lean_unbox(x_1013);
lean_dec(x_1013);
if (x_1014 == 0)
{
lean_object* x_1015; 
lean_dec(x_929);
x_1015 = lean_ctor_get(x_1012, 1);
lean_inc(x_1015);
lean_dec_ref(x_1012);
x_168 = x_970;
x_169 = x_959;
x_170 = x_960;
x_171 = x_961;
x_172 = x_962;
x_173 = x_963;
x_174 = x_964;
x_175 = x_965;
x_176 = x_966;
x_177 = x_1015;
goto block_186;
}
else
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
x_1016 = lean_ctor_get(x_1012, 1);
lean_inc(x_1016);
if (lean_is_exclusive(x_1012)) {
 lean_ctor_release(x_1012, 0);
 lean_ctor_release(x_1012, 1);
 x_1017 = x_1012;
} else {
 lean_dec_ref(x_1012);
 x_1017 = lean_box(0);
}
lean_inc(x_970);
x_1018 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_970, x_959, x_1016);
if (lean_obj_tag(x_1018) == 0)
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
x_1019 = lean_ctor_get(x_1018, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_1018, 1);
lean_inc(x_1020);
lean_dec_ref(x_1018);
x_1021 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_1017)) {
 x_1022 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1022 = x_1017;
 lean_ctor_set_tag(x_1022, 7);
}
lean_ctor_set(x_1022, 0, x_1021);
lean_ctor_set(x_1022, 1, x_1019);
if (lean_is_scalar(x_929)) {
 x_1023 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1023 = x_929;
 lean_ctor_set_tag(x_1023, 7);
}
lean_ctor_set(x_1023, 0, x_1022);
lean_ctor_set(x_1023, 1, x_1021);
x_1024 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_1011, x_1023, x_963, x_964, x_965, x_966, x_1020);
x_1025 = lean_ctor_get(x_1024, 1);
lean_inc(x_1025);
lean_dec_ref(x_1024);
x_168 = x_970;
x_169 = x_959;
x_170 = x_960;
x_171 = x_961;
x_172 = x_962;
x_173 = x_963;
x_174 = x_964;
x_175 = x_965;
x_176 = x_966;
x_177 = x_1025;
goto block_186;
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
lean_dec(x_1017);
lean_dec(x_970);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec_ref(x_963);
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec(x_959);
lean_dec(x_929);
x_1026 = lean_ctor_get(x_1018, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1018, 1);
lean_inc(x_1027);
if (lean_is_exclusive(x_1018)) {
 lean_ctor_release(x_1018, 0);
 lean_ctor_release(x_1018, 1);
 x_1028 = x_1018;
} else {
 lean_dec_ref(x_1018);
 x_1028 = lean_box(0);
}
if (lean_is_scalar(x_1028)) {
 x_1029 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1029 = x_1028;
}
lean_ctor_set(x_1029, 0, x_1026);
lean_ctor_set(x_1029, 1, x_1027);
return x_1029;
}
}
}
}
else
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec_ref(x_963);
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec(x_959);
lean_dec(x_929);
x_1030 = lean_ctor_get(x_969, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_969, 1);
lean_inc(x_1031);
if (lean_is_exclusive(x_969)) {
 lean_ctor_release(x_969, 0);
 lean_ctor_release(x_969, 1);
 x_1032 = x_969;
} else {
 lean_dec_ref(x_969);
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
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec(x_782);
lean_dec(x_781);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
lean_dec_ref(x_772);
lean_dec_ref(x_771);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1048 = lean_ctor_get(x_788, 1);
lean_inc(x_1048);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 lean_ctor_release(x_788, 1);
 x_1049 = x_788;
} else {
 lean_dec_ref(x_788);
 x_1049 = lean_box(0);
}
x_1050 = lean_box(0);
if (lean_is_scalar(x_1049)) {
 x_1051 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1051 = x_1049;
}
lean_ctor_set(x_1051, 0, x_1050);
lean_ctor_set(x_1051, 1, x_1048);
return x_1051;
}
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec(x_782);
lean_dec(x_781);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
lean_dec_ref(x_772);
lean_dec_ref(x_771);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1052 = lean_ctor_get(x_788, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_788, 1);
lean_inc(x_1053);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 lean_ctor_release(x_788, 1);
 x_1054 = x_788;
} else {
 lean_dec_ref(x_788);
 x_1054 = lean_box(0);
}
if (lean_is_scalar(x_1054)) {
 x_1055 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1055 = x_1054;
}
lean_ctor_set(x_1055, 0, x_1052);
lean_ctor_set(x_1055, 1, x_1053);
return x_1055;
}
}
else
{
lean_object* x_1056; 
lean_dec_ref(x_786);
lean_dec(x_784);
lean_dec(x_782);
lean_dec(x_781);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
lean_dec_ref(x_772);
lean_dec_ref(x_771);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1056 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_776, x_10);
return x_1056;
}
}
block_167:
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
lean_ctor_set(x_33, 0, x_12);
x_34 = l_Lean_PersistentArray_set___redArg(x_32, x_11, x_33);
lean_dec(x_11);
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
lean_ctor_set(x_66, 0, x_12);
x_67 = l_Lean_PersistentArray_set___redArg(x_48, x_11, x_66);
lean_dec(x_11);
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
lean_ctor_set(x_102, 0, x_12);
x_103 = l_Lean_PersistentArray_set___redArg(x_83, x_11, x_102);
lean_dec(x_11);
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
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_111 = lean_ctor_get(x_23, 0);
x_112 = lean_ctor_get(x_23, 1);
x_113 = lean_ctor_get(x_23, 2);
x_114 = lean_ctor_get(x_23, 3);
x_115 = lean_ctor_get(x_23, 4);
x_116 = lean_ctor_get(x_23, 5);
x_117 = lean_ctor_get(x_23, 6);
x_118 = lean_ctor_get(x_23, 7);
x_119 = lean_ctor_get_uint8(x_23, sizeof(void*)*17);
x_120 = lean_ctor_get(x_23, 8);
x_121 = lean_ctor_get(x_23, 9);
x_122 = lean_ctor_get(x_23, 10);
x_123 = lean_ctor_get(x_23, 11);
x_124 = lean_ctor_get(x_23, 12);
x_125 = lean_ctor_get(x_23, 13);
x_126 = lean_ctor_get(x_23, 15);
x_127 = lean_ctor_get(x_23, 16);
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
x_128 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_24, 3);
lean_inc_ref(x_130);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 x_131 = x_24;
} else {
 lean_dec_ref(x_24);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_25, 4);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_25, 5);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_25, 6);
lean_inc_ref(x_138);
x_139 = lean_ctor_get(x_25, 7);
lean_inc_ref(x_139);
x_140 = lean_ctor_get(x_25, 8);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_25, 9);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_25, 10);
lean_inc_ref(x_142);
x_143 = lean_ctor_get(x_25, 11);
lean_inc(x_143);
x_144 = lean_ctor_get(x_25, 12);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_25, 13);
lean_inc_ref(x_145);
x_146 = lean_ctor_get(x_25, 14);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_25, sizeof(void*)*22);
x_148 = lean_ctor_get(x_25, 15);
lean_inc(x_148);
x_149 = lean_ctor_get(x_25, 16);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_25, 17);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_25, 18);
lean_inc_ref(x_151);
x_152 = lean_ctor_get(x_25, 19);
lean_inc_ref(x_152);
x_153 = lean_ctor_get(x_25, 20);
lean_inc_ref(x_153);
x_154 = lean_ctor_get_uint8(x_25, sizeof(void*)*22 + 1);
x_155 = lean_ctor_get(x_25, 21);
lean_inc_ref(x_155);
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
 x_156 = x_25;
} else {
 lean_dec_ref(x_25);
 x_156 = lean_box(0);
}
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_12);
x_158 = l_Lean_PersistentArray_set___redArg(x_138, x_11, x_157);
lean_dec(x_11);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(0, 22, 2);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_132);
lean_ctor_set(x_159, 1, x_133);
lean_ctor_set(x_159, 2, x_134);
lean_ctor_set(x_159, 3, x_135);
lean_ctor_set(x_159, 4, x_136);
lean_ctor_set(x_159, 5, x_137);
lean_ctor_set(x_159, 6, x_158);
lean_ctor_set(x_159, 7, x_139);
lean_ctor_set(x_159, 8, x_140);
lean_ctor_set(x_159, 9, x_141);
lean_ctor_set(x_159, 10, x_142);
lean_ctor_set(x_159, 11, x_143);
lean_ctor_set(x_159, 12, x_144);
lean_ctor_set(x_159, 13, x_145);
lean_ctor_set(x_159, 14, x_146);
lean_ctor_set(x_159, 15, x_148);
lean_ctor_set(x_159, 16, x_149);
lean_ctor_set(x_159, 17, x_150);
lean_ctor_set(x_159, 18, x_151);
lean_ctor_set(x_159, 19, x_152);
lean_ctor_set(x_159, 20, x_153);
lean_ctor_set(x_159, 21, x_155);
lean_ctor_set_uint8(x_159, sizeof(void*)*22, x_147);
lean_ctor_set_uint8(x_159, sizeof(void*)*22 + 1, x_154);
if (lean_is_scalar(x_131)) {
 x_160 = lean_alloc_ctor(0, 4, 0);
} else {
 x_160 = x_131;
}
lean_ctor_set(x_160, 0, x_128);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set(x_160, 2, x_129);
lean_ctor_set(x_160, 3, x_130);
x_161 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_161, 0, x_111);
lean_ctor_set(x_161, 1, x_112);
lean_ctor_set(x_161, 2, x_113);
lean_ctor_set(x_161, 3, x_114);
lean_ctor_set(x_161, 4, x_115);
lean_ctor_set(x_161, 5, x_116);
lean_ctor_set(x_161, 6, x_117);
lean_ctor_set(x_161, 7, x_118);
lean_ctor_set(x_161, 8, x_120);
lean_ctor_set(x_161, 9, x_121);
lean_ctor_set(x_161, 10, x_122);
lean_ctor_set(x_161, 11, x_123);
lean_ctor_set(x_161, 12, x_124);
lean_ctor_set(x_161, 13, x_125);
lean_ctor_set(x_161, 14, x_160);
lean_ctor_set(x_161, 15, x_126);
lean_ctor_set(x_161, 16, x_127);
lean_ctor_set_uint8(x_161, sizeof(void*)*17, x_119);
x_162 = lean_st_ref_set(x_14, x_161, x_26);
lean_dec(x_14);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
x_165 = lean_box(0);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_12);
lean_dec(x_11);
return x_20;
}
}
block_186:
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_168);
x_179 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_178, x_169, x_170, x_171, x_172, x_173, x_174, x_175, x_176, x_177);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_179, 0);
lean_dec(x_181);
x_182 = lean_box(0);
lean_ctor_set(x_179, 0, x_182);
return x_179;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_179, 1);
lean_inc(x_183);
lean_dec(x_179);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
return x_179;
}
}
block_190:
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_box(0);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
return x_189;
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
x_50 = lean_ctor_get_uint8(x_49, sizeof(void*)*7 + 11);
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
x_47 = lean_ctor_get_uint8(x_46, sizeof(void*)*7 + 11);
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
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 19);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin, lean_object*);
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

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
extern lean_object* l_Lean_reflBoolTrue;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2963_(lean_object*);
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
uint8_t l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_20_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(x_32);
x_33 = l_Int_Linear_Poly_isSorted(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
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
x_23 = x_1;
x_24 = x_31;
x_25 = x_32;
goto block_30;
}
block_11:
{
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_int_ediv(x_2, x_5);
lean_dec(x_2);
x_8 = l_Int_Linear_Poly_div(x_5, x_3);
lean_dec(x_5);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_4);
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
x_17 = l_Int_Linear_Poly_getConst(x_13);
x_18 = lean_int_emod(x_17, x_16);
lean_dec(x_17);
x_19 = lean_int_dec_eq(x_18, x_15);
lean_dec(x_15);
lean_dec(x_18);
if (x_19 == 0)
{
x_2 = x_12;
x_3 = x_13;
x_4 = x_14;
x_5 = x_16;
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
x_2 = x_12;
x_3 = x_13;
x_4 = x_14;
x_5 = x_16;
x_6 = x_19;
goto block_11;
}
else
{
lean_dec(x_16);
lean_dec_ref(x_13);
lean_dec(x_12);
return x_14;
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
x_12 = x_24;
x_13 = x_25;
x_14 = x_23;
x_15 = x_27;
x_16 = x_26;
goto block_22;
}
else
{
lean_object* x_29; 
x_29 = lean_int_neg(x_26);
lean_dec(x_26);
x_12 = x_24;
x_13 = x_25;
x_14 = x_23;
x_15 = x_27;
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
x_5 = lean_ctor_get(x_2, 12);
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
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_5, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_22);
x_23 = lean_int_mul(x_1, x_21);
lean_dec(x_21);
x_24 = lean_nat_abs(x_23);
lean_dec(x_23);
x_25 = lean_nat_to_int(x_24);
x_26 = l_Int_Linear_Poly_mul(x_22, x_1);
x_27 = lean_int_neg(x_4);
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
x_1 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
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
x_25 = lean_nat_dec_eq(x_15, x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_26);
x_27 = l_Int_Linear_Poly_findVarToSubst___redArg(x_26, x_2, x_10);
lean_dec_ref(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_free_object(x_8);
lean_dec_ref(x_24);
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
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec_ref(x_28);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec_ref(x_27);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_ctor_get(x_35, 0);
lean_inc_ref(x_39);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_15, x_40);
lean_dec(x_15);
lean_ctor_set(x_8, 3, x_41);
x_42 = l_Int_Linear_Poly_coeff(x_39, x_38);
lean_dec_ref(x_39);
x_43 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_42, x_38, x_35, x_37, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_37);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_1 = x_44;
x_10 = x_45;
goto _start;
}
else
{
lean_dec_ref(x_8);
return x_43;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_8);
lean_dec_ref(x_24);
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
x_47 = !lean_is_exclusive(x_27);
if (x_47 == 0)
{
return x_27;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_27, 0);
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_27);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_free_object(x_8);
lean_dec_ref(x_24);
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
x_51 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_17, x_10);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; uint8_t x_67; 
x_52 = lean_ctor_get(x_8, 0);
x_53 = lean_ctor_get(x_8, 1);
x_54 = lean_ctor_get(x_8, 2);
x_55 = lean_ctor_get(x_8, 3);
x_56 = lean_ctor_get(x_8, 4);
x_57 = lean_ctor_get(x_8, 5);
x_58 = lean_ctor_get(x_8, 6);
x_59 = lean_ctor_get(x_8, 7);
x_60 = lean_ctor_get(x_8, 8);
x_61 = lean_ctor_get(x_8, 9);
x_62 = lean_ctor_get(x_8, 10);
x_63 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_64 = lean_ctor_get(x_8, 11);
x_65 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_66 = lean_ctor_get(x_8, 12);
lean_inc(x_66);
lean_inc(x_64);
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
lean_dec(x_8);
x_67 = lean_nat_dec_eq(x_55, x_56);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_68);
x_69 = l_Int_Linear_Poly_findVarToSubst___redArg(x_68, x_2, x_10);
lean_dec_ref(x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_66);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec_ref(x_70);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_dec_ref(x_69);
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_ctor_get(x_76, 0);
lean_inc_ref(x_80);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_add(x_55, x_81);
lean_dec(x_55);
x_83 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_83, 0, x_52);
lean_ctor_set(x_83, 1, x_53);
lean_ctor_set(x_83, 2, x_54);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_83, 4, x_56);
lean_ctor_set(x_83, 5, x_57);
lean_ctor_set(x_83, 6, x_58);
lean_ctor_set(x_83, 7, x_59);
lean_ctor_set(x_83, 8, x_60);
lean_ctor_set(x_83, 9, x_61);
lean_ctor_set(x_83, 10, x_62);
lean_ctor_set(x_83, 11, x_64);
lean_ctor_set(x_83, 12, x_66);
lean_ctor_set_uint8(x_83, sizeof(void*)*13, x_63);
lean_ctor_set_uint8(x_83, sizeof(void*)*13 + 1, x_65);
x_84 = l_Int_Linear_Poly_coeff(x_80, x_79);
lean_dec_ref(x_80);
x_85 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_84, x_79, x_76, x_78, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_83, x_9, x_77);
lean_dec(x_78);
lean_dec(x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_1 = x_86;
x_8 = x_83;
x_10 = x_87;
goto _start;
}
else
{
lean_dec_ref(x_83);
return x_85;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_66);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_1);
x_89 = lean_ctor_get(x_69, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_69, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_91 = x_69;
} else {
 lean_dec_ref(x_69);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; 
lean_dec_ref(x_66);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_1);
x_93 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_57, x_10);
return x_93;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_183; uint8_t x_187; 
x_187 = !lean_is_exclusive(x_8);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_188 = lean_ctor_get(x_8, 0);
x_189 = lean_ctor_get(x_8, 1);
x_190 = lean_ctor_get(x_8, 2);
x_191 = lean_ctor_get(x_8, 3);
x_192 = lean_ctor_get(x_8, 4);
x_193 = lean_ctor_get(x_8, 5);
x_194 = lean_ctor_get(x_8, 6);
x_195 = lean_ctor_get(x_8, 7);
x_196 = lean_ctor_get(x_8, 8);
x_197 = lean_ctor_get(x_8, 9);
x_198 = lean_ctor_get(x_8, 10);
x_199 = lean_ctor_get(x_8, 11);
x_200 = lean_ctor_get(x_8, 12);
x_201 = lean_nat_dec_eq(x_191, x_192);
if (x_201 == 0)
{
lean_object* x_202; 
x_202 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_unbox(x_203);
lean_dec(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; uint8_t x_735; 
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec_ref(x_202);
x_206 = lean_unsigned_to_nat(1u);
x_207 = lean_nat_add(x_191, x_206);
lean_dec(x_191);
lean_ctor_set(x_8, 3, x_207);
x_599 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_600 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_599, x_8, x_205);
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_600)) {
 lean_ctor_release(x_600, 0);
 lean_ctor_release(x_600, 1);
 x_603 = x_600;
} else {
 lean_dec_ref(x_600);
 x_603 = lean_box(0);
}
x_604 = lean_box(0);
x_735 = lean_unbox(x_601);
lean_dec(x_601);
if (x_735 == 0)
{
x_633 = x_2;
x_634 = x_3;
x_635 = x_4;
x_636 = x_5;
x_637 = x_6;
x_638 = x_7;
x_639 = x_8;
x_640 = x_9;
x_641 = x_602;
goto block_734;
}
else
{
lean_object* x_736; 
lean_inc_ref(x_1);
x_736 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_602);
if (lean_obj_tag(x_736) == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_737 = lean_ctor_get(x_736, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_736, 1);
lean_inc(x_738);
lean_dec_ref(x_736);
x_739 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_740 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_740, 0, x_739);
lean_ctor_set(x_740, 1, x_737);
x_741 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_741, 0, x_740);
lean_ctor_set(x_741, 1, x_739);
x_742 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_599, x_741, x_6, x_7, x_8, x_9, x_738);
x_743 = lean_ctor_get(x_742, 1);
lean_inc(x_743);
lean_dec_ref(x_742);
x_633 = x_2;
x_634 = x_3;
x_635 = x_4;
x_636 = x_5;
x_637 = x_6;
x_638 = x_7;
x_639 = x_8;
x_640 = x_9;
x_641 = x_743;
goto block_734;
}
else
{
uint8_t x_744; 
lean_dec(x_603);
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_744 = !lean_is_exclusive(x_736);
if (x_744 == 0)
{
return x_736;
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_745 = lean_ctor_get(x_736, 0);
x_746 = lean_ctor_get(x_736, 1);
lean_inc(x_746);
lean_inc(x_745);
lean_dec(x_736);
x_747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_747, 0, x_745);
lean_ctor_set(x_747, 1, x_746);
return x_747;
}
}
}
block_598:
{
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
lean_dec_ref(x_222);
lean_dec(x_218);
lean_dec(x_216);
lean_dec(x_213);
lean_dec_ref(x_211);
lean_dec(x_210);
x_224 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_225 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_224, x_217, x_212);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_unbox(x_226);
lean_dec(x_226);
if (x_227 == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_225, 1);
lean_inc(x_228);
lean_dec_ref(x_225);
x_11 = x_208;
x_12 = x_219;
x_13 = x_221;
x_14 = x_215;
x_15 = x_209;
x_16 = x_220;
x_17 = x_217;
x_18 = x_214;
x_19 = x_228;
goto block_163;
}
else
{
uint8_t x_229; 
x_229 = !lean_is_exclusive(x_225);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_225, 1);
x_231 = lean_ctor_get(x_225, 0);
lean_dec(x_231);
lean_inc_ref(x_219);
x_232 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_219, x_215, x_230);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec_ref(x_232);
x_235 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_225, 7);
lean_ctor_set(x_225, 1, x_233);
lean_ctor_set(x_225, 0, x_235);
x_236 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_236, 0, x_225);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_224, x_236, x_209, x_220, x_217, x_214, x_234);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec_ref(x_237);
x_11 = x_208;
x_12 = x_219;
x_13 = x_221;
x_14 = x_215;
x_15 = x_209;
x_16 = x_220;
x_17 = x_217;
x_18 = x_214;
x_19 = x_238;
goto block_163;
}
else
{
uint8_t x_239; 
lean_free_object(x_225);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_217);
lean_dec(x_215);
lean_dec(x_214);
lean_dec_ref(x_209);
lean_dec_ref(x_208);
x_239 = !lean_is_exclusive(x_232);
if (x_239 == 0)
{
return x_232;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_232, 0);
x_241 = lean_ctor_get(x_232, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_232);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_225, 1);
lean_inc(x_243);
lean_dec(x_225);
lean_inc_ref(x_219);
x_244 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_219, x_215, x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec_ref(x_244);
x_247 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_248 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_245);
x_249 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_224, x_249, x_209, x_220, x_217, x_214, x_246);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec_ref(x_250);
x_11 = x_208;
x_12 = x_219;
x_13 = x_221;
x_14 = x_215;
x_15 = x_209;
x_16 = x_220;
x_17 = x_217;
x_18 = x_214;
x_19 = x_251;
goto block_163;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_217);
lean_dec(x_215);
lean_dec(x_214);
lean_dec_ref(x_209);
lean_dec_ref(x_208);
x_252 = lean_ctor_get(x_244, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_244, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_254 = x_244;
} else {
 lean_dec_ref(x_244);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_dec_ref(x_208);
x_256 = lean_ctor_get(x_223, 0);
lean_inc(x_256);
lean_dec_ref(x_223);
x_257 = lean_ctor_get(x_256, 1);
lean_inc_ref(x_257);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; 
lean_dec_ref(x_257);
lean_dec(x_221);
lean_dec_ref(x_219);
lean_dec(x_216);
lean_dec_ref(x_211);
lean_dec(x_210);
x_258 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_256, x_215, x_213, x_222, x_218, x_209, x_220, x_217, x_214, x_212);
lean_dec(x_214);
lean_dec_ref(x_217);
lean_dec(x_220);
lean_dec_ref(x_209);
lean_dec(x_218);
lean_dec_ref(x_222);
lean_dec(x_213);
lean_dec(x_215);
return x_258;
}
else
{
lean_object* x_259; uint8_t x_260; 
x_259 = lean_ctor_get(x_256, 0);
lean_inc(x_259);
x_260 = !lean_is_exclusive(x_257);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_261 = lean_ctor_get(x_257, 0);
x_262 = lean_ctor_get(x_257, 2);
x_263 = lean_ctor_get(x_257, 1);
lean_dec(x_263);
x_264 = lean_int_mul(x_210, x_259);
x_265 = lean_int_mul(x_261, x_216);
x_266 = l_Lean_Meta_Grind_Arith_gcdExt(x_264, x_265);
lean_dec(x_265);
lean_dec(x_264);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 0);
lean_inc(x_268);
lean_dec_ref(x_266);
x_269 = lean_ctor_get(x_267, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
lean_dec(x_267);
x_271 = lean_st_ref_take(x_215, x_212);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_272, 14);
lean_inc_ref(x_273);
x_274 = lean_ctor_get(x_273, 1);
lean_inc_ref(x_274);
x_275 = lean_ctor_get(x_271, 1);
lean_inc(x_275);
lean_dec_ref(x_271);
x_276 = !lean_is_exclusive(x_272);
if (x_276 == 0)
{
lean_object* x_277; uint8_t x_278; 
x_277 = lean_ctor_get(x_272, 14);
lean_dec(x_277);
x_278 = !lean_is_exclusive(x_273);
if (x_278 == 0)
{
lean_object* x_279; uint8_t x_280; 
x_279 = lean_ctor_get(x_273, 1);
lean_dec(x_279);
x_280 = !lean_is_exclusive(x_274);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_281 = lean_ctor_get(x_274, 6);
x_282 = lean_box(0);
x_283 = l_Lean_PersistentArray_set___redArg(x_281, x_221, x_282);
lean_ctor_set(x_274, 6, x_283);
x_284 = lean_st_ref_set(x_215, x_272, x_275);
x_285 = !lean_is_exclusive(x_284);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_286 = lean_ctor_get(x_284, 1);
x_287 = lean_ctor_get(x_284, 0);
lean_dec(x_287);
x_288 = lean_int_mul(x_269, x_259);
lean_dec(x_269);
lean_inc_ref(x_211);
x_289 = l_Int_Linear_Poly_mul(x_211, x_288);
lean_dec(x_288);
x_290 = lean_int_mul(x_270, x_216);
lean_dec(x_270);
lean_inc_ref(x_262);
x_291 = l_Int_Linear_Poly_mul(x_262, x_290);
lean_dec(x_290);
x_292 = lean_int_mul(x_216, x_259);
lean_dec(x_259);
lean_dec(x_216);
x_293 = l_Int_Linear_Poly_combine(x_289, x_291);
lean_inc(x_268);
lean_ctor_set(x_257, 2, x_293);
lean_ctor_set(x_257, 1, x_221);
lean_ctor_set(x_257, 0, x_268);
lean_inc(x_256);
lean_inc_ref(x_219);
lean_ctor_set_tag(x_284, 4);
lean_ctor_set(x_284, 1, x_256);
lean_ctor_set(x_284, 0, x_219);
x_294 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_257);
lean_ctor_set(x_294, 2, x_284);
lean_inc(x_214);
lean_inc_ref(x_217);
lean_inc(x_220);
lean_inc_ref(x_209);
lean_inc(x_218);
lean_inc_ref(x_222);
lean_inc(x_213);
lean_inc(x_215);
x_295 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_294, x_215, x_213, x_222, x_218, x_209, x_220, x_217, x_214, x_286);
if (lean_obj_tag(x_295) == 0)
{
uint8_t x_296; 
x_296 = !lean_is_exclusive(x_295);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_297 = lean_ctor_get(x_295, 1);
x_298 = lean_ctor_get(x_295, 0);
lean_dec(x_298);
x_299 = l_Int_Linear_Poly_mul(x_211, x_261);
lean_dec(x_261);
x_300 = lean_int_neg(x_210);
lean_dec(x_210);
x_301 = l_Int_Linear_Poly_mul(x_262, x_300);
lean_dec(x_300);
x_302 = l_Int_Linear_Poly_combine(x_299, x_301);
lean_inc(x_256);
lean_ctor_set_tag(x_295, 5);
lean_ctor_set(x_295, 1, x_256);
lean_ctor_set(x_295, 0, x_219);
x_303 = !lean_is_exclusive(x_256);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_256, 2);
lean_dec(x_304);
x_305 = lean_ctor_get(x_256, 1);
lean_dec(x_305);
x_306 = lean_ctor_get(x_256, 0);
lean_dec(x_306);
lean_ctor_set(x_256, 2, x_295);
lean_ctor_set(x_256, 1, x_302);
lean_ctor_set(x_256, 0, x_268);
x_1 = x_256;
x_2 = x_215;
x_3 = x_213;
x_4 = x_222;
x_5 = x_218;
x_6 = x_209;
x_7 = x_220;
x_8 = x_217;
x_9 = x_214;
x_10 = x_297;
goto _start;
}
else
{
lean_object* x_308; 
lean_dec(x_256);
x_308 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_308, 0, x_268);
lean_ctor_set(x_308, 1, x_302);
lean_ctor_set(x_308, 2, x_295);
x_1 = x_308;
x_2 = x_215;
x_3 = x_213;
x_4 = x_222;
x_5 = x_218;
x_6 = x_209;
x_7 = x_220;
x_8 = x_217;
x_9 = x_214;
x_10 = x_297;
goto _start;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_310 = lean_ctor_get(x_295, 1);
lean_inc(x_310);
lean_dec(x_295);
x_311 = l_Int_Linear_Poly_mul(x_211, x_261);
lean_dec(x_261);
x_312 = lean_int_neg(x_210);
lean_dec(x_210);
x_313 = l_Int_Linear_Poly_mul(x_262, x_312);
lean_dec(x_312);
x_314 = l_Int_Linear_Poly_combine(x_311, x_313);
lean_inc(x_256);
x_315 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_315, 0, x_219);
lean_ctor_set(x_315, 1, x_256);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 x_316 = x_256;
} else {
 lean_dec_ref(x_256);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(0, 3, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_268);
lean_ctor_set(x_317, 1, x_314);
lean_ctor_set(x_317, 2, x_315);
x_1 = x_317;
x_2 = x_215;
x_3 = x_213;
x_4 = x_222;
x_5 = x_218;
x_6 = x_209;
x_7 = x_220;
x_8 = x_217;
x_9 = x_214;
x_10 = x_310;
goto _start;
}
}
else
{
lean_dec(x_268);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec(x_256);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec_ref(x_217);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
return x_295;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_319 = lean_ctor_get(x_284, 1);
lean_inc(x_319);
lean_dec(x_284);
x_320 = lean_int_mul(x_269, x_259);
lean_dec(x_269);
lean_inc_ref(x_211);
x_321 = l_Int_Linear_Poly_mul(x_211, x_320);
lean_dec(x_320);
x_322 = lean_int_mul(x_270, x_216);
lean_dec(x_270);
lean_inc_ref(x_262);
x_323 = l_Int_Linear_Poly_mul(x_262, x_322);
lean_dec(x_322);
x_324 = lean_int_mul(x_216, x_259);
lean_dec(x_259);
lean_dec(x_216);
x_325 = l_Int_Linear_Poly_combine(x_321, x_323);
lean_inc(x_268);
lean_ctor_set(x_257, 2, x_325);
lean_ctor_set(x_257, 1, x_221);
lean_ctor_set(x_257, 0, x_268);
lean_inc(x_256);
lean_inc_ref(x_219);
x_326 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_326, 0, x_219);
lean_ctor_set(x_326, 1, x_256);
x_327 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_257);
lean_ctor_set(x_327, 2, x_326);
lean_inc(x_214);
lean_inc_ref(x_217);
lean_inc(x_220);
lean_inc_ref(x_209);
lean_inc(x_218);
lean_inc_ref(x_222);
lean_inc(x_213);
lean_inc(x_215);
x_328 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_327, x_215, x_213, x_222, x_218, x_209, x_220, x_217, x_214, x_319);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_330 = x_328;
} else {
 lean_dec_ref(x_328);
 x_330 = lean_box(0);
}
x_331 = l_Int_Linear_Poly_mul(x_211, x_261);
lean_dec(x_261);
x_332 = lean_int_neg(x_210);
lean_dec(x_210);
x_333 = l_Int_Linear_Poly_mul(x_262, x_332);
lean_dec(x_332);
x_334 = l_Int_Linear_Poly_combine(x_331, x_333);
lean_inc(x_256);
if (lean_is_scalar(x_330)) {
 x_335 = lean_alloc_ctor(5, 2, 0);
} else {
 x_335 = x_330;
 lean_ctor_set_tag(x_335, 5);
}
lean_ctor_set(x_335, 0, x_219);
lean_ctor_set(x_335, 1, x_256);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 x_336 = x_256;
} else {
 lean_dec_ref(x_256);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(0, 3, 0);
} else {
 x_337 = x_336;
}
lean_ctor_set(x_337, 0, x_268);
lean_ctor_set(x_337, 1, x_334);
lean_ctor_set(x_337, 2, x_335);
x_1 = x_337;
x_2 = x_215;
x_3 = x_213;
x_4 = x_222;
x_5 = x_218;
x_6 = x_209;
x_7 = x_220;
x_8 = x_217;
x_9 = x_214;
x_10 = x_329;
goto _start;
}
else
{
lean_dec(x_268);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec(x_256);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec_ref(x_217);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
return x_328;
}
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_339 = lean_ctor_get(x_274, 0);
x_340 = lean_ctor_get(x_274, 1);
x_341 = lean_ctor_get(x_274, 2);
x_342 = lean_ctor_get(x_274, 3);
x_343 = lean_ctor_get(x_274, 4);
x_344 = lean_ctor_get(x_274, 5);
x_345 = lean_ctor_get(x_274, 6);
x_346 = lean_ctor_get(x_274, 7);
x_347 = lean_ctor_get(x_274, 8);
x_348 = lean_ctor_get(x_274, 9);
x_349 = lean_ctor_get(x_274, 10);
x_350 = lean_ctor_get(x_274, 11);
x_351 = lean_ctor_get(x_274, 12);
x_352 = lean_ctor_get(x_274, 13);
x_353 = lean_ctor_get(x_274, 14);
x_354 = lean_ctor_get_uint8(x_274, sizeof(void*)*21);
x_355 = lean_ctor_get(x_274, 15);
x_356 = lean_ctor_get(x_274, 16);
x_357 = lean_ctor_get(x_274, 17);
x_358 = lean_ctor_get(x_274, 18);
x_359 = lean_ctor_get(x_274, 19);
x_360 = lean_ctor_get(x_274, 20);
x_361 = lean_ctor_get_uint8(x_274, sizeof(void*)*21 + 1);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
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
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_274);
x_362 = lean_box(0);
x_363 = l_Lean_PersistentArray_set___redArg(x_345, x_221, x_362);
x_364 = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(x_364, 0, x_339);
lean_ctor_set(x_364, 1, x_340);
lean_ctor_set(x_364, 2, x_341);
lean_ctor_set(x_364, 3, x_342);
lean_ctor_set(x_364, 4, x_343);
lean_ctor_set(x_364, 5, x_344);
lean_ctor_set(x_364, 6, x_363);
lean_ctor_set(x_364, 7, x_346);
lean_ctor_set(x_364, 8, x_347);
lean_ctor_set(x_364, 9, x_348);
lean_ctor_set(x_364, 10, x_349);
lean_ctor_set(x_364, 11, x_350);
lean_ctor_set(x_364, 12, x_351);
lean_ctor_set(x_364, 13, x_352);
lean_ctor_set(x_364, 14, x_353);
lean_ctor_set(x_364, 15, x_355);
lean_ctor_set(x_364, 16, x_356);
lean_ctor_set(x_364, 17, x_357);
lean_ctor_set(x_364, 18, x_358);
lean_ctor_set(x_364, 19, x_359);
lean_ctor_set(x_364, 20, x_360);
lean_ctor_set_uint8(x_364, sizeof(void*)*21, x_354);
lean_ctor_set_uint8(x_364, sizeof(void*)*21 + 1, x_361);
lean_ctor_set(x_273, 1, x_364);
x_365 = lean_st_ref_set(x_215, x_272, x_275);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_367 = x_365;
} else {
 lean_dec_ref(x_365);
 x_367 = lean_box(0);
}
x_368 = lean_int_mul(x_269, x_259);
lean_dec(x_269);
lean_inc_ref(x_211);
x_369 = l_Int_Linear_Poly_mul(x_211, x_368);
lean_dec(x_368);
x_370 = lean_int_mul(x_270, x_216);
lean_dec(x_270);
lean_inc_ref(x_262);
x_371 = l_Int_Linear_Poly_mul(x_262, x_370);
lean_dec(x_370);
x_372 = lean_int_mul(x_216, x_259);
lean_dec(x_259);
lean_dec(x_216);
x_373 = l_Int_Linear_Poly_combine(x_369, x_371);
lean_inc(x_268);
lean_ctor_set(x_257, 2, x_373);
lean_ctor_set(x_257, 1, x_221);
lean_ctor_set(x_257, 0, x_268);
lean_inc(x_256);
lean_inc_ref(x_219);
if (lean_is_scalar(x_367)) {
 x_374 = lean_alloc_ctor(4, 2, 0);
} else {
 x_374 = x_367;
 lean_ctor_set_tag(x_374, 4);
}
lean_ctor_set(x_374, 0, x_219);
lean_ctor_set(x_374, 1, x_256);
x_375 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_257);
lean_ctor_set(x_375, 2, x_374);
lean_inc(x_214);
lean_inc_ref(x_217);
lean_inc(x_220);
lean_inc_ref(x_209);
lean_inc(x_218);
lean_inc_ref(x_222);
lean_inc(x_213);
lean_inc(x_215);
x_376 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_375, x_215, x_213, x_222, x_218, x_209, x_220, x_217, x_214, x_366);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_378 = x_376;
} else {
 lean_dec_ref(x_376);
 x_378 = lean_box(0);
}
x_379 = l_Int_Linear_Poly_mul(x_211, x_261);
lean_dec(x_261);
x_380 = lean_int_neg(x_210);
lean_dec(x_210);
x_381 = l_Int_Linear_Poly_mul(x_262, x_380);
lean_dec(x_380);
x_382 = l_Int_Linear_Poly_combine(x_379, x_381);
lean_inc(x_256);
if (lean_is_scalar(x_378)) {
 x_383 = lean_alloc_ctor(5, 2, 0);
} else {
 x_383 = x_378;
 lean_ctor_set_tag(x_383, 5);
}
lean_ctor_set(x_383, 0, x_219);
lean_ctor_set(x_383, 1, x_256);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 x_384 = x_256;
} else {
 lean_dec_ref(x_256);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(0, 3, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_268);
lean_ctor_set(x_385, 1, x_382);
lean_ctor_set(x_385, 2, x_383);
x_1 = x_385;
x_2 = x_215;
x_3 = x_213;
x_4 = x_222;
x_5 = x_218;
x_6 = x_209;
x_7 = x_220;
x_8 = x_217;
x_9 = x_214;
x_10 = x_377;
goto _start;
}
else
{
lean_dec(x_268);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec(x_256);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec_ref(x_217);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
return x_376;
}
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_387 = lean_ctor_get(x_273, 0);
x_388 = lean_ctor_get(x_273, 2);
x_389 = lean_ctor_get(x_273, 3);
lean_inc(x_389);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_273);
x_390 = lean_ctor_get(x_274, 0);
lean_inc_ref(x_390);
x_391 = lean_ctor_get(x_274, 1);
lean_inc_ref(x_391);
x_392 = lean_ctor_get(x_274, 2);
lean_inc_ref(x_392);
x_393 = lean_ctor_get(x_274, 3);
lean_inc_ref(x_393);
x_394 = lean_ctor_get(x_274, 4);
lean_inc_ref(x_394);
x_395 = lean_ctor_get(x_274, 5);
lean_inc_ref(x_395);
x_396 = lean_ctor_get(x_274, 6);
lean_inc_ref(x_396);
x_397 = lean_ctor_get(x_274, 7);
lean_inc_ref(x_397);
x_398 = lean_ctor_get(x_274, 8);
lean_inc_ref(x_398);
x_399 = lean_ctor_get(x_274, 9);
lean_inc_ref(x_399);
x_400 = lean_ctor_get(x_274, 10);
lean_inc_ref(x_400);
x_401 = lean_ctor_get(x_274, 11);
lean_inc(x_401);
x_402 = lean_ctor_get(x_274, 12);
lean_inc_ref(x_402);
x_403 = lean_ctor_get(x_274, 13);
lean_inc_ref(x_403);
x_404 = lean_ctor_get(x_274, 14);
lean_inc(x_404);
x_405 = lean_ctor_get_uint8(x_274, sizeof(void*)*21);
x_406 = lean_ctor_get(x_274, 15);
lean_inc(x_406);
x_407 = lean_ctor_get(x_274, 16);
lean_inc_ref(x_407);
x_408 = lean_ctor_get(x_274, 17);
lean_inc_ref(x_408);
x_409 = lean_ctor_get(x_274, 18);
lean_inc_ref(x_409);
x_410 = lean_ctor_get(x_274, 19);
lean_inc_ref(x_410);
x_411 = lean_ctor_get(x_274, 20);
lean_inc_ref(x_411);
x_412 = lean_ctor_get_uint8(x_274, sizeof(void*)*21 + 1);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 lean_ctor_release(x_274, 2);
 lean_ctor_release(x_274, 3);
 lean_ctor_release(x_274, 4);
 lean_ctor_release(x_274, 5);
 lean_ctor_release(x_274, 6);
 lean_ctor_release(x_274, 7);
 lean_ctor_release(x_274, 8);
 lean_ctor_release(x_274, 9);
 lean_ctor_release(x_274, 10);
 lean_ctor_release(x_274, 11);
 lean_ctor_release(x_274, 12);
 lean_ctor_release(x_274, 13);
 lean_ctor_release(x_274, 14);
 lean_ctor_release(x_274, 15);
 lean_ctor_release(x_274, 16);
 lean_ctor_release(x_274, 17);
 lean_ctor_release(x_274, 18);
 lean_ctor_release(x_274, 19);
 lean_ctor_release(x_274, 20);
 x_413 = x_274;
} else {
 lean_dec_ref(x_274);
 x_413 = lean_box(0);
}
x_414 = lean_box(0);
x_415 = l_Lean_PersistentArray_set___redArg(x_396, x_221, x_414);
if (lean_is_scalar(x_413)) {
 x_416 = lean_alloc_ctor(0, 21, 2);
} else {
 x_416 = x_413;
}
lean_ctor_set(x_416, 0, x_390);
lean_ctor_set(x_416, 1, x_391);
lean_ctor_set(x_416, 2, x_392);
lean_ctor_set(x_416, 3, x_393);
lean_ctor_set(x_416, 4, x_394);
lean_ctor_set(x_416, 5, x_395);
lean_ctor_set(x_416, 6, x_415);
lean_ctor_set(x_416, 7, x_397);
lean_ctor_set(x_416, 8, x_398);
lean_ctor_set(x_416, 9, x_399);
lean_ctor_set(x_416, 10, x_400);
lean_ctor_set(x_416, 11, x_401);
lean_ctor_set(x_416, 12, x_402);
lean_ctor_set(x_416, 13, x_403);
lean_ctor_set(x_416, 14, x_404);
lean_ctor_set(x_416, 15, x_406);
lean_ctor_set(x_416, 16, x_407);
lean_ctor_set(x_416, 17, x_408);
lean_ctor_set(x_416, 18, x_409);
lean_ctor_set(x_416, 19, x_410);
lean_ctor_set(x_416, 20, x_411);
lean_ctor_set_uint8(x_416, sizeof(void*)*21, x_405);
lean_ctor_set_uint8(x_416, sizeof(void*)*21 + 1, x_412);
x_417 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_417, 0, x_387);
lean_ctor_set(x_417, 1, x_416);
lean_ctor_set(x_417, 2, x_388);
lean_ctor_set(x_417, 3, x_389);
lean_ctor_set(x_272, 14, x_417);
x_418 = lean_st_ref_set(x_215, x_272, x_275);
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 x_420 = x_418;
} else {
 lean_dec_ref(x_418);
 x_420 = lean_box(0);
}
x_421 = lean_int_mul(x_269, x_259);
lean_dec(x_269);
lean_inc_ref(x_211);
x_422 = l_Int_Linear_Poly_mul(x_211, x_421);
lean_dec(x_421);
x_423 = lean_int_mul(x_270, x_216);
lean_dec(x_270);
lean_inc_ref(x_262);
x_424 = l_Int_Linear_Poly_mul(x_262, x_423);
lean_dec(x_423);
x_425 = lean_int_mul(x_216, x_259);
lean_dec(x_259);
lean_dec(x_216);
x_426 = l_Int_Linear_Poly_combine(x_422, x_424);
lean_inc(x_268);
lean_ctor_set(x_257, 2, x_426);
lean_ctor_set(x_257, 1, x_221);
lean_ctor_set(x_257, 0, x_268);
lean_inc(x_256);
lean_inc_ref(x_219);
if (lean_is_scalar(x_420)) {
 x_427 = lean_alloc_ctor(4, 2, 0);
} else {
 x_427 = x_420;
 lean_ctor_set_tag(x_427, 4);
}
lean_ctor_set(x_427, 0, x_219);
lean_ctor_set(x_427, 1, x_256);
x_428 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_428, 0, x_425);
lean_ctor_set(x_428, 1, x_257);
lean_ctor_set(x_428, 2, x_427);
lean_inc(x_214);
lean_inc_ref(x_217);
lean_inc(x_220);
lean_inc_ref(x_209);
lean_inc(x_218);
lean_inc_ref(x_222);
lean_inc(x_213);
lean_inc(x_215);
x_429 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_428, x_215, x_213, x_222, x_218, x_209, x_220, x_217, x_214, x_419);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_430 = lean_ctor_get(x_429, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 x_431 = x_429;
} else {
 lean_dec_ref(x_429);
 x_431 = lean_box(0);
}
x_432 = l_Int_Linear_Poly_mul(x_211, x_261);
lean_dec(x_261);
x_433 = lean_int_neg(x_210);
lean_dec(x_210);
x_434 = l_Int_Linear_Poly_mul(x_262, x_433);
lean_dec(x_433);
x_435 = l_Int_Linear_Poly_combine(x_432, x_434);
lean_inc(x_256);
if (lean_is_scalar(x_431)) {
 x_436 = lean_alloc_ctor(5, 2, 0);
} else {
 x_436 = x_431;
 lean_ctor_set_tag(x_436, 5);
}
lean_ctor_set(x_436, 0, x_219);
lean_ctor_set(x_436, 1, x_256);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 x_437 = x_256;
} else {
 lean_dec_ref(x_256);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(0, 3, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_268);
lean_ctor_set(x_438, 1, x_435);
lean_ctor_set(x_438, 2, x_436);
x_1 = x_438;
x_2 = x_215;
x_3 = x_213;
x_4 = x_222;
x_5 = x_218;
x_6 = x_209;
x_7 = x_220;
x_8 = x_217;
x_9 = x_214;
x_10 = x_430;
goto _start;
}
else
{
lean_dec(x_268);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec(x_256);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec_ref(x_217);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
return x_429;
}
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_440 = lean_ctor_get(x_272, 0);
x_441 = lean_ctor_get(x_272, 1);
x_442 = lean_ctor_get(x_272, 2);
x_443 = lean_ctor_get(x_272, 3);
x_444 = lean_ctor_get(x_272, 4);
x_445 = lean_ctor_get(x_272, 5);
x_446 = lean_ctor_get(x_272, 6);
x_447 = lean_ctor_get(x_272, 7);
x_448 = lean_ctor_get_uint8(x_272, sizeof(void*)*16);
x_449 = lean_ctor_get(x_272, 8);
x_450 = lean_ctor_get(x_272, 9);
x_451 = lean_ctor_get(x_272, 10);
x_452 = lean_ctor_get(x_272, 11);
x_453 = lean_ctor_get(x_272, 12);
x_454 = lean_ctor_get(x_272, 13);
x_455 = lean_ctor_get(x_272, 15);
lean_inc(x_455);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
lean_inc(x_449);
lean_inc(x_447);
lean_inc(x_446);
lean_inc(x_445);
lean_inc(x_444);
lean_inc(x_443);
lean_inc(x_442);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_272);
x_456 = lean_ctor_get(x_273, 0);
lean_inc_ref(x_456);
x_457 = lean_ctor_get(x_273, 2);
lean_inc_ref(x_457);
x_458 = lean_ctor_get(x_273, 3);
lean_inc_ref(x_458);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 lean_ctor_release(x_273, 2);
 lean_ctor_release(x_273, 3);
 x_459 = x_273;
} else {
 lean_dec_ref(x_273);
 x_459 = lean_box(0);
}
x_460 = lean_ctor_get(x_274, 0);
lean_inc_ref(x_460);
x_461 = lean_ctor_get(x_274, 1);
lean_inc_ref(x_461);
x_462 = lean_ctor_get(x_274, 2);
lean_inc_ref(x_462);
x_463 = lean_ctor_get(x_274, 3);
lean_inc_ref(x_463);
x_464 = lean_ctor_get(x_274, 4);
lean_inc_ref(x_464);
x_465 = lean_ctor_get(x_274, 5);
lean_inc_ref(x_465);
x_466 = lean_ctor_get(x_274, 6);
lean_inc_ref(x_466);
x_467 = lean_ctor_get(x_274, 7);
lean_inc_ref(x_467);
x_468 = lean_ctor_get(x_274, 8);
lean_inc_ref(x_468);
x_469 = lean_ctor_get(x_274, 9);
lean_inc_ref(x_469);
x_470 = lean_ctor_get(x_274, 10);
lean_inc_ref(x_470);
x_471 = lean_ctor_get(x_274, 11);
lean_inc(x_471);
x_472 = lean_ctor_get(x_274, 12);
lean_inc_ref(x_472);
x_473 = lean_ctor_get(x_274, 13);
lean_inc_ref(x_473);
x_474 = lean_ctor_get(x_274, 14);
lean_inc(x_474);
x_475 = lean_ctor_get_uint8(x_274, sizeof(void*)*21);
x_476 = lean_ctor_get(x_274, 15);
lean_inc(x_476);
x_477 = lean_ctor_get(x_274, 16);
lean_inc_ref(x_477);
x_478 = lean_ctor_get(x_274, 17);
lean_inc_ref(x_478);
x_479 = lean_ctor_get(x_274, 18);
lean_inc_ref(x_479);
x_480 = lean_ctor_get(x_274, 19);
lean_inc_ref(x_480);
x_481 = lean_ctor_get(x_274, 20);
lean_inc_ref(x_481);
x_482 = lean_ctor_get_uint8(x_274, sizeof(void*)*21 + 1);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 lean_ctor_release(x_274, 2);
 lean_ctor_release(x_274, 3);
 lean_ctor_release(x_274, 4);
 lean_ctor_release(x_274, 5);
 lean_ctor_release(x_274, 6);
 lean_ctor_release(x_274, 7);
 lean_ctor_release(x_274, 8);
 lean_ctor_release(x_274, 9);
 lean_ctor_release(x_274, 10);
 lean_ctor_release(x_274, 11);
 lean_ctor_release(x_274, 12);
 lean_ctor_release(x_274, 13);
 lean_ctor_release(x_274, 14);
 lean_ctor_release(x_274, 15);
 lean_ctor_release(x_274, 16);
 lean_ctor_release(x_274, 17);
 lean_ctor_release(x_274, 18);
 lean_ctor_release(x_274, 19);
 lean_ctor_release(x_274, 20);
 x_483 = x_274;
} else {
 lean_dec_ref(x_274);
 x_483 = lean_box(0);
}
x_484 = lean_box(0);
x_485 = l_Lean_PersistentArray_set___redArg(x_466, x_221, x_484);
if (lean_is_scalar(x_483)) {
 x_486 = lean_alloc_ctor(0, 21, 2);
} else {
 x_486 = x_483;
}
lean_ctor_set(x_486, 0, x_460);
lean_ctor_set(x_486, 1, x_461);
lean_ctor_set(x_486, 2, x_462);
lean_ctor_set(x_486, 3, x_463);
lean_ctor_set(x_486, 4, x_464);
lean_ctor_set(x_486, 5, x_465);
lean_ctor_set(x_486, 6, x_485);
lean_ctor_set(x_486, 7, x_467);
lean_ctor_set(x_486, 8, x_468);
lean_ctor_set(x_486, 9, x_469);
lean_ctor_set(x_486, 10, x_470);
lean_ctor_set(x_486, 11, x_471);
lean_ctor_set(x_486, 12, x_472);
lean_ctor_set(x_486, 13, x_473);
lean_ctor_set(x_486, 14, x_474);
lean_ctor_set(x_486, 15, x_476);
lean_ctor_set(x_486, 16, x_477);
lean_ctor_set(x_486, 17, x_478);
lean_ctor_set(x_486, 18, x_479);
lean_ctor_set(x_486, 19, x_480);
lean_ctor_set(x_486, 20, x_481);
lean_ctor_set_uint8(x_486, sizeof(void*)*21, x_475);
lean_ctor_set_uint8(x_486, sizeof(void*)*21 + 1, x_482);
if (lean_is_scalar(x_459)) {
 x_487 = lean_alloc_ctor(0, 4, 0);
} else {
 x_487 = x_459;
}
lean_ctor_set(x_487, 0, x_456);
lean_ctor_set(x_487, 1, x_486);
lean_ctor_set(x_487, 2, x_457);
lean_ctor_set(x_487, 3, x_458);
x_488 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_488, 0, x_440);
lean_ctor_set(x_488, 1, x_441);
lean_ctor_set(x_488, 2, x_442);
lean_ctor_set(x_488, 3, x_443);
lean_ctor_set(x_488, 4, x_444);
lean_ctor_set(x_488, 5, x_445);
lean_ctor_set(x_488, 6, x_446);
lean_ctor_set(x_488, 7, x_447);
lean_ctor_set(x_488, 8, x_449);
lean_ctor_set(x_488, 9, x_450);
lean_ctor_set(x_488, 10, x_451);
lean_ctor_set(x_488, 11, x_452);
lean_ctor_set(x_488, 12, x_453);
lean_ctor_set(x_488, 13, x_454);
lean_ctor_set(x_488, 14, x_487);
lean_ctor_set(x_488, 15, x_455);
lean_ctor_set_uint8(x_488, sizeof(void*)*16, x_448);
x_489 = lean_st_ref_set(x_215, x_488, x_275);
x_490 = lean_ctor_get(x_489, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 lean_ctor_release(x_489, 1);
 x_491 = x_489;
} else {
 lean_dec_ref(x_489);
 x_491 = lean_box(0);
}
x_492 = lean_int_mul(x_269, x_259);
lean_dec(x_269);
lean_inc_ref(x_211);
x_493 = l_Int_Linear_Poly_mul(x_211, x_492);
lean_dec(x_492);
x_494 = lean_int_mul(x_270, x_216);
lean_dec(x_270);
lean_inc_ref(x_262);
x_495 = l_Int_Linear_Poly_mul(x_262, x_494);
lean_dec(x_494);
x_496 = lean_int_mul(x_216, x_259);
lean_dec(x_259);
lean_dec(x_216);
x_497 = l_Int_Linear_Poly_combine(x_493, x_495);
lean_inc(x_268);
lean_ctor_set(x_257, 2, x_497);
lean_ctor_set(x_257, 1, x_221);
lean_ctor_set(x_257, 0, x_268);
lean_inc(x_256);
lean_inc_ref(x_219);
if (lean_is_scalar(x_491)) {
 x_498 = lean_alloc_ctor(4, 2, 0);
} else {
 x_498 = x_491;
 lean_ctor_set_tag(x_498, 4);
}
lean_ctor_set(x_498, 0, x_219);
lean_ctor_set(x_498, 1, x_256);
x_499 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_499, 0, x_496);
lean_ctor_set(x_499, 1, x_257);
lean_ctor_set(x_499, 2, x_498);
lean_inc(x_214);
lean_inc_ref(x_217);
lean_inc(x_220);
lean_inc_ref(x_209);
lean_inc(x_218);
lean_inc_ref(x_222);
lean_inc(x_213);
lean_inc(x_215);
x_500 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_499, x_215, x_213, x_222, x_218, x_209, x_220, x_217, x_214, x_490);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
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
x_503 = l_Int_Linear_Poly_mul(x_211, x_261);
lean_dec(x_261);
x_504 = lean_int_neg(x_210);
lean_dec(x_210);
x_505 = l_Int_Linear_Poly_mul(x_262, x_504);
lean_dec(x_504);
x_506 = l_Int_Linear_Poly_combine(x_503, x_505);
lean_inc(x_256);
if (lean_is_scalar(x_502)) {
 x_507 = lean_alloc_ctor(5, 2, 0);
} else {
 x_507 = x_502;
 lean_ctor_set_tag(x_507, 5);
}
lean_ctor_set(x_507, 0, x_219);
lean_ctor_set(x_507, 1, x_256);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 x_508 = x_256;
} else {
 lean_dec_ref(x_256);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_508)) {
 x_509 = lean_alloc_ctor(0, 3, 0);
} else {
 x_509 = x_508;
}
lean_ctor_set(x_509, 0, x_268);
lean_ctor_set(x_509, 1, x_506);
lean_ctor_set(x_509, 2, x_507);
x_1 = x_509;
x_2 = x_215;
x_3 = x_213;
x_4 = x_222;
x_5 = x_218;
x_6 = x_209;
x_7 = x_220;
x_8 = x_217;
x_9 = x_214;
x_10 = x_501;
goto _start;
}
else
{
lean_dec(x_268);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec(x_256);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec_ref(x_217);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
return x_500;
}
}
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; uint8_t x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; uint8_t x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; uint8_t x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_511 = lean_ctor_get(x_257, 0);
x_512 = lean_ctor_get(x_257, 2);
lean_inc(x_512);
lean_inc(x_511);
lean_dec(x_257);
x_513 = lean_int_mul(x_210, x_259);
x_514 = lean_int_mul(x_511, x_216);
x_515 = l_Lean_Meta_Grind_Arith_gcdExt(x_513, x_514);
lean_dec(x_514);
lean_dec(x_513);
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 0);
lean_inc(x_517);
lean_dec_ref(x_515);
x_518 = lean_ctor_get(x_516, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_516, 1);
lean_inc(x_519);
lean_dec(x_516);
x_520 = lean_st_ref_take(x_215, x_212);
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_521, 14);
lean_inc_ref(x_522);
x_523 = lean_ctor_get(x_522, 1);
lean_inc_ref(x_523);
x_524 = lean_ctor_get(x_520, 1);
lean_inc(x_524);
lean_dec_ref(x_520);
x_525 = lean_ctor_get(x_521, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_521, 1);
lean_inc_ref(x_526);
x_527 = lean_ctor_get(x_521, 2);
lean_inc(x_527);
x_528 = lean_ctor_get(x_521, 3);
lean_inc_ref(x_528);
x_529 = lean_ctor_get(x_521, 4);
lean_inc_ref(x_529);
x_530 = lean_ctor_get(x_521, 5);
lean_inc_ref(x_530);
x_531 = lean_ctor_get(x_521, 6);
lean_inc_ref(x_531);
x_532 = lean_ctor_get(x_521, 7);
lean_inc_ref(x_532);
x_533 = lean_ctor_get_uint8(x_521, sizeof(void*)*16);
x_534 = lean_ctor_get(x_521, 8);
lean_inc(x_534);
x_535 = lean_ctor_get(x_521, 9);
lean_inc_ref(x_535);
x_536 = lean_ctor_get(x_521, 10);
lean_inc_ref(x_536);
x_537 = lean_ctor_get(x_521, 11);
lean_inc_ref(x_537);
x_538 = lean_ctor_get(x_521, 12);
lean_inc_ref(x_538);
x_539 = lean_ctor_get(x_521, 13);
lean_inc_ref(x_539);
x_540 = lean_ctor_get(x_521, 15);
lean_inc_ref(x_540);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 lean_ctor_release(x_521, 2);
 lean_ctor_release(x_521, 3);
 lean_ctor_release(x_521, 4);
 lean_ctor_release(x_521, 5);
 lean_ctor_release(x_521, 6);
 lean_ctor_release(x_521, 7);
 lean_ctor_release(x_521, 8);
 lean_ctor_release(x_521, 9);
 lean_ctor_release(x_521, 10);
 lean_ctor_release(x_521, 11);
 lean_ctor_release(x_521, 12);
 lean_ctor_release(x_521, 13);
 lean_ctor_release(x_521, 14);
 lean_ctor_release(x_521, 15);
 x_541 = x_521;
} else {
 lean_dec_ref(x_521);
 x_541 = lean_box(0);
}
x_542 = lean_ctor_get(x_522, 0);
lean_inc_ref(x_542);
x_543 = lean_ctor_get(x_522, 2);
lean_inc_ref(x_543);
x_544 = lean_ctor_get(x_522, 3);
lean_inc_ref(x_544);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 lean_ctor_release(x_522, 1);
 lean_ctor_release(x_522, 2);
 lean_ctor_release(x_522, 3);
 x_545 = x_522;
} else {
 lean_dec_ref(x_522);
 x_545 = lean_box(0);
}
x_546 = lean_ctor_get(x_523, 0);
lean_inc_ref(x_546);
x_547 = lean_ctor_get(x_523, 1);
lean_inc_ref(x_547);
x_548 = lean_ctor_get(x_523, 2);
lean_inc_ref(x_548);
x_549 = lean_ctor_get(x_523, 3);
lean_inc_ref(x_549);
x_550 = lean_ctor_get(x_523, 4);
lean_inc_ref(x_550);
x_551 = lean_ctor_get(x_523, 5);
lean_inc_ref(x_551);
x_552 = lean_ctor_get(x_523, 6);
lean_inc_ref(x_552);
x_553 = lean_ctor_get(x_523, 7);
lean_inc_ref(x_553);
x_554 = lean_ctor_get(x_523, 8);
lean_inc_ref(x_554);
x_555 = lean_ctor_get(x_523, 9);
lean_inc_ref(x_555);
x_556 = lean_ctor_get(x_523, 10);
lean_inc_ref(x_556);
x_557 = lean_ctor_get(x_523, 11);
lean_inc(x_557);
x_558 = lean_ctor_get(x_523, 12);
lean_inc_ref(x_558);
x_559 = lean_ctor_get(x_523, 13);
lean_inc_ref(x_559);
x_560 = lean_ctor_get(x_523, 14);
lean_inc(x_560);
x_561 = lean_ctor_get_uint8(x_523, sizeof(void*)*21);
x_562 = lean_ctor_get(x_523, 15);
lean_inc(x_562);
x_563 = lean_ctor_get(x_523, 16);
lean_inc_ref(x_563);
x_564 = lean_ctor_get(x_523, 17);
lean_inc_ref(x_564);
x_565 = lean_ctor_get(x_523, 18);
lean_inc_ref(x_565);
x_566 = lean_ctor_get(x_523, 19);
lean_inc_ref(x_566);
x_567 = lean_ctor_get(x_523, 20);
lean_inc_ref(x_567);
x_568 = lean_ctor_get_uint8(x_523, sizeof(void*)*21 + 1);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 lean_ctor_release(x_523, 2);
 lean_ctor_release(x_523, 3);
 lean_ctor_release(x_523, 4);
 lean_ctor_release(x_523, 5);
 lean_ctor_release(x_523, 6);
 lean_ctor_release(x_523, 7);
 lean_ctor_release(x_523, 8);
 lean_ctor_release(x_523, 9);
 lean_ctor_release(x_523, 10);
 lean_ctor_release(x_523, 11);
 lean_ctor_release(x_523, 12);
 lean_ctor_release(x_523, 13);
 lean_ctor_release(x_523, 14);
 lean_ctor_release(x_523, 15);
 lean_ctor_release(x_523, 16);
 lean_ctor_release(x_523, 17);
 lean_ctor_release(x_523, 18);
 lean_ctor_release(x_523, 19);
 lean_ctor_release(x_523, 20);
 x_569 = x_523;
} else {
 lean_dec_ref(x_523);
 x_569 = lean_box(0);
}
x_570 = lean_box(0);
x_571 = l_Lean_PersistentArray_set___redArg(x_552, x_221, x_570);
if (lean_is_scalar(x_569)) {
 x_572 = lean_alloc_ctor(0, 21, 2);
} else {
 x_572 = x_569;
}
lean_ctor_set(x_572, 0, x_546);
lean_ctor_set(x_572, 1, x_547);
lean_ctor_set(x_572, 2, x_548);
lean_ctor_set(x_572, 3, x_549);
lean_ctor_set(x_572, 4, x_550);
lean_ctor_set(x_572, 5, x_551);
lean_ctor_set(x_572, 6, x_571);
lean_ctor_set(x_572, 7, x_553);
lean_ctor_set(x_572, 8, x_554);
lean_ctor_set(x_572, 9, x_555);
lean_ctor_set(x_572, 10, x_556);
lean_ctor_set(x_572, 11, x_557);
lean_ctor_set(x_572, 12, x_558);
lean_ctor_set(x_572, 13, x_559);
lean_ctor_set(x_572, 14, x_560);
lean_ctor_set(x_572, 15, x_562);
lean_ctor_set(x_572, 16, x_563);
lean_ctor_set(x_572, 17, x_564);
lean_ctor_set(x_572, 18, x_565);
lean_ctor_set(x_572, 19, x_566);
lean_ctor_set(x_572, 20, x_567);
lean_ctor_set_uint8(x_572, sizeof(void*)*21, x_561);
lean_ctor_set_uint8(x_572, sizeof(void*)*21 + 1, x_568);
if (lean_is_scalar(x_545)) {
 x_573 = lean_alloc_ctor(0, 4, 0);
} else {
 x_573 = x_545;
}
lean_ctor_set(x_573, 0, x_542);
lean_ctor_set(x_573, 1, x_572);
lean_ctor_set(x_573, 2, x_543);
lean_ctor_set(x_573, 3, x_544);
if (lean_is_scalar(x_541)) {
 x_574 = lean_alloc_ctor(0, 16, 1);
} else {
 x_574 = x_541;
}
lean_ctor_set(x_574, 0, x_525);
lean_ctor_set(x_574, 1, x_526);
lean_ctor_set(x_574, 2, x_527);
lean_ctor_set(x_574, 3, x_528);
lean_ctor_set(x_574, 4, x_529);
lean_ctor_set(x_574, 5, x_530);
lean_ctor_set(x_574, 6, x_531);
lean_ctor_set(x_574, 7, x_532);
lean_ctor_set(x_574, 8, x_534);
lean_ctor_set(x_574, 9, x_535);
lean_ctor_set(x_574, 10, x_536);
lean_ctor_set(x_574, 11, x_537);
lean_ctor_set(x_574, 12, x_538);
lean_ctor_set(x_574, 13, x_539);
lean_ctor_set(x_574, 14, x_573);
lean_ctor_set(x_574, 15, x_540);
lean_ctor_set_uint8(x_574, sizeof(void*)*16, x_533);
x_575 = lean_st_ref_set(x_215, x_574, x_524);
x_576 = lean_ctor_get(x_575, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 lean_ctor_release(x_575, 1);
 x_577 = x_575;
} else {
 lean_dec_ref(x_575);
 x_577 = lean_box(0);
}
x_578 = lean_int_mul(x_518, x_259);
lean_dec(x_518);
lean_inc_ref(x_211);
x_579 = l_Int_Linear_Poly_mul(x_211, x_578);
lean_dec(x_578);
x_580 = lean_int_mul(x_519, x_216);
lean_dec(x_519);
lean_inc_ref(x_512);
x_581 = l_Int_Linear_Poly_mul(x_512, x_580);
lean_dec(x_580);
x_582 = lean_int_mul(x_216, x_259);
lean_dec(x_259);
lean_dec(x_216);
x_583 = l_Int_Linear_Poly_combine(x_579, x_581);
lean_inc(x_517);
x_584 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_584, 0, x_517);
lean_ctor_set(x_584, 1, x_221);
lean_ctor_set(x_584, 2, x_583);
lean_inc(x_256);
lean_inc_ref(x_219);
if (lean_is_scalar(x_577)) {
 x_585 = lean_alloc_ctor(4, 2, 0);
} else {
 x_585 = x_577;
 lean_ctor_set_tag(x_585, 4);
}
lean_ctor_set(x_585, 0, x_219);
lean_ctor_set(x_585, 1, x_256);
x_586 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_586, 0, x_582);
lean_ctor_set(x_586, 1, x_584);
lean_ctor_set(x_586, 2, x_585);
lean_inc(x_214);
lean_inc_ref(x_217);
lean_inc(x_220);
lean_inc_ref(x_209);
lean_inc(x_218);
lean_inc_ref(x_222);
lean_inc(x_213);
lean_inc(x_215);
x_587 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_586, x_215, x_213, x_222, x_218, x_209, x_220, x_217, x_214, x_576);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
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
x_590 = l_Int_Linear_Poly_mul(x_211, x_511);
lean_dec(x_511);
x_591 = lean_int_neg(x_210);
lean_dec(x_210);
x_592 = l_Int_Linear_Poly_mul(x_512, x_591);
lean_dec(x_591);
x_593 = l_Int_Linear_Poly_combine(x_590, x_592);
lean_inc(x_256);
if (lean_is_scalar(x_589)) {
 x_594 = lean_alloc_ctor(5, 2, 0);
} else {
 x_594 = x_589;
 lean_ctor_set_tag(x_594, 5);
}
lean_ctor_set(x_594, 0, x_219);
lean_ctor_set(x_594, 1, x_256);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 x_595 = x_256;
} else {
 lean_dec_ref(x_256);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(0, 3, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_517);
lean_ctor_set(x_596, 1, x_593);
lean_ctor_set(x_596, 2, x_594);
x_1 = x_596;
x_2 = x_215;
x_3 = x_213;
x_4 = x_222;
x_5 = x_218;
x_6 = x_209;
x_7 = x_220;
x_8 = x_217;
x_9 = x_214;
x_10 = x_588;
goto _start;
}
else
{
lean_dec(x_517);
lean_dec_ref(x_512);
lean_dec(x_511);
lean_dec(x_256);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec_ref(x_217);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
return x_587;
}
}
}
}
}
block_632:
{
lean_object* x_620; 
x_620 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_611, x_619);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; uint8_t x_625; 
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_621, 6);
lean_inc_ref(x_622);
lean_dec(x_621);
x_623 = lean_ctor_get(x_620, 1);
lean_inc(x_623);
lean_dec_ref(x_620);
x_624 = lean_ctor_get(x_622, 2);
lean_inc(x_624);
x_625 = lean_nat_dec_lt(x_608, x_624);
lean_dec(x_624);
if (x_625 == 0)
{
lean_object* x_626; 
lean_dec_ref(x_622);
x_626 = l_outOfBounds___redArg(x_604);
x_208 = x_605;
x_209 = x_615;
x_210 = x_606;
x_211 = x_609;
x_212 = x_623;
x_213 = x_612;
x_214 = x_618;
x_215 = x_611;
x_216 = x_610;
x_217 = x_617;
x_218 = x_614;
x_219 = x_607;
x_220 = x_616;
x_221 = x_608;
x_222 = x_613;
x_223 = x_626;
goto block_598;
}
else
{
lean_object* x_627; 
x_627 = l_Lean_PersistentArray_get_x21___redArg(x_604, x_622, x_608);
x_208 = x_605;
x_209 = x_615;
x_210 = x_606;
x_211 = x_609;
x_212 = x_623;
x_213 = x_612;
x_214 = x_618;
x_215 = x_611;
x_216 = x_610;
x_217 = x_617;
x_218 = x_614;
x_219 = x_607;
x_220 = x_616;
x_221 = x_608;
x_222 = x_613;
x_223 = x_627;
goto block_598;
}
}
else
{
uint8_t x_628; 
lean_dec(x_618);
lean_dec_ref(x_617);
lean_dec(x_616);
lean_dec_ref(x_615);
lean_dec(x_614);
lean_dec_ref(x_613);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_610);
lean_dec_ref(x_609);
lean_dec(x_608);
lean_dec_ref(x_607);
lean_dec(x_606);
lean_dec_ref(x_605);
x_628 = !lean_is_exclusive(x_620);
if (x_628 == 0)
{
return x_620;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_ctor_get(x_620, 0);
x_630 = lean_ctor_get(x_620, 1);
lean_inc(x_630);
lean_inc(x_629);
lean_dec(x_620);
x_631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_631, 0, x_629);
lean_ctor_set(x_631, 1, x_630);
return x_631;
}
}
}
block_734:
{
lean_object* x_642; lean_object* x_643; 
x_642 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_639);
x_643 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_642, x_633, x_634, x_635, x_636, x_637, x_638, x_639, x_640, x_641);
if (lean_obj_tag(x_643) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; uint8_t x_648; 
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_643, 1);
lean_inc(x_645);
lean_dec_ref(x_643);
x_646 = lean_ctor_get(x_644, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_644, 1);
lean_inc_ref(x_647);
lean_inc(x_646);
x_648 = l_Int_Linear_Poly_isUnsatDvd(x_646, x_647);
if (x_648 == 0)
{
uint8_t x_649; 
x_649 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_644);
if (x_649 == 0)
{
lean_dec(x_603);
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_650; 
lean_dec_ref(x_647);
lean_dec(x_646);
x_650 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_644, x_633, x_634, x_635, x_636, x_637, x_638, x_639, x_640, x_645);
lean_dec(x_640);
lean_dec_ref(x_639);
lean_dec(x_638);
lean_dec_ref(x_637);
lean_dec(x_636);
lean_dec_ref(x_635);
lean_dec(x_634);
lean_dec(x_633);
return x_650;
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_651 = lean_ctor_get(x_647, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_647, 1);
lean_inc(x_652);
x_653 = lean_ctor_get(x_647, 2);
lean_inc_ref(x_653);
lean_inc(x_644);
x_654 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_644, x_633, x_645);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; lean_object* x_656; uint8_t x_657; uint8_t x_658; uint8_t x_659; 
x_655 = lean_ctor_get(x_654, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_654, 1);
lean_inc(x_656);
lean_dec_ref(x_654);
x_657 = 0;
x_658 = lean_unbox(x_655);
lean_dec(x_655);
x_659 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_20_(x_658, x_657);
if (x_659 == 0)
{
x_605 = x_647;
x_606 = x_651;
x_607 = x_644;
x_608 = x_652;
x_609 = x_653;
x_610 = x_646;
x_611 = x_633;
x_612 = x_634;
x_613 = x_635;
x_614 = x_636;
x_615 = x_637;
x_616 = x_638;
x_617 = x_639;
x_618 = x_640;
x_619 = x_656;
goto block_632;
}
else
{
lean_object* x_660; 
x_660 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_652, x_633, x_656);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; 
x_661 = lean_ctor_get(x_660, 1);
lean_inc(x_661);
lean_dec_ref(x_660);
x_605 = x_647;
x_606 = x_651;
x_607 = x_644;
x_608 = x_652;
x_609 = x_653;
x_610 = x_646;
x_611 = x_633;
x_612 = x_634;
x_613 = x_635;
x_614 = x_636;
x_615 = x_637;
x_616 = x_638;
x_617 = x_639;
x_618 = x_640;
x_619 = x_661;
goto block_632;
}
else
{
lean_dec_ref(x_653);
lean_dec(x_652);
lean_dec(x_651);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec(x_644);
lean_dec(x_640);
lean_dec_ref(x_639);
lean_dec(x_638);
lean_dec_ref(x_637);
lean_dec(x_636);
lean_dec_ref(x_635);
lean_dec(x_634);
lean_dec(x_633);
return x_660;
}
}
}
else
{
uint8_t x_662; 
lean_dec_ref(x_653);
lean_dec(x_652);
lean_dec(x_651);
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec(x_644);
lean_dec(x_640);
lean_dec_ref(x_639);
lean_dec(x_638);
lean_dec_ref(x_637);
lean_dec(x_636);
lean_dec_ref(x_635);
lean_dec(x_634);
lean_dec(x_633);
x_662 = !lean_is_exclusive(x_654);
if (x_662 == 0)
{
return x_654;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_663 = lean_ctor_get(x_654, 0);
x_664 = lean_ctor_get(x_654, 1);
lean_inc(x_664);
lean_inc(x_663);
lean_dec(x_654);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_663);
lean_ctor_set(x_665, 1, x_664);
return x_665;
}
}
}
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; uint8_t x_669; 
lean_dec_ref(x_647);
lean_dec(x_646);
lean_dec(x_636);
lean_dec_ref(x_635);
lean_dec(x_634);
x_666 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_667 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_666, x_639, x_645);
x_668 = lean_ctor_get(x_667, 0);
lean_inc(x_668);
x_669 = lean_unbox(x_668);
lean_dec(x_668);
if (x_669 == 0)
{
lean_object* x_670; 
lean_dec(x_644);
lean_dec(x_640);
lean_dec_ref(x_639);
lean_dec(x_638);
lean_dec_ref(x_637);
lean_dec(x_633);
lean_dec(x_603);
x_670 = lean_ctor_get(x_667, 1);
lean_inc(x_670);
lean_dec_ref(x_667);
x_183 = x_670;
goto block_186;
}
else
{
uint8_t x_671; 
x_671 = !lean_is_exclusive(x_667);
if (x_671 == 0)
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_672 = lean_ctor_get(x_667, 1);
x_673 = lean_ctor_get(x_667, 0);
lean_dec(x_673);
x_674 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_644, x_633, x_672);
lean_dec(x_633);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec_ref(x_674);
x_677 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_667, 7);
lean_ctor_set(x_667, 1, x_675);
lean_ctor_set(x_667, 0, x_677);
if (lean_is_scalar(x_603)) {
 x_678 = lean_alloc_ctor(7, 2, 0);
} else {
 x_678 = x_603;
 lean_ctor_set_tag(x_678, 7);
}
lean_ctor_set(x_678, 0, x_667);
lean_ctor_set(x_678, 1, x_677);
x_679 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_666, x_678, x_637, x_638, x_639, x_640, x_676);
lean_dec(x_640);
lean_dec_ref(x_639);
lean_dec(x_638);
lean_dec_ref(x_637);
x_680 = lean_ctor_get(x_679, 1);
lean_inc(x_680);
lean_dec_ref(x_679);
x_183 = x_680;
goto block_186;
}
else
{
uint8_t x_681; 
lean_free_object(x_667);
lean_dec(x_640);
lean_dec_ref(x_639);
lean_dec(x_638);
lean_dec_ref(x_637);
lean_dec(x_603);
x_681 = !lean_is_exclusive(x_674);
if (x_681 == 0)
{
return x_674;
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_682 = lean_ctor_get(x_674, 0);
x_683 = lean_ctor_get(x_674, 1);
lean_inc(x_683);
lean_inc(x_682);
lean_dec(x_674);
x_684 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_684, 0, x_682);
lean_ctor_set(x_684, 1, x_683);
return x_684;
}
}
}
else
{
lean_object* x_685; lean_object* x_686; 
x_685 = lean_ctor_get(x_667, 1);
lean_inc(x_685);
lean_dec(x_667);
x_686 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_644, x_633, x_685);
lean_dec(x_633);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
lean_dec_ref(x_686);
x_689 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_690 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_690, 0, x_689);
lean_ctor_set(x_690, 1, x_687);
if (lean_is_scalar(x_603)) {
 x_691 = lean_alloc_ctor(7, 2, 0);
} else {
 x_691 = x_603;
 lean_ctor_set_tag(x_691, 7);
}
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_689);
x_692 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_666, x_691, x_637, x_638, x_639, x_640, x_688);
lean_dec(x_640);
lean_dec_ref(x_639);
lean_dec(x_638);
lean_dec_ref(x_637);
x_693 = lean_ctor_get(x_692, 1);
lean_inc(x_693);
lean_dec_ref(x_692);
x_183 = x_693;
goto block_186;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
lean_dec(x_640);
lean_dec_ref(x_639);
lean_dec(x_638);
lean_dec_ref(x_637);
lean_dec(x_603);
x_694 = lean_ctor_get(x_686, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_686, 1);
lean_inc(x_695);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_696 = x_686;
} else {
 lean_dec_ref(x_686);
 x_696 = lean_box(0);
}
if (lean_is_scalar(x_696)) {
 x_697 = lean_alloc_ctor(1, 2, 0);
} else {
 x_697 = x_696;
}
lean_ctor_set(x_697, 0, x_694);
lean_ctor_set(x_697, 1, x_695);
return x_697;
}
}
}
}
}
else
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; uint8_t x_701; 
lean_dec_ref(x_647);
lean_dec(x_646);
x_698 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_699 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_698, x_639, x_645);
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_unbox(x_700);
lean_dec(x_700);
if (x_701 == 0)
{
lean_object* x_702; 
lean_dec(x_603);
x_702 = lean_ctor_get(x_699, 1);
lean_inc(x_702);
lean_dec_ref(x_699);
x_164 = x_644;
x_165 = x_633;
x_166 = x_634;
x_167 = x_635;
x_168 = x_636;
x_169 = x_637;
x_170 = x_638;
x_171 = x_639;
x_172 = x_640;
x_173 = x_702;
goto block_182;
}
else
{
uint8_t x_703; 
x_703 = !lean_is_exclusive(x_699);
if (x_703 == 0)
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_704 = lean_ctor_get(x_699, 1);
x_705 = lean_ctor_get(x_699, 0);
lean_dec(x_705);
lean_inc(x_644);
x_706 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_644, x_633, x_704);
if (lean_obj_tag(x_706) == 0)
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_707 = lean_ctor_get(x_706, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_706, 1);
lean_inc(x_708);
lean_dec_ref(x_706);
x_709 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_699, 7);
lean_ctor_set(x_699, 1, x_707);
lean_ctor_set(x_699, 0, x_709);
if (lean_is_scalar(x_603)) {
 x_710 = lean_alloc_ctor(7, 2, 0);
} else {
 x_710 = x_603;
 lean_ctor_set_tag(x_710, 7);
}
lean_ctor_set(x_710, 0, x_699);
lean_ctor_set(x_710, 1, x_709);
x_711 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_698, x_710, x_637, x_638, x_639, x_640, x_708);
x_712 = lean_ctor_get(x_711, 1);
lean_inc(x_712);
lean_dec_ref(x_711);
x_164 = x_644;
x_165 = x_633;
x_166 = x_634;
x_167 = x_635;
x_168 = x_636;
x_169 = x_637;
x_170 = x_638;
x_171 = x_639;
x_172 = x_640;
x_173 = x_712;
goto block_182;
}
else
{
uint8_t x_713; 
lean_free_object(x_699);
lean_dec(x_644);
lean_dec(x_640);
lean_dec_ref(x_639);
lean_dec(x_638);
lean_dec_ref(x_637);
lean_dec(x_636);
lean_dec_ref(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_603);
x_713 = !lean_is_exclusive(x_706);
if (x_713 == 0)
{
return x_706;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_714 = lean_ctor_get(x_706, 0);
x_715 = lean_ctor_get(x_706, 1);
lean_inc(x_715);
lean_inc(x_714);
lean_dec(x_706);
x_716 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_716, 0, x_714);
lean_ctor_set(x_716, 1, x_715);
return x_716;
}
}
}
else
{
lean_object* x_717; lean_object* x_718; 
x_717 = lean_ctor_get(x_699, 1);
lean_inc(x_717);
lean_dec(x_699);
lean_inc(x_644);
x_718 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_644, x_633, x_717);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
lean_dec_ref(x_718);
x_721 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_722 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_722, 0, x_721);
lean_ctor_set(x_722, 1, x_719);
if (lean_is_scalar(x_603)) {
 x_723 = lean_alloc_ctor(7, 2, 0);
} else {
 x_723 = x_603;
 lean_ctor_set_tag(x_723, 7);
}
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_721);
x_724 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_698, x_723, x_637, x_638, x_639, x_640, x_720);
x_725 = lean_ctor_get(x_724, 1);
lean_inc(x_725);
lean_dec_ref(x_724);
x_164 = x_644;
x_165 = x_633;
x_166 = x_634;
x_167 = x_635;
x_168 = x_636;
x_169 = x_637;
x_170 = x_638;
x_171 = x_639;
x_172 = x_640;
x_173 = x_725;
goto block_182;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
lean_dec(x_644);
lean_dec(x_640);
lean_dec_ref(x_639);
lean_dec(x_638);
lean_dec_ref(x_637);
lean_dec(x_636);
lean_dec_ref(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_603);
x_726 = lean_ctor_get(x_718, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_718, 1);
lean_inc(x_727);
if (lean_is_exclusive(x_718)) {
 lean_ctor_release(x_718, 0);
 lean_ctor_release(x_718, 1);
 x_728 = x_718;
} else {
 lean_dec_ref(x_718);
 x_728 = lean_box(0);
}
if (lean_is_scalar(x_728)) {
 x_729 = lean_alloc_ctor(1, 2, 0);
} else {
 x_729 = x_728;
}
lean_ctor_set(x_729, 0, x_726);
lean_ctor_set(x_729, 1, x_727);
return x_729;
}
}
}
}
}
else
{
uint8_t x_730; 
lean_dec(x_640);
lean_dec_ref(x_639);
lean_dec(x_638);
lean_dec_ref(x_637);
lean_dec(x_636);
lean_dec_ref(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_603);
x_730 = !lean_is_exclusive(x_643);
if (x_730 == 0)
{
return x_643;
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_731 = lean_ctor_get(x_643, 0);
x_732 = lean_ctor_get(x_643, 1);
lean_inc(x_732);
lean_inc(x_731);
lean_dec(x_643);
x_733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_733, 0, x_731);
lean_ctor_set(x_733, 1, x_732);
return x_733;
}
}
}
}
else
{
uint8_t x_748; 
lean_free_object(x_8);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec_ref(x_189);
lean_dec_ref(x_188);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_748 = !lean_is_exclusive(x_202);
if (x_748 == 0)
{
lean_object* x_749; lean_object* x_750; 
x_749 = lean_ctor_get(x_202, 0);
lean_dec(x_749);
x_750 = lean_box(0);
lean_ctor_set(x_202, 0, x_750);
return x_202;
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_751 = lean_ctor_get(x_202, 1);
lean_inc(x_751);
lean_dec(x_202);
x_752 = lean_box(0);
x_753 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_753, 0, x_752);
lean_ctor_set(x_753, 1, x_751);
return x_753;
}
}
}
else
{
uint8_t x_754; 
lean_free_object(x_8);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec_ref(x_189);
lean_dec_ref(x_188);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_754 = !lean_is_exclusive(x_202);
if (x_754 == 0)
{
return x_202;
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_755 = lean_ctor_get(x_202, 0);
x_756 = lean_ctor_get(x_202, 1);
lean_inc(x_756);
lean_inc(x_755);
lean_dec(x_202);
x_757 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set(x_757, 1, x_756);
return x_757;
}
}
}
else
{
lean_object* x_758; 
lean_free_object(x_8);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec_ref(x_189);
lean_dec_ref(x_188);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_758 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_193, x_10);
return x_758;
}
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; uint8_t x_770; lean_object* x_771; uint8_t x_772; lean_object* x_773; uint8_t x_774; 
x_759 = lean_ctor_get(x_8, 0);
x_760 = lean_ctor_get(x_8, 1);
x_761 = lean_ctor_get(x_8, 2);
x_762 = lean_ctor_get(x_8, 3);
x_763 = lean_ctor_get(x_8, 4);
x_764 = lean_ctor_get(x_8, 5);
x_765 = lean_ctor_get(x_8, 6);
x_766 = lean_ctor_get(x_8, 7);
x_767 = lean_ctor_get(x_8, 8);
x_768 = lean_ctor_get(x_8, 9);
x_769 = lean_ctor_get(x_8, 10);
x_770 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_771 = lean_ctor_get(x_8, 11);
x_772 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_773 = lean_ctor_get(x_8, 12);
lean_inc(x_773);
lean_inc(x_771);
lean_inc(x_769);
lean_inc(x_768);
lean_inc(x_767);
lean_inc(x_766);
lean_inc(x_765);
lean_inc(x_764);
lean_inc(x_763);
lean_inc(x_762);
lean_inc(x_761);
lean_inc(x_760);
lean_inc(x_759);
lean_dec(x_8);
x_774 = lean_nat_dec_eq(x_762, x_763);
if (x_774 == 0)
{
lean_object* x_775; 
x_775 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; uint8_t x_777; 
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
x_777 = lean_unbox(x_776);
lean_dec(x_776);
if (x_777 == 0)
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; uint8_t x_1020; 
x_778 = lean_ctor_get(x_775, 1);
lean_inc(x_778);
lean_dec_ref(x_775);
x_779 = lean_unsigned_to_nat(1u);
x_780 = lean_nat_add(x_762, x_779);
lean_dec(x_762);
x_781 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_781, 0, x_759);
lean_ctor_set(x_781, 1, x_760);
lean_ctor_set(x_781, 2, x_761);
lean_ctor_set(x_781, 3, x_780);
lean_ctor_set(x_781, 4, x_763);
lean_ctor_set(x_781, 5, x_764);
lean_ctor_set(x_781, 6, x_765);
lean_ctor_set(x_781, 7, x_766);
lean_ctor_set(x_781, 8, x_767);
lean_ctor_set(x_781, 9, x_768);
lean_ctor_set(x_781, 10, x_769);
lean_ctor_set(x_781, 11, x_771);
lean_ctor_set(x_781, 12, x_773);
lean_ctor_set_uint8(x_781, sizeof(void*)*13, x_770);
lean_ctor_set_uint8(x_781, sizeof(void*)*13 + 1, x_772);
x_910 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_911 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_910, x_781, x_778);
x_912 = lean_ctor_get(x_911, 0);
lean_inc(x_912);
x_913 = lean_ctor_get(x_911, 1);
lean_inc(x_913);
if (lean_is_exclusive(x_911)) {
 lean_ctor_release(x_911, 0);
 lean_ctor_release(x_911, 1);
 x_914 = x_911;
} else {
 lean_dec_ref(x_911);
 x_914 = lean_box(0);
}
x_915 = lean_box(0);
x_1020 = lean_unbox(x_912);
lean_dec(x_912);
if (x_1020 == 0)
{
x_944 = x_2;
x_945 = x_3;
x_946 = x_4;
x_947 = x_5;
x_948 = x_6;
x_949 = x_7;
x_950 = x_781;
x_951 = x_9;
x_952 = x_913;
goto block_1019;
}
else
{
lean_object* x_1021; 
lean_inc_ref(x_1);
x_1021 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_913);
if (lean_obj_tag(x_1021) == 0)
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
x_1022 = lean_ctor_get(x_1021, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1021, 1);
lean_inc(x_1023);
lean_dec_ref(x_1021);
x_1024 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_1025 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1025, 0, x_1024);
lean_ctor_set(x_1025, 1, x_1022);
x_1026 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1026, 0, x_1025);
lean_ctor_set(x_1026, 1, x_1024);
x_1027 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_910, x_1026, x_6, x_7, x_781, x_9, x_1023);
x_1028 = lean_ctor_get(x_1027, 1);
lean_inc(x_1028);
lean_dec_ref(x_1027);
x_944 = x_2;
x_945 = x_3;
x_946 = x_4;
x_947 = x_5;
x_948 = x_6;
x_949 = x_7;
x_950 = x_781;
x_951 = x_9;
x_952 = x_1028;
goto block_1019;
}
else
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
lean_dec(x_914);
lean_dec_ref(x_781);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1029 = lean_ctor_get(x_1021, 0);
lean_inc(x_1029);
x_1030 = lean_ctor_get(x_1021, 1);
lean_inc(x_1030);
if (lean_is_exclusive(x_1021)) {
 lean_ctor_release(x_1021, 0);
 lean_ctor_release(x_1021, 1);
 x_1031 = x_1021;
} else {
 lean_dec_ref(x_1021);
 x_1031 = lean_box(0);
}
if (lean_is_scalar(x_1031)) {
 x_1032 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1032 = x_1031;
}
lean_ctor_set(x_1032, 0, x_1029);
lean_ctor_set(x_1032, 1, x_1030);
return x_1032;
}
}
block_909:
{
if (lean_obj_tag(x_797) == 0)
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; uint8_t x_801; 
lean_dec_ref(x_796);
lean_dec(x_792);
lean_dec(x_790);
lean_dec(x_787);
lean_dec_ref(x_785);
lean_dec(x_784);
x_798 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_799 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_798, x_791, x_786);
x_800 = lean_ctor_get(x_799, 0);
lean_inc(x_800);
x_801 = lean_unbox(x_800);
lean_dec(x_800);
if (x_801 == 0)
{
lean_object* x_802; 
x_802 = lean_ctor_get(x_799, 1);
lean_inc(x_802);
lean_dec_ref(x_799);
x_11 = x_782;
x_12 = x_793;
x_13 = x_795;
x_14 = x_789;
x_15 = x_783;
x_16 = x_794;
x_17 = x_791;
x_18 = x_788;
x_19 = x_802;
goto block_163;
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_803 = lean_ctor_get(x_799, 1);
lean_inc(x_803);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_804 = x_799;
} else {
 lean_dec_ref(x_799);
 x_804 = lean_box(0);
}
lean_inc_ref(x_793);
x_805 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_793, x_789, x_803);
if (lean_obj_tag(x_805) == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_806 = lean_ctor_get(x_805, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_805, 1);
lean_inc(x_807);
lean_dec_ref(x_805);
x_808 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_804)) {
 x_809 = lean_alloc_ctor(7, 2, 0);
} else {
 x_809 = x_804;
 lean_ctor_set_tag(x_809, 7);
}
lean_ctor_set(x_809, 0, x_808);
lean_ctor_set(x_809, 1, x_806);
x_810 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_810, 0, x_809);
lean_ctor_set(x_810, 1, x_808);
x_811 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_798, x_810, x_783, x_794, x_791, x_788, x_807);
x_812 = lean_ctor_get(x_811, 1);
lean_inc(x_812);
lean_dec_ref(x_811);
x_11 = x_782;
x_12 = x_793;
x_13 = x_795;
x_14 = x_789;
x_15 = x_783;
x_16 = x_794;
x_17 = x_791;
x_18 = x_788;
x_19 = x_812;
goto block_163;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
lean_dec(x_804);
lean_dec(x_795);
lean_dec(x_794);
lean_dec_ref(x_793);
lean_dec_ref(x_791);
lean_dec(x_789);
lean_dec(x_788);
lean_dec_ref(x_783);
lean_dec_ref(x_782);
x_813 = lean_ctor_get(x_805, 0);
lean_inc(x_813);
x_814 = lean_ctor_get(x_805, 1);
lean_inc(x_814);
if (lean_is_exclusive(x_805)) {
 lean_ctor_release(x_805, 0);
 lean_ctor_release(x_805, 1);
 x_815 = x_805;
} else {
 lean_dec_ref(x_805);
 x_815 = lean_box(0);
}
if (lean_is_scalar(x_815)) {
 x_816 = lean_alloc_ctor(1, 2, 0);
} else {
 x_816 = x_815;
}
lean_ctor_set(x_816, 0, x_813);
lean_ctor_set(x_816, 1, x_814);
return x_816;
}
}
}
else
{
lean_object* x_817; lean_object* x_818; 
lean_dec_ref(x_782);
x_817 = lean_ctor_get(x_797, 0);
lean_inc(x_817);
lean_dec_ref(x_797);
x_818 = lean_ctor_get(x_817, 1);
lean_inc_ref(x_818);
if (lean_obj_tag(x_818) == 0)
{
lean_object* x_819; 
lean_dec_ref(x_818);
lean_dec(x_795);
lean_dec_ref(x_793);
lean_dec(x_790);
lean_dec_ref(x_785);
lean_dec(x_784);
x_819 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_817, x_789, x_787, x_796, x_792, x_783, x_794, x_791, x_788, x_786);
lean_dec(x_788);
lean_dec_ref(x_791);
lean_dec(x_794);
lean_dec_ref(x_783);
lean_dec(x_792);
lean_dec_ref(x_796);
lean_dec(x_787);
lean_dec(x_789);
return x_819;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; uint8_t x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; uint8_t x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; uint8_t x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
x_820 = lean_ctor_get(x_817, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_818, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_818, 2);
lean_inc_ref(x_822);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 lean_ctor_release(x_818, 1);
 lean_ctor_release(x_818, 2);
 x_823 = x_818;
} else {
 lean_dec_ref(x_818);
 x_823 = lean_box(0);
}
x_824 = lean_int_mul(x_784, x_820);
x_825 = lean_int_mul(x_821, x_790);
x_826 = l_Lean_Meta_Grind_Arith_gcdExt(x_824, x_825);
lean_dec(x_825);
lean_dec(x_824);
x_827 = lean_ctor_get(x_826, 1);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 0);
lean_inc(x_828);
lean_dec_ref(x_826);
x_829 = lean_ctor_get(x_827, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_827, 1);
lean_inc(x_830);
lean_dec(x_827);
x_831 = lean_st_ref_take(x_789, x_786);
x_832 = lean_ctor_get(x_831, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_832, 14);
lean_inc_ref(x_833);
x_834 = lean_ctor_get(x_833, 1);
lean_inc_ref(x_834);
x_835 = lean_ctor_get(x_831, 1);
lean_inc(x_835);
lean_dec_ref(x_831);
x_836 = lean_ctor_get(x_832, 0);
lean_inc(x_836);
x_837 = lean_ctor_get(x_832, 1);
lean_inc_ref(x_837);
x_838 = lean_ctor_get(x_832, 2);
lean_inc(x_838);
x_839 = lean_ctor_get(x_832, 3);
lean_inc_ref(x_839);
x_840 = lean_ctor_get(x_832, 4);
lean_inc_ref(x_840);
x_841 = lean_ctor_get(x_832, 5);
lean_inc_ref(x_841);
x_842 = lean_ctor_get(x_832, 6);
lean_inc_ref(x_842);
x_843 = lean_ctor_get(x_832, 7);
lean_inc_ref(x_843);
x_844 = lean_ctor_get_uint8(x_832, sizeof(void*)*16);
x_845 = lean_ctor_get(x_832, 8);
lean_inc(x_845);
x_846 = lean_ctor_get(x_832, 9);
lean_inc_ref(x_846);
x_847 = lean_ctor_get(x_832, 10);
lean_inc_ref(x_847);
x_848 = lean_ctor_get(x_832, 11);
lean_inc_ref(x_848);
x_849 = lean_ctor_get(x_832, 12);
lean_inc_ref(x_849);
x_850 = lean_ctor_get(x_832, 13);
lean_inc_ref(x_850);
x_851 = lean_ctor_get(x_832, 15);
lean_inc_ref(x_851);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 lean_ctor_release(x_832, 1);
 lean_ctor_release(x_832, 2);
 lean_ctor_release(x_832, 3);
 lean_ctor_release(x_832, 4);
 lean_ctor_release(x_832, 5);
 lean_ctor_release(x_832, 6);
 lean_ctor_release(x_832, 7);
 lean_ctor_release(x_832, 8);
 lean_ctor_release(x_832, 9);
 lean_ctor_release(x_832, 10);
 lean_ctor_release(x_832, 11);
 lean_ctor_release(x_832, 12);
 lean_ctor_release(x_832, 13);
 lean_ctor_release(x_832, 14);
 lean_ctor_release(x_832, 15);
 x_852 = x_832;
} else {
 lean_dec_ref(x_832);
 x_852 = lean_box(0);
}
x_853 = lean_ctor_get(x_833, 0);
lean_inc_ref(x_853);
x_854 = lean_ctor_get(x_833, 2);
lean_inc_ref(x_854);
x_855 = lean_ctor_get(x_833, 3);
lean_inc_ref(x_855);
if (lean_is_exclusive(x_833)) {
 lean_ctor_release(x_833, 0);
 lean_ctor_release(x_833, 1);
 lean_ctor_release(x_833, 2);
 lean_ctor_release(x_833, 3);
 x_856 = x_833;
} else {
 lean_dec_ref(x_833);
 x_856 = lean_box(0);
}
x_857 = lean_ctor_get(x_834, 0);
lean_inc_ref(x_857);
x_858 = lean_ctor_get(x_834, 1);
lean_inc_ref(x_858);
x_859 = lean_ctor_get(x_834, 2);
lean_inc_ref(x_859);
x_860 = lean_ctor_get(x_834, 3);
lean_inc_ref(x_860);
x_861 = lean_ctor_get(x_834, 4);
lean_inc_ref(x_861);
x_862 = lean_ctor_get(x_834, 5);
lean_inc_ref(x_862);
x_863 = lean_ctor_get(x_834, 6);
lean_inc_ref(x_863);
x_864 = lean_ctor_get(x_834, 7);
lean_inc_ref(x_864);
x_865 = lean_ctor_get(x_834, 8);
lean_inc_ref(x_865);
x_866 = lean_ctor_get(x_834, 9);
lean_inc_ref(x_866);
x_867 = lean_ctor_get(x_834, 10);
lean_inc_ref(x_867);
x_868 = lean_ctor_get(x_834, 11);
lean_inc(x_868);
x_869 = lean_ctor_get(x_834, 12);
lean_inc_ref(x_869);
x_870 = lean_ctor_get(x_834, 13);
lean_inc_ref(x_870);
x_871 = lean_ctor_get(x_834, 14);
lean_inc(x_871);
x_872 = lean_ctor_get_uint8(x_834, sizeof(void*)*21);
x_873 = lean_ctor_get(x_834, 15);
lean_inc(x_873);
x_874 = lean_ctor_get(x_834, 16);
lean_inc_ref(x_874);
x_875 = lean_ctor_get(x_834, 17);
lean_inc_ref(x_875);
x_876 = lean_ctor_get(x_834, 18);
lean_inc_ref(x_876);
x_877 = lean_ctor_get(x_834, 19);
lean_inc_ref(x_877);
x_878 = lean_ctor_get(x_834, 20);
lean_inc_ref(x_878);
x_879 = lean_ctor_get_uint8(x_834, sizeof(void*)*21 + 1);
if (lean_is_exclusive(x_834)) {
 lean_ctor_release(x_834, 0);
 lean_ctor_release(x_834, 1);
 lean_ctor_release(x_834, 2);
 lean_ctor_release(x_834, 3);
 lean_ctor_release(x_834, 4);
 lean_ctor_release(x_834, 5);
 lean_ctor_release(x_834, 6);
 lean_ctor_release(x_834, 7);
 lean_ctor_release(x_834, 8);
 lean_ctor_release(x_834, 9);
 lean_ctor_release(x_834, 10);
 lean_ctor_release(x_834, 11);
 lean_ctor_release(x_834, 12);
 lean_ctor_release(x_834, 13);
 lean_ctor_release(x_834, 14);
 lean_ctor_release(x_834, 15);
 lean_ctor_release(x_834, 16);
 lean_ctor_release(x_834, 17);
 lean_ctor_release(x_834, 18);
 lean_ctor_release(x_834, 19);
 lean_ctor_release(x_834, 20);
 x_880 = x_834;
} else {
 lean_dec_ref(x_834);
 x_880 = lean_box(0);
}
x_881 = lean_box(0);
x_882 = l_Lean_PersistentArray_set___redArg(x_863, x_795, x_881);
if (lean_is_scalar(x_880)) {
 x_883 = lean_alloc_ctor(0, 21, 2);
} else {
 x_883 = x_880;
}
lean_ctor_set(x_883, 0, x_857);
lean_ctor_set(x_883, 1, x_858);
lean_ctor_set(x_883, 2, x_859);
lean_ctor_set(x_883, 3, x_860);
lean_ctor_set(x_883, 4, x_861);
lean_ctor_set(x_883, 5, x_862);
lean_ctor_set(x_883, 6, x_882);
lean_ctor_set(x_883, 7, x_864);
lean_ctor_set(x_883, 8, x_865);
lean_ctor_set(x_883, 9, x_866);
lean_ctor_set(x_883, 10, x_867);
lean_ctor_set(x_883, 11, x_868);
lean_ctor_set(x_883, 12, x_869);
lean_ctor_set(x_883, 13, x_870);
lean_ctor_set(x_883, 14, x_871);
lean_ctor_set(x_883, 15, x_873);
lean_ctor_set(x_883, 16, x_874);
lean_ctor_set(x_883, 17, x_875);
lean_ctor_set(x_883, 18, x_876);
lean_ctor_set(x_883, 19, x_877);
lean_ctor_set(x_883, 20, x_878);
lean_ctor_set_uint8(x_883, sizeof(void*)*21, x_872);
lean_ctor_set_uint8(x_883, sizeof(void*)*21 + 1, x_879);
if (lean_is_scalar(x_856)) {
 x_884 = lean_alloc_ctor(0, 4, 0);
} else {
 x_884 = x_856;
}
lean_ctor_set(x_884, 0, x_853);
lean_ctor_set(x_884, 1, x_883);
lean_ctor_set(x_884, 2, x_854);
lean_ctor_set(x_884, 3, x_855);
if (lean_is_scalar(x_852)) {
 x_885 = lean_alloc_ctor(0, 16, 1);
} else {
 x_885 = x_852;
}
lean_ctor_set(x_885, 0, x_836);
lean_ctor_set(x_885, 1, x_837);
lean_ctor_set(x_885, 2, x_838);
lean_ctor_set(x_885, 3, x_839);
lean_ctor_set(x_885, 4, x_840);
lean_ctor_set(x_885, 5, x_841);
lean_ctor_set(x_885, 6, x_842);
lean_ctor_set(x_885, 7, x_843);
lean_ctor_set(x_885, 8, x_845);
lean_ctor_set(x_885, 9, x_846);
lean_ctor_set(x_885, 10, x_847);
lean_ctor_set(x_885, 11, x_848);
lean_ctor_set(x_885, 12, x_849);
lean_ctor_set(x_885, 13, x_850);
lean_ctor_set(x_885, 14, x_884);
lean_ctor_set(x_885, 15, x_851);
lean_ctor_set_uint8(x_885, sizeof(void*)*16, x_844);
x_886 = lean_st_ref_set(x_789, x_885, x_835);
x_887 = lean_ctor_get(x_886, 1);
lean_inc(x_887);
if (lean_is_exclusive(x_886)) {
 lean_ctor_release(x_886, 0);
 lean_ctor_release(x_886, 1);
 x_888 = x_886;
} else {
 lean_dec_ref(x_886);
 x_888 = lean_box(0);
}
x_889 = lean_int_mul(x_829, x_820);
lean_dec(x_829);
lean_inc_ref(x_785);
x_890 = l_Int_Linear_Poly_mul(x_785, x_889);
lean_dec(x_889);
x_891 = lean_int_mul(x_830, x_790);
lean_dec(x_830);
lean_inc_ref(x_822);
x_892 = l_Int_Linear_Poly_mul(x_822, x_891);
lean_dec(x_891);
x_893 = lean_int_mul(x_790, x_820);
lean_dec(x_820);
lean_dec(x_790);
x_894 = l_Int_Linear_Poly_combine(x_890, x_892);
lean_inc(x_828);
if (lean_is_scalar(x_823)) {
 x_895 = lean_alloc_ctor(1, 3, 0);
} else {
 x_895 = x_823;
}
lean_ctor_set(x_895, 0, x_828);
lean_ctor_set(x_895, 1, x_795);
lean_ctor_set(x_895, 2, x_894);
lean_inc(x_817);
lean_inc_ref(x_793);
if (lean_is_scalar(x_888)) {
 x_896 = lean_alloc_ctor(4, 2, 0);
} else {
 x_896 = x_888;
 lean_ctor_set_tag(x_896, 4);
}
lean_ctor_set(x_896, 0, x_793);
lean_ctor_set(x_896, 1, x_817);
x_897 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_897, 0, x_893);
lean_ctor_set(x_897, 1, x_895);
lean_ctor_set(x_897, 2, x_896);
lean_inc(x_788);
lean_inc_ref(x_791);
lean_inc(x_794);
lean_inc_ref(x_783);
lean_inc(x_792);
lean_inc_ref(x_796);
lean_inc(x_787);
lean_inc(x_789);
x_898 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_897, x_789, x_787, x_796, x_792, x_783, x_794, x_791, x_788, x_887);
if (lean_obj_tag(x_898) == 0)
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; 
x_899 = lean_ctor_get(x_898, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_900 = x_898;
} else {
 lean_dec_ref(x_898);
 x_900 = lean_box(0);
}
x_901 = l_Int_Linear_Poly_mul(x_785, x_821);
lean_dec(x_821);
x_902 = lean_int_neg(x_784);
lean_dec(x_784);
x_903 = l_Int_Linear_Poly_mul(x_822, x_902);
lean_dec(x_902);
x_904 = l_Int_Linear_Poly_combine(x_901, x_903);
lean_inc(x_817);
if (lean_is_scalar(x_900)) {
 x_905 = lean_alloc_ctor(5, 2, 0);
} else {
 x_905 = x_900;
 lean_ctor_set_tag(x_905, 5);
}
lean_ctor_set(x_905, 0, x_793);
lean_ctor_set(x_905, 1, x_817);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 lean_ctor_release(x_817, 2);
 x_906 = x_817;
} else {
 lean_dec_ref(x_817);
 x_906 = lean_box(0);
}
if (lean_is_scalar(x_906)) {
 x_907 = lean_alloc_ctor(0, 3, 0);
} else {
 x_907 = x_906;
}
lean_ctor_set(x_907, 0, x_828);
lean_ctor_set(x_907, 1, x_904);
lean_ctor_set(x_907, 2, x_905);
x_1 = x_907;
x_2 = x_789;
x_3 = x_787;
x_4 = x_796;
x_5 = x_792;
x_6 = x_783;
x_7 = x_794;
x_8 = x_791;
x_9 = x_788;
x_10 = x_899;
goto _start;
}
else
{
lean_dec(x_828);
lean_dec_ref(x_822);
lean_dec(x_821);
lean_dec(x_817);
lean_dec_ref(x_796);
lean_dec(x_794);
lean_dec_ref(x_793);
lean_dec(x_792);
lean_dec_ref(x_791);
lean_dec(x_789);
lean_dec(x_788);
lean_dec(x_787);
lean_dec_ref(x_785);
lean_dec(x_784);
lean_dec_ref(x_783);
return x_898;
}
}
}
}
block_943:
{
lean_object* x_931; 
x_931 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_922, x_930);
if (lean_obj_tag(x_931) == 0)
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; uint8_t x_936; 
x_932 = lean_ctor_get(x_931, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_932, 6);
lean_inc_ref(x_933);
lean_dec(x_932);
x_934 = lean_ctor_get(x_931, 1);
lean_inc(x_934);
lean_dec_ref(x_931);
x_935 = lean_ctor_get(x_933, 2);
lean_inc(x_935);
x_936 = lean_nat_dec_lt(x_919, x_935);
lean_dec(x_935);
if (x_936 == 0)
{
lean_object* x_937; 
lean_dec_ref(x_933);
x_937 = l_outOfBounds___redArg(x_915);
x_782 = x_916;
x_783 = x_926;
x_784 = x_917;
x_785 = x_920;
x_786 = x_934;
x_787 = x_923;
x_788 = x_929;
x_789 = x_922;
x_790 = x_921;
x_791 = x_928;
x_792 = x_925;
x_793 = x_918;
x_794 = x_927;
x_795 = x_919;
x_796 = x_924;
x_797 = x_937;
goto block_909;
}
else
{
lean_object* x_938; 
x_938 = l_Lean_PersistentArray_get_x21___redArg(x_915, x_933, x_919);
x_782 = x_916;
x_783 = x_926;
x_784 = x_917;
x_785 = x_920;
x_786 = x_934;
x_787 = x_923;
x_788 = x_929;
x_789 = x_922;
x_790 = x_921;
x_791 = x_928;
x_792 = x_925;
x_793 = x_918;
x_794 = x_927;
x_795 = x_919;
x_796 = x_924;
x_797 = x_938;
goto block_909;
}
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
lean_dec(x_929);
lean_dec_ref(x_928);
lean_dec(x_927);
lean_dec_ref(x_926);
lean_dec(x_925);
lean_dec_ref(x_924);
lean_dec(x_923);
lean_dec(x_922);
lean_dec(x_921);
lean_dec_ref(x_920);
lean_dec(x_919);
lean_dec_ref(x_918);
lean_dec(x_917);
lean_dec_ref(x_916);
x_939 = lean_ctor_get(x_931, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_931, 1);
lean_inc(x_940);
if (lean_is_exclusive(x_931)) {
 lean_ctor_release(x_931, 0);
 lean_ctor_release(x_931, 1);
 x_941 = x_931;
} else {
 lean_dec_ref(x_931);
 x_941 = lean_box(0);
}
if (lean_is_scalar(x_941)) {
 x_942 = lean_alloc_ctor(1, 2, 0);
} else {
 x_942 = x_941;
}
lean_ctor_set(x_942, 0, x_939);
lean_ctor_set(x_942, 1, x_940);
return x_942;
}
}
block_1019:
{
lean_object* x_953; lean_object* x_954; 
x_953 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_950);
x_954 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_953, x_944, x_945, x_946, x_947, x_948, x_949, x_950, x_951, x_952);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; uint8_t x_959; 
x_955 = lean_ctor_get(x_954, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_954, 1);
lean_inc(x_956);
lean_dec_ref(x_954);
x_957 = lean_ctor_get(x_955, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_955, 1);
lean_inc_ref(x_958);
lean_inc(x_957);
x_959 = l_Int_Linear_Poly_isUnsatDvd(x_957, x_958);
if (x_959 == 0)
{
uint8_t x_960; 
x_960 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_955);
if (x_960 == 0)
{
lean_dec(x_914);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_961; 
lean_dec_ref(x_958);
lean_dec(x_957);
x_961 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_955, x_944, x_945, x_946, x_947, x_948, x_949, x_950, x_951, x_956);
lean_dec(x_951);
lean_dec_ref(x_950);
lean_dec(x_949);
lean_dec_ref(x_948);
lean_dec(x_947);
lean_dec_ref(x_946);
lean_dec(x_945);
lean_dec(x_944);
return x_961;
}
else
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; 
x_962 = lean_ctor_get(x_958, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_958, 1);
lean_inc(x_963);
x_964 = lean_ctor_get(x_958, 2);
lean_inc_ref(x_964);
lean_inc(x_955);
x_965 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_955, x_944, x_956);
if (lean_obj_tag(x_965) == 0)
{
lean_object* x_966; lean_object* x_967; uint8_t x_968; uint8_t x_969; uint8_t x_970; 
x_966 = lean_ctor_get(x_965, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_965, 1);
lean_inc(x_967);
lean_dec_ref(x_965);
x_968 = 0;
x_969 = lean_unbox(x_966);
lean_dec(x_966);
x_970 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_20_(x_969, x_968);
if (x_970 == 0)
{
x_916 = x_958;
x_917 = x_962;
x_918 = x_955;
x_919 = x_963;
x_920 = x_964;
x_921 = x_957;
x_922 = x_944;
x_923 = x_945;
x_924 = x_946;
x_925 = x_947;
x_926 = x_948;
x_927 = x_949;
x_928 = x_950;
x_929 = x_951;
x_930 = x_967;
goto block_943;
}
else
{
lean_object* x_971; 
x_971 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_963, x_944, x_967);
if (lean_obj_tag(x_971) == 0)
{
lean_object* x_972; 
x_972 = lean_ctor_get(x_971, 1);
lean_inc(x_972);
lean_dec_ref(x_971);
x_916 = x_958;
x_917 = x_962;
x_918 = x_955;
x_919 = x_963;
x_920 = x_964;
x_921 = x_957;
x_922 = x_944;
x_923 = x_945;
x_924 = x_946;
x_925 = x_947;
x_926 = x_948;
x_927 = x_949;
x_928 = x_950;
x_929 = x_951;
x_930 = x_972;
goto block_943;
}
else
{
lean_dec_ref(x_964);
lean_dec(x_963);
lean_dec(x_962);
lean_dec_ref(x_958);
lean_dec(x_957);
lean_dec(x_955);
lean_dec(x_951);
lean_dec_ref(x_950);
lean_dec(x_949);
lean_dec_ref(x_948);
lean_dec(x_947);
lean_dec_ref(x_946);
lean_dec(x_945);
lean_dec(x_944);
return x_971;
}
}
}
else
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; 
lean_dec_ref(x_964);
lean_dec(x_963);
lean_dec(x_962);
lean_dec_ref(x_958);
lean_dec(x_957);
lean_dec(x_955);
lean_dec(x_951);
lean_dec_ref(x_950);
lean_dec(x_949);
lean_dec_ref(x_948);
lean_dec(x_947);
lean_dec_ref(x_946);
lean_dec(x_945);
lean_dec(x_944);
x_973 = lean_ctor_get(x_965, 0);
lean_inc(x_973);
x_974 = lean_ctor_get(x_965, 1);
lean_inc(x_974);
if (lean_is_exclusive(x_965)) {
 lean_ctor_release(x_965, 0);
 lean_ctor_release(x_965, 1);
 x_975 = x_965;
} else {
 lean_dec_ref(x_965);
 x_975 = lean_box(0);
}
if (lean_is_scalar(x_975)) {
 x_976 = lean_alloc_ctor(1, 2, 0);
} else {
 x_976 = x_975;
}
lean_ctor_set(x_976, 0, x_973);
lean_ctor_set(x_976, 1, x_974);
return x_976;
}
}
}
else
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; uint8_t x_980; 
lean_dec_ref(x_958);
lean_dec(x_957);
lean_dec(x_947);
lean_dec_ref(x_946);
lean_dec(x_945);
x_977 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_978 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_977, x_950, x_956);
x_979 = lean_ctor_get(x_978, 0);
lean_inc(x_979);
x_980 = lean_unbox(x_979);
lean_dec(x_979);
if (x_980 == 0)
{
lean_object* x_981; 
lean_dec(x_955);
lean_dec(x_951);
lean_dec_ref(x_950);
lean_dec(x_949);
lean_dec_ref(x_948);
lean_dec(x_944);
lean_dec(x_914);
x_981 = lean_ctor_get(x_978, 1);
lean_inc(x_981);
lean_dec_ref(x_978);
x_183 = x_981;
goto block_186;
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_982 = lean_ctor_get(x_978, 1);
lean_inc(x_982);
if (lean_is_exclusive(x_978)) {
 lean_ctor_release(x_978, 0);
 lean_ctor_release(x_978, 1);
 x_983 = x_978;
} else {
 lean_dec_ref(x_978);
 x_983 = lean_box(0);
}
x_984 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_955, x_944, x_982);
lean_dec(x_944);
if (lean_obj_tag(x_984) == 0)
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; 
x_985 = lean_ctor_get(x_984, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_984, 1);
lean_inc(x_986);
lean_dec_ref(x_984);
x_987 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_983)) {
 x_988 = lean_alloc_ctor(7, 2, 0);
} else {
 x_988 = x_983;
 lean_ctor_set_tag(x_988, 7);
}
lean_ctor_set(x_988, 0, x_987);
lean_ctor_set(x_988, 1, x_985);
if (lean_is_scalar(x_914)) {
 x_989 = lean_alloc_ctor(7, 2, 0);
} else {
 x_989 = x_914;
 lean_ctor_set_tag(x_989, 7);
}
lean_ctor_set(x_989, 0, x_988);
lean_ctor_set(x_989, 1, x_987);
x_990 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_977, x_989, x_948, x_949, x_950, x_951, x_986);
lean_dec(x_951);
lean_dec_ref(x_950);
lean_dec(x_949);
lean_dec_ref(x_948);
x_991 = lean_ctor_get(x_990, 1);
lean_inc(x_991);
lean_dec_ref(x_990);
x_183 = x_991;
goto block_186;
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; 
lean_dec(x_983);
lean_dec(x_951);
lean_dec_ref(x_950);
lean_dec(x_949);
lean_dec_ref(x_948);
lean_dec(x_914);
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
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; uint8_t x_999; 
lean_dec_ref(x_958);
lean_dec(x_957);
x_996 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_997 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_996, x_950, x_956);
x_998 = lean_ctor_get(x_997, 0);
lean_inc(x_998);
x_999 = lean_unbox(x_998);
lean_dec(x_998);
if (x_999 == 0)
{
lean_object* x_1000; 
lean_dec(x_914);
x_1000 = lean_ctor_get(x_997, 1);
lean_inc(x_1000);
lean_dec_ref(x_997);
x_164 = x_955;
x_165 = x_944;
x_166 = x_945;
x_167 = x_946;
x_168 = x_947;
x_169 = x_948;
x_170 = x_949;
x_171 = x_950;
x_172 = x_951;
x_173 = x_1000;
goto block_182;
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
lean_inc(x_955);
x_1003 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_955, x_944, x_1001);
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
if (lean_is_scalar(x_914)) {
 x_1008 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1008 = x_914;
 lean_ctor_set_tag(x_1008, 7);
}
lean_ctor_set(x_1008, 0, x_1007);
lean_ctor_set(x_1008, 1, x_1006);
x_1009 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_996, x_1008, x_948, x_949, x_950, x_951, x_1005);
x_1010 = lean_ctor_get(x_1009, 1);
lean_inc(x_1010);
lean_dec_ref(x_1009);
x_164 = x_955;
x_165 = x_944;
x_166 = x_945;
x_167 = x_946;
x_168 = x_947;
x_169 = x_948;
x_170 = x_949;
x_171 = x_950;
x_172 = x_951;
x_173 = x_1010;
goto block_182;
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; 
lean_dec(x_1002);
lean_dec(x_955);
lean_dec(x_951);
lean_dec_ref(x_950);
lean_dec(x_949);
lean_dec_ref(x_948);
lean_dec(x_947);
lean_dec_ref(x_946);
lean_dec(x_945);
lean_dec(x_944);
lean_dec(x_914);
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
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
lean_dec(x_951);
lean_dec_ref(x_950);
lean_dec(x_949);
lean_dec_ref(x_948);
lean_dec(x_947);
lean_dec_ref(x_946);
lean_dec(x_945);
lean_dec(x_944);
lean_dec(x_914);
x_1015 = lean_ctor_get(x_954, 0);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_954, 1);
lean_inc(x_1016);
if (lean_is_exclusive(x_954)) {
 lean_ctor_release(x_954, 0);
 lean_ctor_release(x_954, 1);
 x_1017 = x_954;
} else {
 lean_dec_ref(x_954);
 x_1017 = lean_box(0);
}
if (lean_is_scalar(x_1017)) {
 x_1018 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1018 = x_1017;
}
lean_ctor_set(x_1018, 0, x_1015);
lean_ctor_set(x_1018, 1, x_1016);
return x_1018;
}
}
}
else
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
lean_dec_ref(x_773);
lean_dec(x_771);
lean_dec(x_769);
lean_dec(x_768);
lean_dec(x_767);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_762);
lean_dec(x_761);
lean_dec_ref(x_760);
lean_dec_ref(x_759);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1033 = lean_ctor_get(x_775, 1);
lean_inc(x_1033);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_1034 = x_775;
} else {
 lean_dec_ref(x_775);
 x_1034 = lean_box(0);
}
x_1035 = lean_box(0);
if (lean_is_scalar(x_1034)) {
 x_1036 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1036 = x_1034;
}
lean_ctor_set(x_1036, 0, x_1035);
lean_ctor_set(x_1036, 1, x_1033);
return x_1036;
}
}
else
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
lean_dec_ref(x_773);
lean_dec(x_771);
lean_dec(x_769);
lean_dec(x_768);
lean_dec(x_767);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_762);
lean_dec(x_761);
lean_dec_ref(x_760);
lean_dec_ref(x_759);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1037 = lean_ctor_get(x_775, 0);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_775, 1);
lean_inc(x_1038);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_1039 = x_775;
} else {
 lean_dec_ref(x_775);
 x_1039 = lean_box(0);
}
if (lean_is_scalar(x_1039)) {
 x_1040 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1040 = x_1039;
}
lean_ctor_set(x_1040, 0, x_1037);
lean_ctor_set(x_1040, 1, x_1038);
return x_1040;
}
}
else
{
lean_object* x_1041; 
lean_dec_ref(x_773);
lean_dec(x_771);
lean_dec(x_769);
lean_dec(x_768);
lean_dec(x_767);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_763);
lean_dec(x_762);
lean_dec(x_761);
lean_dec_ref(x_760);
lean_dec_ref(x_759);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1041 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_764, x_10);
return x_1041;
}
}
block_163:
{
lean_object* x_20; 
x_20 = l_Int_Linear_Poly_updateOccs___redArg(x_11, x_14, x_15, x_16, x_17, x_18, x_19);
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
x_34 = l_Lean_PersistentArray_set___redArg(x_32, x_13, x_33);
lean_dec(x_13);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
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
x_57 = lean_ctor_get_uint8(x_25, sizeof(void*)*21);
x_58 = lean_ctor_get(x_25, 15);
x_59 = lean_ctor_get(x_25, 16);
x_60 = lean_ctor_get(x_25, 17);
x_61 = lean_ctor_get(x_25, 18);
x_62 = lean_ctor_get(x_25, 19);
x_63 = lean_ctor_get(x_25, 20);
x_64 = lean_ctor_get_uint8(x_25, sizeof(void*)*21 + 1);
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
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_12);
x_66 = l_Lean_PersistentArray_set___redArg(x_48, x_13, x_65);
lean_dec(x_13);
x_67 = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(x_67, 0, x_42);
lean_ctor_set(x_67, 1, x_43);
lean_ctor_set(x_67, 2, x_44);
lean_ctor_set(x_67, 3, x_45);
lean_ctor_set(x_67, 4, x_46);
lean_ctor_set(x_67, 5, x_47);
lean_ctor_set(x_67, 6, x_66);
lean_ctor_set(x_67, 7, x_49);
lean_ctor_set(x_67, 8, x_50);
lean_ctor_set(x_67, 9, x_51);
lean_ctor_set(x_67, 10, x_52);
lean_ctor_set(x_67, 11, x_53);
lean_ctor_set(x_67, 12, x_54);
lean_ctor_set(x_67, 13, x_55);
lean_ctor_set(x_67, 14, x_56);
lean_ctor_set(x_67, 15, x_58);
lean_ctor_set(x_67, 16, x_59);
lean_ctor_set(x_67, 17, x_60);
lean_ctor_set(x_67, 18, x_61);
lean_ctor_set(x_67, 19, x_62);
lean_ctor_set(x_67, 20, x_63);
lean_ctor_set_uint8(x_67, sizeof(void*)*21, x_57);
lean_ctor_set_uint8(x_67, sizeof(void*)*21 + 1, x_64);
lean_ctor_set(x_24, 1, x_67);
x_68 = lean_st_ref_set(x_14, x_23, x_26);
lean_dec(x_14);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_73 = lean_ctor_get(x_24, 0);
x_74 = lean_ctor_get(x_24, 2);
x_75 = lean_ctor_get(x_24, 3);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
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
x_91 = lean_ctor_get_uint8(x_25, sizeof(void*)*21);
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
x_98 = lean_ctor_get_uint8(x_25, sizeof(void*)*21 + 1);
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
 x_99 = x_25;
} else {
 lean_dec_ref(x_25);
 x_99 = lean_box(0);
}
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_12);
x_101 = l_Lean_PersistentArray_set___redArg(x_82, x_13, x_100);
lean_dec(x_13);
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(0, 21, 2);
} else {
 x_102 = x_99;
}
lean_ctor_set(x_102, 0, x_76);
lean_ctor_set(x_102, 1, x_77);
lean_ctor_set(x_102, 2, x_78);
lean_ctor_set(x_102, 3, x_79);
lean_ctor_set(x_102, 4, x_80);
lean_ctor_set(x_102, 5, x_81);
lean_ctor_set(x_102, 6, x_101);
lean_ctor_set(x_102, 7, x_83);
lean_ctor_set(x_102, 8, x_84);
lean_ctor_set(x_102, 9, x_85);
lean_ctor_set(x_102, 10, x_86);
lean_ctor_set(x_102, 11, x_87);
lean_ctor_set(x_102, 12, x_88);
lean_ctor_set(x_102, 13, x_89);
lean_ctor_set(x_102, 14, x_90);
lean_ctor_set(x_102, 15, x_92);
lean_ctor_set(x_102, 16, x_93);
lean_ctor_set(x_102, 17, x_94);
lean_ctor_set(x_102, 18, x_95);
lean_ctor_set(x_102, 19, x_96);
lean_ctor_set(x_102, 20, x_97);
lean_ctor_set_uint8(x_102, sizeof(void*)*21, x_91);
lean_ctor_set_uint8(x_102, sizeof(void*)*21 + 1, x_98);
x_103 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_103, 0, x_73);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_74);
lean_ctor_set(x_103, 3, x_75);
lean_ctor_set(x_23, 14, x_103);
x_104 = lean_st_ref_set(x_14, x_23, x_26);
lean_dec(x_14);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
x_107 = lean_box(0);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_109 = lean_ctor_get(x_23, 0);
x_110 = lean_ctor_get(x_23, 1);
x_111 = lean_ctor_get(x_23, 2);
x_112 = lean_ctor_get(x_23, 3);
x_113 = lean_ctor_get(x_23, 4);
x_114 = lean_ctor_get(x_23, 5);
x_115 = lean_ctor_get(x_23, 6);
x_116 = lean_ctor_get(x_23, 7);
x_117 = lean_ctor_get_uint8(x_23, sizeof(void*)*16);
x_118 = lean_ctor_get(x_23, 8);
x_119 = lean_ctor_get(x_23, 9);
x_120 = lean_ctor_get(x_23, 10);
x_121 = lean_ctor_get(x_23, 11);
x_122 = lean_ctor_get(x_23, 12);
x_123 = lean_ctor_get(x_23, 13);
x_124 = lean_ctor_get(x_23, 15);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_23);
x_125 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_24, 3);
lean_inc_ref(x_127);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 x_128 = x_24;
} else {
 lean_dec_ref(x_24);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_25, 4);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_25, 5);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_25, 6);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_25, 7);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_25, 8);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_25, 9);
lean_inc_ref(x_138);
x_139 = lean_ctor_get(x_25, 10);
lean_inc_ref(x_139);
x_140 = lean_ctor_get(x_25, 11);
lean_inc(x_140);
x_141 = lean_ctor_get(x_25, 12);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_25, 13);
lean_inc_ref(x_142);
x_143 = lean_ctor_get(x_25, 14);
lean_inc(x_143);
x_144 = lean_ctor_get_uint8(x_25, sizeof(void*)*21);
x_145 = lean_ctor_get(x_25, 15);
lean_inc(x_145);
x_146 = lean_ctor_get(x_25, 16);
lean_inc_ref(x_146);
x_147 = lean_ctor_get(x_25, 17);
lean_inc_ref(x_147);
x_148 = lean_ctor_get(x_25, 18);
lean_inc_ref(x_148);
x_149 = lean_ctor_get(x_25, 19);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_25, 20);
lean_inc_ref(x_150);
x_151 = lean_ctor_get_uint8(x_25, sizeof(void*)*21 + 1);
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
 x_152 = x_25;
} else {
 lean_dec_ref(x_25);
 x_152 = lean_box(0);
}
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_12);
x_154 = l_Lean_PersistentArray_set___redArg(x_135, x_13, x_153);
lean_dec(x_13);
if (lean_is_scalar(x_152)) {
 x_155 = lean_alloc_ctor(0, 21, 2);
} else {
 x_155 = x_152;
}
lean_ctor_set(x_155, 0, x_129);
lean_ctor_set(x_155, 1, x_130);
lean_ctor_set(x_155, 2, x_131);
lean_ctor_set(x_155, 3, x_132);
lean_ctor_set(x_155, 4, x_133);
lean_ctor_set(x_155, 5, x_134);
lean_ctor_set(x_155, 6, x_154);
lean_ctor_set(x_155, 7, x_136);
lean_ctor_set(x_155, 8, x_137);
lean_ctor_set(x_155, 9, x_138);
lean_ctor_set(x_155, 10, x_139);
lean_ctor_set(x_155, 11, x_140);
lean_ctor_set(x_155, 12, x_141);
lean_ctor_set(x_155, 13, x_142);
lean_ctor_set(x_155, 14, x_143);
lean_ctor_set(x_155, 15, x_145);
lean_ctor_set(x_155, 16, x_146);
lean_ctor_set(x_155, 17, x_147);
lean_ctor_set(x_155, 18, x_148);
lean_ctor_set(x_155, 19, x_149);
lean_ctor_set(x_155, 20, x_150);
lean_ctor_set_uint8(x_155, sizeof(void*)*21, x_144);
lean_ctor_set_uint8(x_155, sizeof(void*)*21 + 1, x_151);
if (lean_is_scalar(x_128)) {
 x_156 = lean_alloc_ctor(0, 4, 0);
} else {
 x_156 = x_128;
}
lean_ctor_set(x_156, 0, x_125);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set(x_156, 2, x_126);
lean_ctor_set(x_156, 3, x_127);
x_157 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_157, 0, x_109);
lean_ctor_set(x_157, 1, x_110);
lean_ctor_set(x_157, 2, x_111);
lean_ctor_set(x_157, 3, x_112);
lean_ctor_set(x_157, 4, x_113);
lean_ctor_set(x_157, 5, x_114);
lean_ctor_set(x_157, 6, x_115);
lean_ctor_set(x_157, 7, x_116);
lean_ctor_set(x_157, 8, x_118);
lean_ctor_set(x_157, 9, x_119);
lean_ctor_set(x_157, 10, x_120);
lean_ctor_set(x_157, 11, x_121);
lean_ctor_set(x_157, 12, x_122);
lean_ctor_set(x_157, 13, x_123);
lean_ctor_set(x_157, 14, x_156);
lean_ctor_set(x_157, 15, x_124);
lean_ctor_set_uint8(x_157, sizeof(void*)*16, x_117);
x_158 = lean_st_ref_set(x_14, x_157, x_26);
lean_dec(x_14);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_160 = x_158;
} else {
 lean_dec_ref(x_158);
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
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
return x_20;
}
}
block_182:
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_164);
x_175 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_174, x_165, x_166, x_167, x_168, x_169, x_170, x_171, x_172, x_173);
if (lean_obj_tag(x_175) == 0)
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_175, 0);
lean_dec(x_177);
x_178 = lean_box(0);
lean_ctor_set(x_175, 0, x_178);
return x_175;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
lean_dec(x_175);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
return x_175;
}
}
block_186:
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Int_Linear_Poly_normCommRing_x3f(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
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
lean_dec(x_11);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_reflBoolTrue;
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
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
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
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_34 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_35 = l_Lean_Expr_isConstOf(x_33, x_34);
lean_dec_ref(x_33);
if (x_35 == 0)
{
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
lean_object* x_36; 
lean_dec(x_18);
x_36 = l_Lean_Meta_isInstDvdInt___redArg(x_30, x_7, x_17);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_36, 0, x_41);
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec_ref(x_36);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_27);
x_46 = l_Lean_Meta_getIntValue_x3f(x_27, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_2);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_50, sizeof(void*)*7 + 11);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec_ref(x_49);
x_11 = x_52;
goto block_14;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec_ref(x_49);
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
x_55 = l_Lean_indentExpr(x_1);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_Grind_reportIssue(x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_53);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec_ref(x_59);
x_11 = x_60;
goto block_14;
}
else
{
return x_59;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_61 = !lean_is_exclusive(x_49);
if (x_61 == 0)
{
return x_49;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_49, 0);
x_63 = lean_ctor_get(x_49, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_49);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_46, 1);
lean_inc(x_65);
lean_dec_ref(x_46);
x_66 = !lean_is_exclusive(x_47);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_47, 0);
lean_inc_ref(x_1);
x_68 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_65);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_free_object(x_47);
lean_dec(x_67);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec_ref(x_68);
lean_inc_ref(x_1);
x_72 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_71);
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
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_88 = l_Lean_mkApp4(x_85, x_27, x_24, x_86, x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Lean_Meta_Grind_pushNewFact(x_88, x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_84);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
lean_object* x_99; lean_object* x_100; 
lean_dec_ref(x_27);
x_99 = lean_ctor_get(x_68, 1);
lean_inc(x_99);
lean_dec_ref(x_68);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_100 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec_ref(x_100);
lean_ctor_set_tag(x_47, 0);
lean_ctor_set(x_47, 0, x_1);
x_103 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_103, 0, x_67);
lean_ctor_set(x_103, 1, x_101);
lean_ctor_set(x_103, 2, x_47);
x_104 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
return x_104;
}
else
{
uint8_t x_105; 
lean_free_object(x_47);
lean_dec(x_67);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_105 = !lean_is_exclusive(x_100);
if (x_105 == 0)
{
return x_100;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_100, 0);
x_107 = lean_ctor_get(x_100, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_100);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
else
{
uint8_t x_109; 
lean_free_object(x_47);
lean_dec(x_67);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_109 = !lean_is_exclusive(x_68);
if (x_109 == 0)
{
return x_68;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_68, 0);
x_111 = lean_ctor_get(x_68, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_68);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_47, 0);
lean_inc(x_113);
lean_dec(x_47);
lean_inc_ref(x_1);
x_114 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_65);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_113);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec_ref(x_114);
lean_inc_ref(x_1);
x_118 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_122 = x_118;
} else {
 lean_dec_ref(x_118);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_118, 1);
lean_inc(x_125);
lean_dec_ref(x_118);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_126 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec_ref(x_126);
x_129 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_130 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
x_131 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_127);
x_132 = l_Lean_mkApp4(x_129, x_27, x_24, x_130, x_131);
x_133 = lean_unsigned_to_nat(0u);
x_134 = l_Lean_Meta_Grind_pushNewFact(x_132, x_133, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_128);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_135 = lean_ctor_get(x_126, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_126, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_137 = x_126;
} else {
 lean_dec_ref(x_126);
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
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_139 = lean_ctor_get(x_118, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_118, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_141 = x_118;
} else {
 lean_dec_ref(x_118);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec_ref(x_27);
x_143 = lean_ctor_get(x_114, 1);
lean_inc(x_143);
lean_dec_ref(x_114);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_144 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec_ref(x_144);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_1);
x_148 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_148, 0, x_113);
lean_ctor_set(x_148, 1, x_145);
lean_ctor_set(x_148, 2, x_147);
x_149 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_148, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_146);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_113);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_113);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_154 = lean_ctor_get(x_114, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_114, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_156 = x_114;
} else {
 lean_dec_ref(x_114);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
}
else
{
uint8_t x_158; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_158 = !lean_is_exclusive(x_46);
if (x_158 == 0)
{
return x_46;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_46, 0);
x_160 = lean_ctor_get(x_46, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_46);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
else
{
uint8_t x_162; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_162 = !lean_is_exclusive(x_36);
if (x_162 == 0)
{
return x_36;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_36, 0);
x_164 = lean_ctor_get(x_36, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_36);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
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
uint8_t x_166; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_166 = !lean_is_exclusive(x_15);
if (x_166 == 0)
{
return x_15;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_15, 0);
x_168 = lean_ctor_get(x_15, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_15);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_21);
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
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
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
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
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
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_32 = l_Lean_Expr_isConstOf(x_30, x_31);
lean_dec_ref(x_30);
if (x_32 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
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
lean_object* x_33; 
x_33 = l_Lean_Meta_isInstDvdNat___redArg(x_27, x_7, x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_33, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec_ref(x_33);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_43 = l_Lean_Meta_getNatValue_x3f(x_24, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec(x_2);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*7 + 11);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec_ref(x_46);
x_15 = x_49;
goto block_18;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec_ref(x_46);
x_51 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
x_52 = l_Lean_indentExpr(x_1);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Meta_Grind_reportIssue(x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec_ref(x_56);
x_15 = x_57;
goto block_18;
}
else
{
return x_56;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_58 = !lean_is_exclusive(x_46);
if (x_58 == 0)
{
return x_46;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_46, 0);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_46);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_43, 1);
lean_inc(x_62);
lean_dec_ref(x_43);
x_63 = lean_ctor_get(x_44, 0);
lean_inc(x_63);
lean_dec_ref(x_44);
lean_inc_ref(x_1);
x_64 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec_ref(x_64);
lean_inc_ref(x_1);
x_68 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_67);
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
lean_dec_ref(x_24);
lean_dec_ref(x_21);
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
x_83 = l_Lean_mkApp3(x_81, x_24, x_21, x_82);
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Lean_Meta_Grind_pushNewFact(x_83, x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_80);
return x_85;
}
else
{
uint8_t x_86; 
lean_dec_ref(x_24);
lean_dec_ref(x_21);
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
lean_dec_ref(x_24);
lean_dec_ref(x_21);
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
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_64, 1);
lean_inc(x_94);
lean_dec_ref(x_64);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_24);
x_95 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_21);
x_100 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_97);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec_ref(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_102);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec_ref(x_105);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_103);
x_108 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_103, x_106, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec_ref(x_108);
x_111 = l_Int_Linear_Expr_norm(x_109);
x_112 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
x_113 = l_Lean_mkApp6(x_112, x_24, x_21, x_98, x_103, x_99, x_104);
lean_inc(x_63);
x_114 = lean_nat_to_int(x_63);
x_115 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_115, 0, x_1);
lean_ctor_set(x_115, 1, x_113);
lean_ctor_set(x_115, 2, x_63);
lean_ctor_set(x_115, 3, x_109);
x_116 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_111);
lean_ctor_set(x_116, 2, x_115);
x_117 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_116, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_110);
return x_117;
}
else
{
uint8_t x_118; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_63);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_118 = !lean_is_exclusive(x_108);
if (x_118 == 0)
{
return x_108;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_108, 0);
x_120 = lean_ctor_get(x_108, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_108);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_63);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_122 = !lean_is_exclusive(x_105);
if (x_122 == 0)
{
return x_105;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_105, 0);
x_124 = lean_ctor_get(x_105, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_105);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_63);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_126 = !lean_is_exclusive(x_100);
if (x_126 == 0)
{
return x_100;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_100, 0);
x_128 = lean_ctor_get(x_100, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_100);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_63);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_130 = !lean_is_exclusive(x_95);
if (x_130 == 0)
{
return x_95;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_95, 0);
x_132 = lean_ctor_get(x_95, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_95);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_63);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_134 = !lean_is_exclusive(x_64);
if (x_134 == 0)
{
return x_64;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_64, 0);
x_136 = lean_ctor_get(x_64, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_64);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
else
{
uint8_t x_138; 
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_138 = !lean_is_exclusive(x_43);
if (x_138 == 0)
{
return x_43;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_43, 0);
x_140 = lean_ctor_get(x_43, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_43);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
else
{
uint8_t x_142; 
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_142 = !lean_is_exclusive(x_33);
if (x_142 == 0)
{
return x_33;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_33, 0);
x_144 = lean_ctor_get(x_33, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_33);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
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
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 20);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_36);
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_34);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_39 = l_Lean_Expr_isConstOf(x_37, x_38);
lean_dec_ref(x_37);
if (x_39 == 0)
{
lean_dec_ref(x_36);
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
lean_object* x_40; uint8_t x_41; 
lean_dec(x_24);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0;
x_41 = l_Lean_Expr_isConstOf(x_36, x_40);
lean_dec_ref(x_36);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2963_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3, x_1);
return x_4;
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
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2963_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

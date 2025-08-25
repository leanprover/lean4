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
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqLBool____x40_Lean_Data_LBool_27903016____hygCtx___hyg_9_(uint8_t, uint8_t);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_186; uint8_t x_190; 
x_190 = !lean_is_exclusive(x_8);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_191 = lean_ctor_get(x_8, 0);
x_192 = lean_ctor_get(x_8, 1);
x_193 = lean_ctor_get(x_8, 2);
x_194 = lean_ctor_get(x_8, 3);
x_195 = lean_ctor_get(x_8, 4);
x_196 = lean_ctor_get(x_8, 5);
x_197 = lean_ctor_get(x_8, 6);
x_198 = lean_ctor_get(x_8, 7);
x_199 = lean_ctor_get(x_8, 8);
x_200 = lean_ctor_get(x_8, 9);
x_201 = lean_ctor_get(x_8, 10);
x_202 = lean_ctor_get(x_8, 11);
x_203 = lean_ctor_get(x_8, 12);
x_204 = lean_ctor_get(x_8, 13);
x_205 = lean_nat_dec_eq(x_194, x_195);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; uint8_t x_208; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_unbox(x_207);
lean_dec(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; uint8_t x_744; 
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
lean_dec_ref(x_206);
x_210 = lean_unsigned_to_nat(1u);
x_211 = lean_nat_add(x_194, x_210);
lean_dec(x_194);
lean_ctor_set(x_8, 3, x_211);
x_608 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_609 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_608, x_8, x_209);
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_612 = x_609;
} else {
 lean_dec_ref(x_609);
 x_612 = lean_box(0);
}
x_613 = lean_box(0);
x_744 = lean_unbox(x_610);
lean_dec(x_610);
if (x_744 == 0)
{
x_642 = x_2;
x_643 = x_3;
x_644 = x_4;
x_645 = x_5;
x_646 = x_6;
x_647 = x_7;
x_648 = x_8;
x_649 = x_9;
x_650 = x_611;
goto block_743;
}
else
{
lean_object* x_745; 
lean_inc_ref(x_1);
x_745 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_611);
if (lean_obj_tag(x_745) == 0)
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_745, 1);
lean_inc(x_747);
lean_dec_ref(x_745);
x_748 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_749 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_749, 0, x_748);
lean_ctor_set(x_749, 1, x_746);
x_750 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_750, 0, x_749);
lean_ctor_set(x_750, 1, x_748);
x_751 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_608, x_750, x_6, x_7, x_8, x_9, x_747);
x_752 = lean_ctor_get(x_751, 1);
lean_inc(x_752);
lean_dec_ref(x_751);
x_642 = x_2;
x_643 = x_3;
x_644 = x_4;
x_645 = x_5;
x_646 = x_6;
x_647 = x_7;
x_648 = x_8;
x_649 = x_9;
x_650 = x_752;
goto block_743;
}
else
{
uint8_t x_753; 
lean_dec(x_612);
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_753 = !lean_is_exclusive(x_745);
if (x_753 == 0)
{
return x_745;
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_754 = lean_ctor_get(x_745, 0);
x_755 = lean_ctor_get(x_745, 1);
lean_inc(x_755);
lean_inc(x_754);
lean_dec(x_745);
x_756 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_756, 0, x_754);
lean_ctor_set(x_756, 1, x_755);
return x_756;
}
}
}
block_607:
{
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec(x_212);
x_228 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_229 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_228, x_225, x_219);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_unbox(x_230);
lean_dec(x_230);
if (x_231 == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_dec_ref(x_229);
x_11 = x_218;
x_12 = x_220;
x_13 = x_217;
x_14 = x_216;
x_15 = x_226;
x_16 = x_224;
x_17 = x_225;
x_18 = x_221;
x_19 = x_232;
goto block_166;
}
else
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_229);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_229, 1);
x_235 = lean_ctor_get(x_229, 0);
lean_dec(x_235);
lean_inc_ref(x_218);
x_236 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_218, x_216, x_234);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec_ref(x_236);
x_239 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_229, 7);
lean_ctor_set(x_229, 1, x_237);
lean_ctor_set(x_229, 0, x_239);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_229);
lean_ctor_set(x_240, 1, x_239);
x_241 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_228, x_240, x_226, x_224, x_225, x_221, x_238);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec_ref(x_241);
x_11 = x_218;
x_12 = x_220;
x_13 = x_217;
x_14 = x_216;
x_15 = x_226;
x_16 = x_224;
x_17 = x_225;
x_18 = x_221;
x_19 = x_242;
goto block_166;
}
else
{
uint8_t x_243; 
lean_free_object(x_229);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_218);
lean_dec_ref(x_217);
lean_dec(x_216);
x_243 = !lean_is_exclusive(x_236);
if (x_243 == 0)
{
return x_236;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_236, 0);
x_245 = lean_ctor_get(x_236, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_236);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
else
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_229, 1);
lean_inc(x_247);
lean_dec(x_229);
lean_inc_ref(x_218);
x_248 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_218, x_216, x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec_ref(x_248);
x_251 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_252 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_249);
x_253 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_251);
x_254 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_228, x_253, x_226, x_224, x_225, x_221, x_250);
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec_ref(x_254);
x_11 = x_218;
x_12 = x_220;
x_13 = x_217;
x_14 = x_216;
x_15 = x_226;
x_16 = x_224;
x_17 = x_225;
x_18 = x_221;
x_19 = x_255;
goto block_166;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_218);
lean_dec_ref(x_217);
lean_dec(x_216);
x_256 = lean_ctor_get(x_248, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_248, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_258 = x_248;
} else {
 lean_dec_ref(x_248);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
}
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_dec_ref(x_217);
x_260 = lean_ctor_get(x_227, 0);
lean_inc(x_260);
lean_dec_ref(x_227);
x_261 = lean_ctor_get(x_260, 1);
lean_inc_ref(x_261);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; 
lean_dec_ref(x_261);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_218);
lean_dec(x_215);
lean_dec(x_213);
x_262 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_260, x_216, x_212, x_214, x_223, x_226, x_224, x_225, x_221, x_219);
lean_dec(x_221);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_226);
lean_dec(x_223);
lean_dec_ref(x_214);
lean_dec(x_212);
lean_dec(x_216);
return x_262;
}
else
{
uint8_t x_263; 
x_263 = !lean_is_exclusive(x_261);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_264 = lean_ctor_get(x_260, 0);
x_265 = lean_ctor_get(x_261, 0);
x_266 = lean_ctor_get(x_261, 2);
x_267 = lean_ctor_get(x_261, 1);
lean_dec(x_267);
x_268 = lean_int_mul(x_213, x_264);
x_269 = lean_int_mul(x_265, x_215);
x_270 = l_Lean_Meta_Grind_Arith_gcdExt(x_268, x_269);
lean_dec(x_269);
lean_dec(x_268);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
lean_dec_ref(x_270);
x_273 = lean_ctor_get(x_271, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_271, 1);
lean_inc(x_274);
lean_dec(x_271);
x_275 = lean_st_ref_take(x_216, x_219);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_276, 14);
lean_inc_ref(x_277);
x_278 = lean_ctor_get(x_277, 1);
lean_inc_ref(x_278);
x_279 = lean_ctor_get(x_275, 1);
lean_inc(x_279);
lean_dec_ref(x_275);
x_280 = !lean_is_exclusive(x_276);
if (x_280 == 0)
{
lean_object* x_281; uint8_t x_282; 
x_281 = lean_ctor_get(x_276, 14);
lean_dec(x_281);
x_282 = !lean_is_exclusive(x_277);
if (x_282 == 0)
{
lean_object* x_283; uint8_t x_284; 
x_283 = lean_ctor_get(x_277, 1);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_278);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_285 = lean_ctor_get(x_278, 6);
x_286 = lean_box(0);
x_287 = l_Lean_PersistentArray_set___redArg(x_285, x_220, x_286);
lean_ctor_set(x_278, 6, x_287);
x_288 = lean_st_ref_set(x_216, x_276, x_279);
x_289 = !lean_is_exclusive(x_288);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_290 = lean_ctor_get(x_288, 1);
x_291 = lean_ctor_get(x_288, 0);
lean_dec(x_291);
x_292 = lean_int_mul(x_273, x_264);
lean_dec(x_273);
lean_inc_ref(x_222);
x_293 = l_Int_Linear_Poly_mul(x_222, x_292);
lean_dec(x_292);
x_294 = lean_int_mul(x_274, x_215);
lean_dec(x_274);
lean_inc_ref(x_266);
x_295 = l_Int_Linear_Poly_mul(x_266, x_294);
lean_dec(x_294);
x_296 = lean_int_mul(x_215, x_264);
lean_dec(x_215);
x_297 = l_Int_Linear_Poly_combine(x_293, x_295);
lean_inc(x_272);
lean_ctor_set(x_261, 2, x_297);
lean_ctor_set(x_261, 1, x_220);
lean_ctor_set(x_261, 0, x_272);
lean_inc(x_260);
lean_inc_ref(x_218);
lean_ctor_set_tag(x_288, 4);
lean_ctor_set(x_288, 1, x_260);
lean_ctor_set(x_288, 0, x_218);
x_298 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_261);
lean_ctor_set(x_298, 2, x_288);
lean_inc(x_221);
lean_inc_ref(x_225);
lean_inc(x_224);
lean_inc_ref(x_226);
lean_inc(x_223);
lean_inc_ref(x_214);
lean_inc(x_212);
lean_inc(x_216);
x_299 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_298, x_216, x_212, x_214, x_223, x_226, x_224, x_225, x_221, x_290);
if (lean_obj_tag(x_299) == 0)
{
uint8_t x_300; 
x_300 = !lean_is_exclusive(x_299);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_301 = lean_ctor_get(x_299, 1);
x_302 = lean_ctor_get(x_299, 0);
lean_dec(x_302);
x_303 = l_Int_Linear_Poly_mul(x_222, x_265);
lean_dec(x_265);
x_304 = lean_int_neg(x_213);
lean_dec(x_213);
x_305 = l_Int_Linear_Poly_mul(x_266, x_304);
lean_dec(x_304);
x_306 = l_Int_Linear_Poly_combine(x_303, x_305);
lean_inc(x_260);
lean_ctor_set_tag(x_299, 5);
lean_ctor_set(x_299, 1, x_260);
lean_ctor_set(x_299, 0, x_218);
x_307 = !lean_is_exclusive(x_260);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_260, 2);
lean_dec(x_308);
x_309 = lean_ctor_get(x_260, 1);
lean_dec(x_309);
x_310 = lean_ctor_get(x_260, 0);
lean_dec(x_310);
lean_ctor_set(x_260, 2, x_299);
lean_ctor_set(x_260, 1, x_306);
lean_ctor_set(x_260, 0, x_272);
x_1 = x_260;
x_2 = x_216;
x_3 = x_212;
x_4 = x_214;
x_5 = x_223;
x_6 = x_226;
x_7 = x_224;
x_8 = x_225;
x_9 = x_221;
x_10 = x_301;
goto _start;
}
else
{
lean_object* x_312; 
lean_dec(x_260);
x_312 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_312, 0, x_272);
lean_ctor_set(x_312, 1, x_306);
lean_ctor_set(x_312, 2, x_299);
x_1 = x_312;
x_2 = x_216;
x_3 = x_212;
x_4 = x_214;
x_5 = x_223;
x_6 = x_226;
x_7 = x_224;
x_8 = x_225;
x_9 = x_221;
x_10 = x_301;
goto _start;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_314 = lean_ctor_get(x_299, 1);
lean_inc(x_314);
lean_dec(x_299);
x_315 = l_Int_Linear_Poly_mul(x_222, x_265);
lean_dec(x_265);
x_316 = lean_int_neg(x_213);
lean_dec(x_213);
x_317 = l_Int_Linear_Poly_mul(x_266, x_316);
lean_dec(x_316);
x_318 = l_Int_Linear_Poly_combine(x_315, x_317);
lean_inc(x_260);
x_319 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_319, 0, x_218);
lean_ctor_set(x_319, 1, x_260);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 x_320 = x_260;
} else {
 lean_dec_ref(x_260);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(0, 3, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_272);
lean_ctor_set(x_321, 1, x_318);
lean_ctor_set(x_321, 2, x_319);
x_1 = x_321;
x_2 = x_216;
x_3 = x_212;
x_4 = x_214;
x_5 = x_223;
x_6 = x_226;
x_7 = x_224;
x_8 = x_225;
x_9 = x_221;
x_10 = x_314;
goto _start;
}
}
else
{
lean_dec(x_272);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec(x_260);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_221);
lean_dec_ref(x_218);
lean_dec(x_216);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec(x_212);
return x_299;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_323 = lean_ctor_get(x_288, 1);
lean_inc(x_323);
lean_dec(x_288);
x_324 = lean_int_mul(x_273, x_264);
lean_dec(x_273);
lean_inc_ref(x_222);
x_325 = l_Int_Linear_Poly_mul(x_222, x_324);
lean_dec(x_324);
x_326 = lean_int_mul(x_274, x_215);
lean_dec(x_274);
lean_inc_ref(x_266);
x_327 = l_Int_Linear_Poly_mul(x_266, x_326);
lean_dec(x_326);
x_328 = lean_int_mul(x_215, x_264);
lean_dec(x_215);
x_329 = l_Int_Linear_Poly_combine(x_325, x_327);
lean_inc(x_272);
lean_ctor_set(x_261, 2, x_329);
lean_ctor_set(x_261, 1, x_220);
lean_ctor_set(x_261, 0, x_272);
lean_inc(x_260);
lean_inc_ref(x_218);
x_330 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_330, 0, x_218);
lean_ctor_set(x_330, 1, x_260);
x_331 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_261);
lean_ctor_set(x_331, 2, x_330);
lean_inc(x_221);
lean_inc_ref(x_225);
lean_inc(x_224);
lean_inc_ref(x_226);
lean_inc(x_223);
lean_inc_ref(x_214);
lean_inc(x_212);
lean_inc(x_216);
x_332 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_331, x_216, x_212, x_214, x_223, x_226, x_224, x_225, x_221, x_323);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_333 = lean_ctor_get(x_332, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_334 = x_332;
} else {
 lean_dec_ref(x_332);
 x_334 = lean_box(0);
}
x_335 = l_Int_Linear_Poly_mul(x_222, x_265);
lean_dec(x_265);
x_336 = lean_int_neg(x_213);
lean_dec(x_213);
x_337 = l_Int_Linear_Poly_mul(x_266, x_336);
lean_dec(x_336);
x_338 = l_Int_Linear_Poly_combine(x_335, x_337);
lean_inc(x_260);
if (lean_is_scalar(x_334)) {
 x_339 = lean_alloc_ctor(5, 2, 0);
} else {
 x_339 = x_334;
 lean_ctor_set_tag(x_339, 5);
}
lean_ctor_set(x_339, 0, x_218);
lean_ctor_set(x_339, 1, x_260);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 x_340 = x_260;
} else {
 lean_dec_ref(x_260);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(0, 3, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_272);
lean_ctor_set(x_341, 1, x_338);
lean_ctor_set(x_341, 2, x_339);
x_1 = x_341;
x_2 = x_216;
x_3 = x_212;
x_4 = x_214;
x_5 = x_223;
x_6 = x_226;
x_7 = x_224;
x_8 = x_225;
x_9 = x_221;
x_10 = x_333;
goto _start;
}
else
{
lean_dec(x_272);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec(x_260);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_221);
lean_dec_ref(x_218);
lean_dec(x_216);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec(x_212);
return x_332;
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_343 = lean_ctor_get(x_278, 0);
x_344 = lean_ctor_get(x_278, 1);
x_345 = lean_ctor_get(x_278, 2);
x_346 = lean_ctor_get(x_278, 3);
x_347 = lean_ctor_get(x_278, 4);
x_348 = lean_ctor_get(x_278, 5);
x_349 = lean_ctor_get(x_278, 6);
x_350 = lean_ctor_get(x_278, 7);
x_351 = lean_ctor_get(x_278, 8);
x_352 = lean_ctor_get(x_278, 9);
x_353 = lean_ctor_get(x_278, 10);
x_354 = lean_ctor_get(x_278, 11);
x_355 = lean_ctor_get(x_278, 12);
x_356 = lean_ctor_get(x_278, 13);
x_357 = lean_ctor_get(x_278, 14);
x_358 = lean_ctor_get_uint8(x_278, sizeof(void*)*22);
x_359 = lean_ctor_get(x_278, 15);
x_360 = lean_ctor_get(x_278, 16);
x_361 = lean_ctor_get(x_278, 17);
x_362 = lean_ctor_get(x_278, 18);
x_363 = lean_ctor_get(x_278, 19);
x_364 = lean_ctor_get(x_278, 20);
x_365 = lean_ctor_get_uint8(x_278, sizeof(void*)*22 + 1);
x_366 = lean_ctor_get(x_278, 21);
lean_inc(x_366);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
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
lean_inc(x_343);
lean_dec(x_278);
x_367 = lean_box(0);
x_368 = l_Lean_PersistentArray_set___redArg(x_349, x_220, x_367);
x_369 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_369, 0, x_343);
lean_ctor_set(x_369, 1, x_344);
lean_ctor_set(x_369, 2, x_345);
lean_ctor_set(x_369, 3, x_346);
lean_ctor_set(x_369, 4, x_347);
lean_ctor_set(x_369, 5, x_348);
lean_ctor_set(x_369, 6, x_368);
lean_ctor_set(x_369, 7, x_350);
lean_ctor_set(x_369, 8, x_351);
lean_ctor_set(x_369, 9, x_352);
lean_ctor_set(x_369, 10, x_353);
lean_ctor_set(x_369, 11, x_354);
lean_ctor_set(x_369, 12, x_355);
lean_ctor_set(x_369, 13, x_356);
lean_ctor_set(x_369, 14, x_357);
lean_ctor_set(x_369, 15, x_359);
lean_ctor_set(x_369, 16, x_360);
lean_ctor_set(x_369, 17, x_361);
lean_ctor_set(x_369, 18, x_362);
lean_ctor_set(x_369, 19, x_363);
lean_ctor_set(x_369, 20, x_364);
lean_ctor_set(x_369, 21, x_366);
lean_ctor_set_uint8(x_369, sizeof(void*)*22, x_358);
lean_ctor_set_uint8(x_369, sizeof(void*)*22 + 1, x_365);
lean_ctor_set(x_277, 1, x_369);
x_370 = lean_st_ref_set(x_216, x_276, x_279);
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_372 = x_370;
} else {
 lean_dec_ref(x_370);
 x_372 = lean_box(0);
}
x_373 = lean_int_mul(x_273, x_264);
lean_dec(x_273);
lean_inc_ref(x_222);
x_374 = l_Int_Linear_Poly_mul(x_222, x_373);
lean_dec(x_373);
x_375 = lean_int_mul(x_274, x_215);
lean_dec(x_274);
lean_inc_ref(x_266);
x_376 = l_Int_Linear_Poly_mul(x_266, x_375);
lean_dec(x_375);
x_377 = lean_int_mul(x_215, x_264);
lean_dec(x_215);
x_378 = l_Int_Linear_Poly_combine(x_374, x_376);
lean_inc(x_272);
lean_ctor_set(x_261, 2, x_378);
lean_ctor_set(x_261, 1, x_220);
lean_ctor_set(x_261, 0, x_272);
lean_inc(x_260);
lean_inc_ref(x_218);
if (lean_is_scalar(x_372)) {
 x_379 = lean_alloc_ctor(4, 2, 0);
} else {
 x_379 = x_372;
 lean_ctor_set_tag(x_379, 4);
}
lean_ctor_set(x_379, 0, x_218);
lean_ctor_set(x_379, 1, x_260);
x_380 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_261);
lean_ctor_set(x_380, 2, x_379);
lean_inc(x_221);
lean_inc_ref(x_225);
lean_inc(x_224);
lean_inc_ref(x_226);
lean_inc(x_223);
lean_inc_ref(x_214);
lean_inc(x_212);
lean_inc(x_216);
x_381 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_380, x_216, x_212, x_214, x_223, x_226, x_224, x_225, x_221, x_371);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_382 = lean_ctor_get(x_381, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_383 = x_381;
} else {
 lean_dec_ref(x_381);
 x_383 = lean_box(0);
}
x_384 = l_Int_Linear_Poly_mul(x_222, x_265);
lean_dec(x_265);
x_385 = lean_int_neg(x_213);
lean_dec(x_213);
x_386 = l_Int_Linear_Poly_mul(x_266, x_385);
lean_dec(x_385);
x_387 = l_Int_Linear_Poly_combine(x_384, x_386);
lean_inc(x_260);
if (lean_is_scalar(x_383)) {
 x_388 = lean_alloc_ctor(5, 2, 0);
} else {
 x_388 = x_383;
 lean_ctor_set_tag(x_388, 5);
}
lean_ctor_set(x_388, 0, x_218);
lean_ctor_set(x_388, 1, x_260);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 x_389 = x_260;
} else {
 lean_dec_ref(x_260);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(0, 3, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_272);
lean_ctor_set(x_390, 1, x_387);
lean_ctor_set(x_390, 2, x_388);
x_1 = x_390;
x_2 = x_216;
x_3 = x_212;
x_4 = x_214;
x_5 = x_223;
x_6 = x_226;
x_7 = x_224;
x_8 = x_225;
x_9 = x_221;
x_10 = x_382;
goto _start;
}
else
{
lean_dec(x_272);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec(x_260);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_221);
lean_dec_ref(x_218);
lean_dec(x_216);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec(x_212);
return x_381;
}
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_392 = lean_ctor_get(x_277, 0);
x_393 = lean_ctor_get(x_277, 2);
x_394 = lean_ctor_get(x_277, 3);
lean_inc(x_394);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_277);
x_395 = lean_ctor_get(x_278, 0);
lean_inc_ref(x_395);
x_396 = lean_ctor_get(x_278, 1);
lean_inc_ref(x_396);
x_397 = lean_ctor_get(x_278, 2);
lean_inc_ref(x_397);
x_398 = lean_ctor_get(x_278, 3);
lean_inc_ref(x_398);
x_399 = lean_ctor_get(x_278, 4);
lean_inc_ref(x_399);
x_400 = lean_ctor_get(x_278, 5);
lean_inc_ref(x_400);
x_401 = lean_ctor_get(x_278, 6);
lean_inc_ref(x_401);
x_402 = lean_ctor_get(x_278, 7);
lean_inc_ref(x_402);
x_403 = lean_ctor_get(x_278, 8);
lean_inc_ref(x_403);
x_404 = lean_ctor_get(x_278, 9);
lean_inc_ref(x_404);
x_405 = lean_ctor_get(x_278, 10);
lean_inc_ref(x_405);
x_406 = lean_ctor_get(x_278, 11);
lean_inc(x_406);
x_407 = lean_ctor_get(x_278, 12);
lean_inc_ref(x_407);
x_408 = lean_ctor_get(x_278, 13);
lean_inc_ref(x_408);
x_409 = lean_ctor_get(x_278, 14);
lean_inc(x_409);
x_410 = lean_ctor_get_uint8(x_278, sizeof(void*)*22);
x_411 = lean_ctor_get(x_278, 15);
lean_inc(x_411);
x_412 = lean_ctor_get(x_278, 16);
lean_inc_ref(x_412);
x_413 = lean_ctor_get(x_278, 17);
lean_inc_ref(x_413);
x_414 = lean_ctor_get(x_278, 18);
lean_inc_ref(x_414);
x_415 = lean_ctor_get(x_278, 19);
lean_inc_ref(x_415);
x_416 = lean_ctor_get(x_278, 20);
lean_inc_ref(x_416);
x_417 = lean_ctor_get_uint8(x_278, sizeof(void*)*22 + 1);
x_418 = lean_ctor_get(x_278, 21);
lean_inc_ref(x_418);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 lean_ctor_release(x_278, 2);
 lean_ctor_release(x_278, 3);
 lean_ctor_release(x_278, 4);
 lean_ctor_release(x_278, 5);
 lean_ctor_release(x_278, 6);
 lean_ctor_release(x_278, 7);
 lean_ctor_release(x_278, 8);
 lean_ctor_release(x_278, 9);
 lean_ctor_release(x_278, 10);
 lean_ctor_release(x_278, 11);
 lean_ctor_release(x_278, 12);
 lean_ctor_release(x_278, 13);
 lean_ctor_release(x_278, 14);
 lean_ctor_release(x_278, 15);
 lean_ctor_release(x_278, 16);
 lean_ctor_release(x_278, 17);
 lean_ctor_release(x_278, 18);
 lean_ctor_release(x_278, 19);
 lean_ctor_release(x_278, 20);
 lean_ctor_release(x_278, 21);
 x_419 = x_278;
} else {
 lean_dec_ref(x_278);
 x_419 = lean_box(0);
}
x_420 = lean_box(0);
x_421 = l_Lean_PersistentArray_set___redArg(x_401, x_220, x_420);
if (lean_is_scalar(x_419)) {
 x_422 = lean_alloc_ctor(0, 22, 2);
} else {
 x_422 = x_419;
}
lean_ctor_set(x_422, 0, x_395);
lean_ctor_set(x_422, 1, x_396);
lean_ctor_set(x_422, 2, x_397);
lean_ctor_set(x_422, 3, x_398);
lean_ctor_set(x_422, 4, x_399);
lean_ctor_set(x_422, 5, x_400);
lean_ctor_set(x_422, 6, x_421);
lean_ctor_set(x_422, 7, x_402);
lean_ctor_set(x_422, 8, x_403);
lean_ctor_set(x_422, 9, x_404);
lean_ctor_set(x_422, 10, x_405);
lean_ctor_set(x_422, 11, x_406);
lean_ctor_set(x_422, 12, x_407);
lean_ctor_set(x_422, 13, x_408);
lean_ctor_set(x_422, 14, x_409);
lean_ctor_set(x_422, 15, x_411);
lean_ctor_set(x_422, 16, x_412);
lean_ctor_set(x_422, 17, x_413);
lean_ctor_set(x_422, 18, x_414);
lean_ctor_set(x_422, 19, x_415);
lean_ctor_set(x_422, 20, x_416);
lean_ctor_set(x_422, 21, x_418);
lean_ctor_set_uint8(x_422, sizeof(void*)*22, x_410);
lean_ctor_set_uint8(x_422, sizeof(void*)*22 + 1, x_417);
x_423 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_423, 0, x_392);
lean_ctor_set(x_423, 1, x_422);
lean_ctor_set(x_423, 2, x_393);
lean_ctor_set(x_423, 3, x_394);
lean_ctor_set(x_276, 14, x_423);
x_424 = lean_st_ref_set(x_216, x_276, x_279);
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_426 = x_424;
} else {
 lean_dec_ref(x_424);
 x_426 = lean_box(0);
}
x_427 = lean_int_mul(x_273, x_264);
lean_dec(x_273);
lean_inc_ref(x_222);
x_428 = l_Int_Linear_Poly_mul(x_222, x_427);
lean_dec(x_427);
x_429 = lean_int_mul(x_274, x_215);
lean_dec(x_274);
lean_inc_ref(x_266);
x_430 = l_Int_Linear_Poly_mul(x_266, x_429);
lean_dec(x_429);
x_431 = lean_int_mul(x_215, x_264);
lean_dec(x_215);
x_432 = l_Int_Linear_Poly_combine(x_428, x_430);
lean_inc(x_272);
lean_ctor_set(x_261, 2, x_432);
lean_ctor_set(x_261, 1, x_220);
lean_ctor_set(x_261, 0, x_272);
lean_inc(x_260);
lean_inc_ref(x_218);
if (lean_is_scalar(x_426)) {
 x_433 = lean_alloc_ctor(4, 2, 0);
} else {
 x_433 = x_426;
 lean_ctor_set_tag(x_433, 4);
}
lean_ctor_set(x_433, 0, x_218);
lean_ctor_set(x_433, 1, x_260);
x_434 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_434, 0, x_431);
lean_ctor_set(x_434, 1, x_261);
lean_ctor_set(x_434, 2, x_433);
lean_inc(x_221);
lean_inc_ref(x_225);
lean_inc(x_224);
lean_inc_ref(x_226);
lean_inc(x_223);
lean_inc_ref(x_214);
lean_inc(x_212);
lean_inc(x_216);
x_435 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_434, x_216, x_212, x_214, x_223, x_226, x_224, x_225, x_221, x_425);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_436 = lean_ctor_get(x_435, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_437 = x_435;
} else {
 lean_dec_ref(x_435);
 x_437 = lean_box(0);
}
x_438 = l_Int_Linear_Poly_mul(x_222, x_265);
lean_dec(x_265);
x_439 = lean_int_neg(x_213);
lean_dec(x_213);
x_440 = l_Int_Linear_Poly_mul(x_266, x_439);
lean_dec(x_439);
x_441 = l_Int_Linear_Poly_combine(x_438, x_440);
lean_inc(x_260);
if (lean_is_scalar(x_437)) {
 x_442 = lean_alloc_ctor(5, 2, 0);
} else {
 x_442 = x_437;
 lean_ctor_set_tag(x_442, 5);
}
lean_ctor_set(x_442, 0, x_218);
lean_ctor_set(x_442, 1, x_260);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 x_443 = x_260;
} else {
 lean_dec_ref(x_260);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(0, 3, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_272);
lean_ctor_set(x_444, 1, x_441);
lean_ctor_set(x_444, 2, x_442);
x_1 = x_444;
x_2 = x_216;
x_3 = x_212;
x_4 = x_214;
x_5 = x_223;
x_6 = x_226;
x_7 = x_224;
x_8 = x_225;
x_9 = x_221;
x_10 = x_436;
goto _start;
}
else
{
lean_dec(x_272);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec(x_260);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_221);
lean_dec_ref(x_218);
lean_dec(x_216);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec(x_212);
return x_435;
}
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_446 = lean_ctor_get(x_276, 0);
x_447 = lean_ctor_get(x_276, 1);
x_448 = lean_ctor_get(x_276, 2);
x_449 = lean_ctor_get(x_276, 3);
x_450 = lean_ctor_get(x_276, 4);
x_451 = lean_ctor_get(x_276, 5);
x_452 = lean_ctor_get(x_276, 6);
x_453 = lean_ctor_get(x_276, 7);
x_454 = lean_ctor_get_uint8(x_276, sizeof(void*)*16);
x_455 = lean_ctor_get(x_276, 8);
x_456 = lean_ctor_get(x_276, 9);
x_457 = lean_ctor_get(x_276, 10);
x_458 = lean_ctor_get(x_276, 11);
x_459 = lean_ctor_get(x_276, 12);
x_460 = lean_ctor_get(x_276, 13);
x_461 = lean_ctor_get(x_276, 15);
lean_inc(x_461);
lean_inc(x_460);
lean_inc(x_459);
lean_inc(x_458);
lean_inc(x_457);
lean_inc(x_456);
lean_inc(x_455);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
lean_inc(x_449);
lean_inc(x_448);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_276);
x_462 = lean_ctor_get(x_277, 0);
lean_inc_ref(x_462);
x_463 = lean_ctor_get(x_277, 2);
lean_inc_ref(x_463);
x_464 = lean_ctor_get(x_277, 3);
lean_inc_ref(x_464);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 lean_ctor_release(x_277, 2);
 lean_ctor_release(x_277, 3);
 x_465 = x_277;
} else {
 lean_dec_ref(x_277);
 x_465 = lean_box(0);
}
x_466 = lean_ctor_get(x_278, 0);
lean_inc_ref(x_466);
x_467 = lean_ctor_get(x_278, 1);
lean_inc_ref(x_467);
x_468 = lean_ctor_get(x_278, 2);
lean_inc_ref(x_468);
x_469 = lean_ctor_get(x_278, 3);
lean_inc_ref(x_469);
x_470 = lean_ctor_get(x_278, 4);
lean_inc_ref(x_470);
x_471 = lean_ctor_get(x_278, 5);
lean_inc_ref(x_471);
x_472 = lean_ctor_get(x_278, 6);
lean_inc_ref(x_472);
x_473 = lean_ctor_get(x_278, 7);
lean_inc_ref(x_473);
x_474 = lean_ctor_get(x_278, 8);
lean_inc_ref(x_474);
x_475 = lean_ctor_get(x_278, 9);
lean_inc_ref(x_475);
x_476 = lean_ctor_get(x_278, 10);
lean_inc_ref(x_476);
x_477 = lean_ctor_get(x_278, 11);
lean_inc(x_477);
x_478 = lean_ctor_get(x_278, 12);
lean_inc_ref(x_478);
x_479 = lean_ctor_get(x_278, 13);
lean_inc_ref(x_479);
x_480 = lean_ctor_get(x_278, 14);
lean_inc(x_480);
x_481 = lean_ctor_get_uint8(x_278, sizeof(void*)*22);
x_482 = lean_ctor_get(x_278, 15);
lean_inc(x_482);
x_483 = lean_ctor_get(x_278, 16);
lean_inc_ref(x_483);
x_484 = lean_ctor_get(x_278, 17);
lean_inc_ref(x_484);
x_485 = lean_ctor_get(x_278, 18);
lean_inc_ref(x_485);
x_486 = lean_ctor_get(x_278, 19);
lean_inc_ref(x_486);
x_487 = lean_ctor_get(x_278, 20);
lean_inc_ref(x_487);
x_488 = lean_ctor_get_uint8(x_278, sizeof(void*)*22 + 1);
x_489 = lean_ctor_get(x_278, 21);
lean_inc_ref(x_489);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 lean_ctor_release(x_278, 2);
 lean_ctor_release(x_278, 3);
 lean_ctor_release(x_278, 4);
 lean_ctor_release(x_278, 5);
 lean_ctor_release(x_278, 6);
 lean_ctor_release(x_278, 7);
 lean_ctor_release(x_278, 8);
 lean_ctor_release(x_278, 9);
 lean_ctor_release(x_278, 10);
 lean_ctor_release(x_278, 11);
 lean_ctor_release(x_278, 12);
 lean_ctor_release(x_278, 13);
 lean_ctor_release(x_278, 14);
 lean_ctor_release(x_278, 15);
 lean_ctor_release(x_278, 16);
 lean_ctor_release(x_278, 17);
 lean_ctor_release(x_278, 18);
 lean_ctor_release(x_278, 19);
 lean_ctor_release(x_278, 20);
 lean_ctor_release(x_278, 21);
 x_490 = x_278;
} else {
 lean_dec_ref(x_278);
 x_490 = lean_box(0);
}
x_491 = lean_box(0);
x_492 = l_Lean_PersistentArray_set___redArg(x_472, x_220, x_491);
if (lean_is_scalar(x_490)) {
 x_493 = lean_alloc_ctor(0, 22, 2);
} else {
 x_493 = x_490;
}
lean_ctor_set(x_493, 0, x_466);
lean_ctor_set(x_493, 1, x_467);
lean_ctor_set(x_493, 2, x_468);
lean_ctor_set(x_493, 3, x_469);
lean_ctor_set(x_493, 4, x_470);
lean_ctor_set(x_493, 5, x_471);
lean_ctor_set(x_493, 6, x_492);
lean_ctor_set(x_493, 7, x_473);
lean_ctor_set(x_493, 8, x_474);
lean_ctor_set(x_493, 9, x_475);
lean_ctor_set(x_493, 10, x_476);
lean_ctor_set(x_493, 11, x_477);
lean_ctor_set(x_493, 12, x_478);
lean_ctor_set(x_493, 13, x_479);
lean_ctor_set(x_493, 14, x_480);
lean_ctor_set(x_493, 15, x_482);
lean_ctor_set(x_493, 16, x_483);
lean_ctor_set(x_493, 17, x_484);
lean_ctor_set(x_493, 18, x_485);
lean_ctor_set(x_493, 19, x_486);
lean_ctor_set(x_493, 20, x_487);
lean_ctor_set(x_493, 21, x_489);
lean_ctor_set_uint8(x_493, sizeof(void*)*22, x_481);
lean_ctor_set_uint8(x_493, sizeof(void*)*22 + 1, x_488);
if (lean_is_scalar(x_465)) {
 x_494 = lean_alloc_ctor(0, 4, 0);
} else {
 x_494 = x_465;
}
lean_ctor_set(x_494, 0, x_462);
lean_ctor_set(x_494, 1, x_493);
lean_ctor_set(x_494, 2, x_463);
lean_ctor_set(x_494, 3, x_464);
x_495 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_495, 0, x_446);
lean_ctor_set(x_495, 1, x_447);
lean_ctor_set(x_495, 2, x_448);
lean_ctor_set(x_495, 3, x_449);
lean_ctor_set(x_495, 4, x_450);
lean_ctor_set(x_495, 5, x_451);
lean_ctor_set(x_495, 6, x_452);
lean_ctor_set(x_495, 7, x_453);
lean_ctor_set(x_495, 8, x_455);
lean_ctor_set(x_495, 9, x_456);
lean_ctor_set(x_495, 10, x_457);
lean_ctor_set(x_495, 11, x_458);
lean_ctor_set(x_495, 12, x_459);
lean_ctor_set(x_495, 13, x_460);
lean_ctor_set(x_495, 14, x_494);
lean_ctor_set(x_495, 15, x_461);
lean_ctor_set_uint8(x_495, sizeof(void*)*16, x_454);
x_496 = lean_st_ref_set(x_216, x_495, x_279);
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_498 = x_496;
} else {
 lean_dec_ref(x_496);
 x_498 = lean_box(0);
}
x_499 = lean_int_mul(x_273, x_264);
lean_dec(x_273);
lean_inc_ref(x_222);
x_500 = l_Int_Linear_Poly_mul(x_222, x_499);
lean_dec(x_499);
x_501 = lean_int_mul(x_274, x_215);
lean_dec(x_274);
lean_inc_ref(x_266);
x_502 = l_Int_Linear_Poly_mul(x_266, x_501);
lean_dec(x_501);
x_503 = lean_int_mul(x_215, x_264);
lean_dec(x_215);
x_504 = l_Int_Linear_Poly_combine(x_500, x_502);
lean_inc(x_272);
lean_ctor_set(x_261, 2, x_504);
lean_ctor_set(x_261, 1, x_220);
lean_ctor_set(x_261, 0, x_272);
lean_inc(x_260);
lean_inc_ref(x_218);
if (lean_is_scalar(x_498)) {
 x_505 = lean_alloc_ctor(4, 2, 0);
} else {
 x_505 = x_498;
 lean_ctor_set_tag(x_505, 4);
}
lean_ctor_set(x_505, 0, x_218);
lean_ctor_set(x_505, 1, x_260);
x_506 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_506, 0, x_503);
lean_ctor_set(x_506, 1, x_261);
lean_ctor_set(x_506, 2, x_505);
lean_inc(x_221);
lean_inc_ref(x_225);
lean_inc(x_224);
lean_inc_ref(x_226);
lean_inc(x_223);
lean_inc_ref(x_214);
lean_inc(x_212);
lean_inc(x_216);
x_507 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_506, x_216, x_212, x_214, x_223, x_226, x_224, x_225, x_221, x_497);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_508 = lean_ctor_get(x_507, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 lean_ctor_release(x_507, 1);
 x_509 = x_507;
} else {
 lean_dec_ref(x_507);
 x_509 = lean_box(0);
}
x_510 = l_Int_Linear_Poly_mul(x_222, x_265);
lean_dec(x_265);
x_511 = lean_int_neg(x_213);
lean_dec(x_213);
x_512 = l_Int_Linear_Poly_mul(x_266, x_511);
lean_dec(x_511);
x_513 = l_Int_Linear_Poly_combine(x_510, x_512);
lean_inc(x_260);
if (lean_is_scalar(x_509)) {
 x_514 = lean_alloc_ctor(5, 2, 0);
} else {
 x_514 = x_509;
 lean_ctor_set_tag(x_514, 5);
}
lean_ctor_set(x_514, 0, x_218);
lean_ctor_set(x_514, 1, x_260);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 x_515 = x_260;
} else {
 lean_dec_ref(x_260);
 x_515 = lean_box(0);
}
if (lean_is_scalar(x_515)) {
 x_516 = lean_alloc_ctor(0, 3, 0);
} else {
 x_516 = x_515;
}
lean_ctor_set(x_516, 0, x_272);
lean_ctor_set(x_516, 1, x_513);
lean_ctor_set(x_516, 2, x_514);
x_1 = x_516;
x_2 = x_216;
x_3 = x_212;
x_4 = x_214;
x_5 = x_223;
x_6 = x_226;
x_7 = x_224;
x_8 = x_225;
x_9 = x_221;
x_10 = x_508;
goto _start;
}
else
{
lean_dec(x_272);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec(x_260);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_221);
lean_dec_ref(x_218);
lean_dec(x_216);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec(x_212);
return x_507;
}
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; uint8_t x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_518 = lean_ctor_get(x_260, 0);
x_519 = lean_ctor_get(x_261, 0);
x_520 = lean_ctor_get(x_261, 2);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_261);
x_521 = lean_int_mul(x_213, x_518);
x_522 = lean_int_mul(x_519, x_215);
x_523 = l_Lean_Meta_Grind_Arith_gcdExt(x_521, x_522);
lean_dec(x_522);
lean_dec(x_521);
x_524 = lean_ctor_get(x_523, 1);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 0);
lean_inc(x_525);
lean_dec_ref(x_523);
x_526 = lean_ctor_get(x_524, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_524, 1);
lean_inc(x_527);
lean_dec(x_524);
x_528 = lean_st_ref_take(x_216, x_219);
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_529, 14);
lean_inc_ref(x_530);
x_531 = lean_ctor_get(x_530, 1);
lean_inc_ref(x_531);
x_532 = lean_ctor_get(x_528, 1);
lean_inc(x_532);
lean_dec_ref(x_528);
x_533 = lean_ctor_get(x_529, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_529, 1);
lean_inc_ref(x_534);
x_535 = lean_ctor_get(x_529, 2);
lean_inc(x_535);
x_536 = lean_ctor_get(x_529, 3);
lean_inc_ref(x_536);
x_537 = lean_ctor_get(x_529, 4);
lean_inc_ref(x_537);
x_538 = lean_ctor_get(x_529, 5);
lean_inc_ref(x_538);
x_539 = lean_ctor_get(x_529, 6);
lean_inc_ref(x_539);
x_540 = lean_ctor_get(x_529, 7);
lean_inc_ref(x_540);
x_541 = lean_ctor_get_uint8(x_529, sizeof(void*)*16);
x_542 = lean_ctor_get(x_529, 8);
lean_inc(x_542);
x_543 = lean_ctor_get(x_529, 9);
lean_inc_ref(x_543);
x_544 = lean_ctor_get(x_529, 10);
lean_inc_ref(x_544);
x_545 = lean_ctor_get(x_529, 11);
lean_inc_ref(x_545);
x_546 = lean_ctor_get(x_529, 12);
lean_inc_ref(x_546);
x_547 = lean_ctor_get(x_529, 13);
lean_inc_ref(x_547);
x_548 = lean_ctor_get(x_529, 15);
lean_inc_ref(x_548);
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
 x_549 = x_529;
} else {
 lean_dec_ref(x_529);
 x_549 = lean_box(0);
}
x_550 = lean_ctor_get(x_530, 0);
lean_inc_ref(x_550);
x_551 = lean_ctor_get(x_530, 2);
lean_inc_ref(x_551);
x_552 = lean_ctor_get(x_530, 3);
lean_inc_ref(x_552);
if (lean_is_exclusive(x_530)) {
 lean_ctor_release(x_530, 0);
 lean_ctor_release(x_530, 1);
 lean_ctor_release(x_530, 2);
 lean_ctor_release(x_530, 3);
 x_553 = x_530;
} else {
 lean_dec_ref(x_530);
 x_553 = lean_box(0);
}
x_554 = lean_ctor_get(x_531, 0);
lean_inc_ref(x_554);
x_555 = lean_ctor_get(x_531, 1);
lean_inc_ref(x_555);
x_556 = lean_ctor_get(x_531, 2);
lean_inc_ref(x_556);
x_557 = lean_ctor_get(x_531, 3);
lean_inc_ref(x_557);
x_558 = lean_ctor_get(x_531, 4);
lean_inc_ref(x_558);
x_559 = lean_ctor_get(x_531, 5);
lean_inc_ref(x_559);
x_560 = lean_ctor_get(x_531, 6);
lean_inc_ref(x_560);
x_561 = lean_ctor_get(x_531, 7);
lean_inc_ref(x_561);
x_562 = lean_ctor_get(x_531, 8);
lean_inc_ref(x_562);
x_563 = lean_ctor_get(x_531, 9);
lean_inc_ref(x_563);
x_564 = lean_ctor_get(x_531, 10);
lean_inc_ref(x_564);
x_565 = lean_ctor_get(x_531, 11);
lean_inc(x_565);
x_566 = lean_ctor_get(x_531, 12);
lean_inc_ref(x_566);
x_567 = lean_ctor_get(x_531, 13);
lean_inc_ref(x_567);
x_568 = lean_ctor_get(x_531, 14);
lean_inc(x_568);
x_569 = lean_ctor_get_uint8(x_531, sizeof(void*)*22);
x_570 = lean_ctor_get(x_531, 15);
lean_inc(x_570);
x_571 = lean_ctor_get(x_531, 16);
lean_inc_ref(x_571);
x_572 = lean_ctor_get(x_531, 17);
lean_inc_ref(x_572);
x_573 = lean_ctor_get(x_531, 18);
lean_inc_ref(x_573);
x_574 = lean_ctor_get(x_531, 19);
lean_inc_ref(x_574);
x_575 = lean_ctor_get(x_531, 20);
lean_inc_ref(x_575);
x_576 = lean_ctor_get_uint8(x_531, sizeof(void*)*22 + 1);
x_577 = lean_ctor_get(x_531, 21);
lean_inc_ref(x_577);
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
 lean_ctor_release(x_531, 17);
 lean_ctor_release(x_531, 18);
 lean_ctor_release(x_531, 19);
 lean_ctor_release(x_531, 20);
 lean_ctor_release(x_531, 21);
 x_578 = x_531;
} else {
 lean_dec_ref(x_531);
 x_578 = lean_box(0);
}
x_579 = lean_box(0);
x_580 = l_Lean_PersistentArray_set___redArg(x_560, x_220, x_579);
if (lean_is_scalar(x_578)) {
 x_581 = lean_alloc_ctor(0, 22, 2);
} else {
 x_581 = x_578;
}
lean_ctor_set(x_581, 0, x_554);
lean_ctor_set(x_581, 1, x_555);
lean_ctor_set(x_581, 2, x_556);
lean_ctor_set(x_581, 3, x_557);
lean_ctor_set(x_581, 4, x_558);
lean_ctor_set(x_581, 5, x_559);
lean_ctor_set(x_581, 6, x_580);
lean_ctor_set(x_581, 7, x_561);
lean_ctor_set(x_581, 8, x_562);
lean_ctor_set(x_581, 9, x_563);
lean_ctor_set(x_581, 10, x_564);
lean_ctor_set(x_581, 11, x_565);
lean_ctor_set(x_581, 12, x_566);
lean_ctor_set(x_581, 13, x_567);
lean_ctor_set(x_581, 14, x_568);
lean_ctor_set(x_581, 15, x_570);
lean_ctor_set(x_581, 16, x_571);
lean_ctor_set(x_581, 17, x_572);
lean_ctor_set(x_581, 18, x_573);
lean_ctor_set(x_581, 19, x_574);
lean_ctor_set(x_581, 20, x_575);
lean_ctor_set(x_581, 21, x_577);
lean_ctor_set_uint8(x_581, sizeof(void*)*22, x_569);
lean_ctor_set_uint8(x_581, sizeof(void*)*22 + 1, x_576);
if (lean_is_scalar(x_553)) {
 x_582 = lean_alloc_ctor(0, 4, 0);
} else {
 x_582 = x_553;
}
lean_ctor_set(x_582, 0, x_550);
lean_ctor_set(x_582, 1, x_581);
lean_ctor_set(x_582, 2, x_551);
lean_ctor_set(x_582, 3, x_552);
if (lean_is_scalar(x_549)) {
 x_583 = lean_alloc_ctor(0, 16, 1);
} else {
 x_583 = x_549;
}
lean_ctor_set(x_583, 0, x_533);
lean_ctor_set(x_583, 1, x_534);
lean_ctor_set(x_583, 2, x_535);
lean_ctor_set(x_583, 3, x_536);
lean_ctor_set(x_583, 4, x_537);
lean_ctor_set(x_583, 5, x_538);
lean_ctor_set(x_583, 6, x_539);
lean_ctor_set(x_583, 7, x_540);
lean_ctor_set(x_583, 8, x_542);
lean_ctor_set(x_583, 9, x_543);
lean_ctor_set(x_583, 10, x_544);
lean_ctor_set(x_583, 11, x_545);
lean_ctor_set(x_583, 12, x_546);
lean_ctor_set(x_583, 13, x_547);
lean_ctor_set(x_583, 14, x_582);
lean_ctor_set(x_583, 15, x_548);
lean_ctor_set_uint8(x_583, sizeof(void*)*16, x_541);
x_584 = lean_st_ref_set(x_216, x_583, x_532);
x_585 = lean_ctor_get(x_584, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_584)) {
 lean_ctor_release(x_584, 0);
 lean_ctor_release(x_584, 1);
 x_586 = x_584;
} else {
 lean_dec_ref(x_584);
 x_586 = lean_box(0);
}
x_587 = lean_int_mul(x_526, x_518);
lean_dec(x_526);
lean_inc_ref(x_222);
x_588 = l_Int_Linear_Poly_mul(x_222, x_587);
lean_dec(x_587);
x_589 = lean_int_mul(x_527, x_215);
lean_dec(x_527);
lean_inc_ref(x_520);
x_590 = l_Int_Linear_Poly_mul(x_520, x_589);
lean_dec(x_589);
x_591 = lean_int_mul(x_215, x_518);
lean_dec(x_215);
x_592 = l_Int_Linear_Poly_combine(x_588, x_590);
lean_inc(x_525);
x_593 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_593, 0, x_525);
lean_ctor_set(x_593, 1, x_220);
lean_ctor_set(x_593, 2, x_592);
lean_inc(x_260);
lean_inc_ref(x_218);
if (lean_is_scalar(x_586)) {
 x_594 = lean_alloc_ctor(4, 2, 0);
} else {
 x_594 = x_586;
 lean_ctor_set_tag(x_594, 4);
}
lean_ctor_set(x_594, 0, x_218);
lean_ctor_set(x_594, 1, x_260);
x_595 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_595, 0, x_591);
lean_ctor_set(x_595, 1, x_593);
lean_ctor_set(x_595, 2, x_594);
lean_inc(x_221);
lean_inc_ref(x_225);
lean_inc(x_224);
lean_inc_ref(x_226);
lean_inc(x_223);
lean_inc_ref(x_214);
lean_inc(x_212);
lean_inc(x_216);
x_596 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_595, x_216, x_212, x_214, x_223, x_226, x_224, x_225, x_221, x_585);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_598 = x_596;
} else {
 lean_dec_ref(x_596);
 x_598 = lean_box(0);
}
x_599 = l_Int_Linear_Poly_mul(x_222, x_519);
lean_dec(x_519);
x_600 = lean_int_neg(x_213);
lean_dec(x_213);
x_601 = l_Int_Linear_Poly_mul(x_520, x_600);
lean_dec(x_600);
x_602 = l_Int_Linear_Poly_combine(x_599, x_601);
lean_inc(x_260);
if (lean_is_scalar(x_598)) {
 x_603 = lean_alloc_ctor(5, 2, 0);
} else {
 x_603 = x_598;
 lean_ctor_set_tag(x_603, 5);
}
lean_ctor_set(x_603, 0, x_218);
lean_ctor_set(x_603, 1, x_260);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 x_604 = x_260;
} else {
 lean_dec_ref(x_260);
 x_604 = lean_box(0);
}
if (lean_is_scalar(x_604)) {
 x_605 = lean_alloc_ctor(0, 3, 0);
} else {
 x_605 = x_604;
}
lean_ctor_set(x_605, 0, x_525);
lean_ctor_set(x_605, 1, x_602);
lean_ctor_set(x_605, 2, x_603);
x_1 = x_605;
x_2 = x_216;
x_3 = x_212;
x_4 = x_214;
x_5 = x_223;
x_6 = x_226;
x_7 = x_224;
x_8 = x_225;
x_9 = x_221;
x_10 = x_597;
goto _start;
}
else
{
lean_dec(x_525);
lean_dec_ref(x_520);
lean_dec(x_519);
lean_dec(x_260);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_221);
lean_dec_ref(x_218);
lean_dec(x_216);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec(x_212);
return x_596;
}
}
}
}
}
block_641:
{
lean_object* x_629; 
x_629 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_620, x_628);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; uint8_t x_634; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_630, 6);
lean_inc_ref(x_631);
lean_dec(x_630);
x_632 = lean_ctor_get(x_629, 1);
lean_inc(x_632);
lean_dec_ref(x_629);
x_633 = lean_ctor_get(x_631, 2);
x_634 = lean_nat_dec_lt(x_616, x_633);
if (x_634 == 0)
{
lean_object* x_635; 
lean_dec_ref(x_631);
x_635 = l_outOfBounds___redArg(x_613);
x_212 = x_621;
x_213 = x_615;
x_214 = x_622;
x_215 = x_617;
x_216 = x_620;
x_217 = x_619;
x_218 = x_614;
x_219 = x_632;
x_220 = x_616;
x_221 = x_627;
x_222 = x_618;
x_223 = x_623;
x_224 = x_625;
x_225 = x_626;
x_226 = x_624;
x_227 = x_635;
goto block_607;
}
else
{
lean_object* x_636; 
x_636 = l_Lean_PersistentArray_get_x21___redArg(x_613, x_631, x_616);
x_212 = x_621;
x_213 = x_615;
x_214 = x_622;
x_215 = x_617;
x_216 = x_620;
x_217 = x_619;
x_218 = x_614;
x_219 = x_632;
x_220 = x_616;
x_221 = x_627;
x_222 = x_618;
x_223 = x_623;
x_224 = x_625;
x_225 = x_626;
x_226 = x_624;
x_227 = x_636;
goto block_607;
}
}
else
{
uint8_t x_637; 
lean_dec(x_627);
lean_dec_ref(x_626);
lean_dec(x_625);
lean_dec_ref(x_624);
lean_dec(x_623);
lean_dec_ref(x_622);
lean_dec(x_621);
lean_dec(x_620);
lean_dec_ref(x_619);
lean_dec_ref(x_618);
lean_dec(x_617);
lean_dec(x_616);
lean_dec(x_615);
lean_dec_ref(x_614);
x_637 = !lean_is_exclusive(x_629);
if (x_637 == 0)
{
return x_629;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_629, 0);
x_639 = lean_ctor_get(x_629, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_629);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
return x_640;
}
}
}
block_743:
{
lean_object* x_651; lean_object* x_652; 
x_651 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_648);
x_652 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_651, x_642, x_643, x_644, x_645, x_646, x_647, x_648, x_649, x_650);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_657; 
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
lean_dec_ref(x_652);
x_655 = lean_ctor_get(x_653, 0);
x_656 = lean_ctor_get(x_653, 1);
lean_inc(x_655);
x_657 = l_Int_Linear_Poly_isUnsatDvd(x_655, x_656);
if (x_657 == 0)
{
uint8_t x_658; 
x_658 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_653);
if (x_658 == 0)
{
lean_dec(x_612);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_659; 
x_659 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_653, x_642, x_643, x_644, x_645, x_646, x_647, x_648, x_649, x_654);
lean_dec(x_649);
lean_dec_ref(x_648);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec(x_642);
return x_659;
}
else
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
lean_inc_ref(x_656);
lean_inc(x_655);
x_660 = lean_ctor_get(x_656, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_656, 1);
lean_inc(x_661);
x_662 = lean_ctor_get(x_656, 2);
lean_inc_ref(x_662);
lean_inc(x_653);
x_663 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_653, x_642, x_654);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; uint8_t x_666; uint8_t x_667; uint8_t x_668; 
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
lean_dec_ref(x_663);
x_666 = 0;
x_667 = lean_unbox(x_664);
lean_dec(x_664);
x_668 = l_Lean_beqLBool____x40_Lean_Data_LBool_27903016____hygCtx___hyg_9_(x_667, x_666);
if (x_668 == 0)
{
x_614 = x_653;
x_615 = x_660;
x_616 = x_661;
x_617 = x_655;
x_618 = x_662;
x_619 = x_656;
x_620 = x_642;
x_621 = x_643;
x_622 = x_644;
x_623 = x_645;
x_624 = x_646;
x_625 = x_647;
x_626 = x_648;
x_627 = x_649;
x_628 = x_665;
goto block_641;
}
else
{
lean_object* x_669; 
x_669 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_661, x_642, x_665);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; 
x_670 = lean_ctor_get(x_669, 1);
lean_inc(x_670);
lean_dec_ref(x_669);
x_614 = x_653;
x_615 = x_660;
x_616 = x_661;
x_617 = x_655;
x_618 = x_662;
x_619 = x_656;
x_620 = x_642;
x_621 = x_643;
x_622 = x_644;
x_623 = x_645;
x_624 = x_646;
x_625 = x_647;
x_626 = x_648;
x_627 = x_649;
x_628 = x_670;
goto block_641;
}
else
{
lean_dec_ref(x_662);
lean_dec(x_661);
lean_dec(x_660);
lean_dec_ref(x_656);
lean_dec(x_655);
lean_dec(x_653);
lean_dec(x_649);
lean_dec_ref(x_648);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec(x_642);
return x_669;
}
}
}
else
{
uint8_t x_671; 
lean_dec_ref(x_662);
lean_dec(x_661);
lean_dec(x_660);
lean_dec_ref(x_656);
lean_dec(x_655);
lean_dec(x_653);
lean_dec(x_649);
lean_dec_ref(x_648);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec(x_642);
x_671 = !lean_is_exclusive(x_663);
if (x_671 == 0)
{
return x_663;
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_672 = lean_ctor_get(x_663, 0);
x_673 = lean_ctor_get(x_663, 1);
lean_inc(x_673);
lean_inc(x_672);
lean_dec(x_663);
x_674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_674, 0, x_672);
lean_ctor_set(x_674, 1, x_673);
return x_674;
}
}
}
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; uint8_t x_678; 
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
x_675 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_676 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_675, x_648, x_654);
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
x_678 = lean_unbox(x_677);
lean_dec(x_677);
if (x_678 == 0)
{
lean_object* x_679; 
lean_dec(x_653);
lean_dec(x_649);
lean_dec_ref(x_648);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_642);
lean_dec(x_612);
x_679 = lean_ctor_get(x_676, 1);
lean_inc(x_679);
lean_dec_ref(x_676);
x_186 = x_679;
goto block_189;
}
else
{
uint8_t x_680; 
x_680 = !lean_is_exclusive(x_676);
if (x_680 == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_681 = lean_ctor_get(x_676, 1);
x_682 = lean_ctor_get(x_676, 0);
lean_dec(x_682);
x_683 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_653, x_642, x_681);
lean_dec(x_642);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_683, 1);
lean_inc(x_685);
lean_dec_ref(x_683);
x_686 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_676, 7);
lean_ctor_set(x_676, 1, x_684);
lean_ctor_set(x_676, 0, x_686);
if (lean_is_scalar(x_612)) {
 x_687 = lean_alloc_ctor(7, 2, 0);
} else {
 x_687 = x_612;
 lean_ctor_set_tag(x_687, 7);
}
lean_ctor_set(x_687, 0, x_676);
lean_ctor_set(x_687, 1, x_686);
x_688 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_675, x_687, x_646, x_647, x_648, x_649, x_685);
lean_dec(x_649);
lean_dec_ref(x_648);
lean_dec(x_647);
lean_dec_ref(x_646);
x_689 = lean_ctor_get(x_688, 1);
lean_inc(x_689);
lean_dec_ref(x_688);
x_186 = x_689;
goto block_189;
}
else
{
uint8_t x_690; 
lean_free_object(x_676);
lean_dec(x_649);
lean_dec_ref(x_648);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_612);
x_690 = !lean_is_exclusive(x_683);
if (x_690 == 0)
{
return x_683;
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_691 = lean_ctor_get(x_683, 0);
x_692 = lean_ctor_get(x_683, 1);
lean_inc(x_692);
lean_inc(x_691);
lean_dec(x_683);
x_693 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_693, 0, x_691);
lean_ctor_set(x_693, 1, x_692);
return x_693;
}
}
}
else
{
lean_object* x_694; lean_object* x_695; 
x_694 = lean_ctor_get(x_676, 1);
lean_inc(x_694);
lean_dec(x_676);
x_695 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_653, x_642, x_694);
lean_dec(x_642);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
lean_dec_ref(x_695);
x_698 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_699 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_699, 0, x_698);
lean_ctor_set(x_699, 1, x_696);
if (lean_is_scalar(x_612)) {
 x_700 = lean_alloc_ctor(7, 2, 0);
} else {
 x_700 = x_612;
 lean_ctor_set_tag(x_700, 7);
}
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_698);
x_701 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_675, x_700, x_646, x_647, x_648, x_649, x_697);
lean_dec(x_649);
lean_dec_ref(x_648);
lean_dec(x_647);
lean_dec_ref(x_646);
x_702 = lean_ctor_get(x_701, 1);
lean_inc(x_702);
lean_dec_ref(x_701);
x_186 = x_702;
goto block_189;
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_dec(x_649);
lean_dec_ref(x_648);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_612);
x_703 = lean_ctor_get(x_695, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_695, 1);
lean_inc(x_704);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 x_705 = x_695;
} else {
 lean_dec_ref(x_695);
 x_705 = lean_box(0);
}
if (lean_is_scalar(x_705)) {
 x_706 = lean_alloc_ctor(1, 2, 0);
} else {
 x_706 = x_705;
}
lean_ctor_set(x_706, 0, x_703);
lean_ctor_set(x_706, 1, x_704);
return x_706;
}
}
}
}
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; uint8_t x_710; 
x_707 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_708 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_707, x_648, x_654);
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
x_710 = lean_unbox(x_709);
lean_dec(x_709);
if (x_710 == 0)
{
lean_object* x_711; 
lean_dec(x_612);
x_711 = lean_ctor_get(x_708, 1);
lean_inc(x_711);
lean_dec_ref(x_708);
x_167 = x_653;
x_168 = x_642;
x_169 = x_643;
x_170 = x_644;
x_171 = x_645;
x_172 = x_646;
x_173 = x_647;
x_174 = x_648;
x_175 = x_649;
x_176 = x_711;
goto block_185;
}
else
{
uint8_t x_712; 
x_712 = !lean_is_exclusive(x_708);
if (x_712 == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_708, 1);
x_714 = lean_ctor_get(x_708, 0);
lean_dec(x_714);
lean_inc(x_653);
x_715 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_653, x_642, x_713);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
lean_dec_ref(x_715);
x_718 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
lean_ctor_set_tag(x_708, 7);
lean_ctor_set(x_708, 1, x_716);
lean_ctor_set(x_708, 0, x_718);
if (lean_is_scalar(x_612)) {
 x_719 = lean_alloc_ctor(7, 2, 0);
} else {
 x_719 = x_612;
 lean_ctor_set_tag(x_719, 7);
}
lean_ctor_set(x_719, 0, x_708);
lean_ctor_set(x_719, 1, x_718);
x_720 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_707, x_719, x_646, x_647, x_648, x_649, x_717);
x_721 = lean_ctor_get(x_720, 1);
lean_inc(x_721);
lean_dec_ref(x_720);
x_167 = x_653;
x_168 = x_642;
x_169 = x_643;
x_170 = x_644;
x_171 = x_645;
x_172 = x_646;
x_173 = x_647;
x_174 = x_648;
x_175 = x_649;
x_176 = x_721;
goto block_185;
}
else
{
uint8_t x_722; 
lean_free_object(x_708);
lean_dec(x_653);
lean_dec(x_649);
lean_dec_ref(x_648);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec(x_642);
lean_dec(x_612);
x_722 = !lean_is_exclusive(x_715);
if (x_722 == 0)
{
return x_715;
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_723 = lean_ctor_get(x_715, 0);
x_724 = lean_ctor_get(x_715, 1);
lean_inc(x_724);
lean_inc(x_723);
lean_dec(x_715);
x_725 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_725, 0, x_723);
lean_ctor_set(x_725, 1, x_724);
return x_725;
}
}
}
else
{
lean_object* x_726; lean_object* x_727; 
x_726 = lean_ctor_get(x_708, 1);
lean_inc(x_726);
lean_dec(x_708);
lean_inc(x_653);
x_727 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_653, x_642, x_726);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
lean_dec_ref(x_727);
x_730 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_731 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_728);
if (lean_is_scalar(x_612)) {
 x_732 = lean_alloc_ctor(7, 2, 0);
} else {
 x_732 = x_612;
 lean_ctor_set_tag(x_732, 7);
}
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_730);
x_733 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_707, x_732, x_646, x_647, x_648, x_649, x_729);
x_734 = lean_ctor_get(x_733, 1);
lean_inc(x_734);
lean_dec_ref(x_733);
x_167 = x_653;
x_168 = x_642;
x_169 = x_643;
x_170 = x_644;
x_171 = x_645;
x_172 = x_646;
x_173 = x_647;
x_174 = x_648;
x_175 = x_649;
x_176 = x_734;
goto block_185;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
lean_dec(x_653);
lean_dec(x_649);
lean_dec_ref(x_648);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec(x_642);
lean_dec(x_612);
x_735 = lean_ctor_get(x_727, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_727, 1);
lean_inc(x_736);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_737 = x_727;
} else {
 lean_dec_ref(x_727);
 x_737 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_738 = lean_alloc_ctor(1, 2, 0);
} else {
 x_738 = x_737;
}
lean_ctor_set(x_738, 0, x_735);
lean_ctor_set(x_738, 1, x_736);
return x_738;
}
}
}
}
}
else
{
uint8_t x_739; 
lean_dec(x_649);
lean_dec_ref(x_648);
lean_dec(x_647);
lean_dec_ref(x_646);
lean_dec(x_645);
lean_dec_ref(x_644);
lean_dec(x_643);
lean_dec(x_642);
lean_dec(x_612);
x_739 = !lean_is_exclusive(x_652);
if (x_739 == 0)
{
return x_652;
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_740 = lean_ctor_get(x_652, 0);
x_741 = lean_ctor_get(x_652, 1);
lean_inc(x_741);
lean_inc(x_740);
lean_dec(x_652);
x_742 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_742, 0, x_740);
lean_ctor_set(x_742, 1, x_741);
return x_742;
}
}
}
}
else
{
uint8_t x_757; 
lean_free_object(x_8);
lean_dec_ref(x_204);
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
lean_dec(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_757 = !lean_is_exclusive(x_206);
if (x_757 == 0)
{
lean_object* x_758; lean_object* x_759; 
x_758 = lean_ctor_get(x_206, 0);
lean_dec(x_758);
x_759 = lean_box(0);
lean_ctor_set(x_206, 0, x_759);
return x_206;
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; 
x_760 = lean_ctor_get(x_206, 1);
lean_inc(x_760);
lean_dec(x_206);
x_761 = lean_box(0);
x_762 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_762, 0, x_761);
lean_ctor_set(x_762, 1, x_760);
return x_762;
}
}
}
else
{
uint8_t x_763; 
lean_free_object(x_8);
lean_dec_ref(x_204);
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
lean_dec(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_763 = !lean_is_exclusive(x_206);
if (x_763 == 0)
{
return x_206;
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_764 = lean_ctor_get(x_206, 0);
x_765 = lean_ctor_get(x_206, 1);
lean_inc(x_765);
lean_inc(x_764);
lean_dec(x_206);
x_766 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_766, 0, x_764);
lean_ctor_set(x_766, 1, x_765);
return x_766;
}
}
}
else
{
lean_object* x_767; 
lean_free_object(x_8);
lean_dec_ref(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_767 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_196, x_10);
return x_767;
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; uint8_t x_780; lean_object* x_781; uint8_t x_782; lean_object* x_783; uint8_t x_784; 
x_768 = lean_ctor_get(x_8, 0);
x_769 = lean_ctor_get(x_8, 1);
x_770 = lean_ctor_get(x_8, 2);
x_771 = lean_ctor_get(x_8, 3);
x_772 = lean_ctor_get(x_8, 4);
x_773 = lean_ctor_get(x_8, 5);
x_774 = lean_ctor_get(x_8, 6);
x_775 = lean_ctor_get(x_8, 7);
x_776 = lean_ctor_get(x_8, 8);
x_777 = lean_ctor_get(x_8, 9);
x_778 = lean_ctor_get(x_8, 10);
x_779 = lean_ctor_get(x_8, 11);
x_780 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_781 = lean_ctor_get(x_8, 12);
x_782 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_783 = lean_ctor_get(x_8, 13);
lean_inc(x_783);
lean_inc(x_781);
lean_inc(x_779);
lean_inc(x_778);
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
lean_dec(x_8);
x_784 = lean_nat_dec_eq(x_771, x_772);
if (x_784 == 0)
{
lean_object* x_785; 
x_785 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
if (lean_obj_tag(x_785) == 0)
{
lean_object* x_786; uint8_t x_787; 
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
x_787 = lean_unbox(x_786);
lean_dec(x_786);
if (x_787 == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; uint8_t x_1031; 
x_788 = lean_ctor_get(x_785, 1);
lean_inc(x_788);
lean_dec_ref(x_785);
x_789 = lean_unsigned_to_nat(1u);
x_790 = lean_nat_add(x_771, x_789);
lean_dec(x_771);
x_791 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_791, 0, x_768);
lean_ctor_set(x_791, 1, x_769);
lean_ctor_set(x_791, 2, x_770);
lean_ctor_set(x_791, 3, x_790);
lean_ctor_set(x_791, 4, x_772);
lean_ctor_set(x_791, 5, x_773);
lean_ctor_set(x_791, 6, x_774);
lean_ctor_set(x_791, 7, x_775);
lean_ctor_set(x_791, 8, x_776);
lean_ctor_set(x_791, 9, x_777);
lean_ctor_set(x_791, 10, x_778);
lean_ctor_set(x_791, 11, x_779);
lean_ctor_set(x_791, 12, x_781);
lean_ctor_set(x_791, 13, x_783);
lean_ctor_set_uint8(x_791, sizeof(void*)*14, x_780);
lean_ctor_set_uint8(x_791, sizeof(void*)*14 + 1, x_782);
x_921 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_922 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_921, x_791, x_788);
x_923 = lean_ctor_get(x_922, 0);
lean_inc(x_923);
x_924 = lean_ctor_get(x_922, 1);
lean_inc(x_924);
if (lean_is_exclusive(x_922)) {
 lean_ctor_release(x_922, 0);
 lean_ctor_release(x_922, 1);
 x_925 = x_922;
} else {
 lean_dec_ref(x_922);
 x_925 = lean_box(0);
}
x_926 = lean_box(0);
x_1031 = lean_unbox(x_923);
lean_dec(x_923);
if (x_1031 == 0)
{
x_955 = x_2;
x_956 = x_3;
x_957 = x_4;
x_958 = x_5;
x_959 = x_6;
x_960 = x_7;
x_961 = x_791;
x_962 = x_9;
x_963 = x_924;
goto block_1030;
}
else
{
lean_object* x_1032; 
lean_inc_ref(x_1);
x_1032 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_924);
if (lean_obj_tag(x_1032) == 0)
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1032, 1);
lean_inc(x_1034);
lean_dec_ref(x_1032);
x_1035 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_1036 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1036, 0, x_1035);
lean_ctor_set(x_1036, 1, x_1033);
x_1037 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1037, 0, x_1036);
lean_ctor_set(x_1037, 1, x_1035);
x_1038 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_921, x_1037, x_6, x_7, x_791, x_9, x_1034);
x_1039 = lean_ctor_get(x_1038, 1);
lean_inc(x_1039);
lean_dec_ref(x_1038);
x_955 = x_2;
x_956 = x_3;
x_957 = x_4;
x_958 = x_5;
x_959 = x_6;
x_960 = x_7;
x_961 = x_791;
x_962 = x_9;
x_963 = x_1039;
goto block_1030;
}
else
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
lean_dec(x_925);
lean_dec_ref(x_791);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1040 = lean_ctor_get(x_1032, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_1032, 1);
lean_inc(x_1041);
if (lean_is_exclusive(x_1032)) {
 lean_ctor_release(x_1032, 0);
 lean_ctor_release(x_1032, 1);
 x_1042 = x_1032;
} else {
 lean_dec_ref(x_1032);
 x_1042 = lean_box(0);
}
if (lean_is_scalar(x_1042)) {
 x_1043 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1043 = x_1042;
}
lean_ctor_set(x_1043, 0, x_1040);
lean_ctor_set(x_1043, 1, x_1041);
return x_1043;
}
}
block_920:
{
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; uint8_t x_811; 
lean_dec(x_803);
lean_dec_ref(x_802);
lean_dec(x_795);
lean_dec_ref(x_794);
lean_dec(x_793);
lean_dec(x_792);
x_808 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_809 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_808, x_805, x_799);
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
x_811 = lean_unbox(x_810);
lean_dec(x_810);
if (x_811 == 0)
{
lean_object* x_812; 
x_812 = lean_ctor_get(x_809, 1);
lean_inc(x_812);
lean_dec_ref(x_809);
x_11 = x_798;
x_12 = x_800;
x_13 = x_797;
x_14 = x_796;
x_15 = x_806;
x_16 = x_804;
x_17 = x_805;
x_18 = x_801;
x_19 = x_812;
goto block_166;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_809, 1);
lean_inc(x_813);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 x_814 = x_809;
} else {
 lean_dec_ref(x_809);
 x_814 = lean_box(0);
}
lean_inc_ref(x_798);
x_815 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_798, x_796, x_813);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_815, 1);
lean_inc(x_817);
lean_dec_ref(x_815);
x_818 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_814)) {
 x_819 = lean_alloc_ctor(7, 2, 0);
} else {
 x_819 = x_814;
 lean_ctor_set_tag(x_819, 7);
}
lean_ctor_set(x_819, 0, x_818);
lean_ctor_set(x_819, 1, x_816);
x_820 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_820, 0, x_819);
lean_ctor_set(x_820, 1, x_818);
x_821 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_808, x_820, x_806, x_804, x_805, x_801, x_817);
x_822 = lean_ctor_get(x_821, 1);
lean_inc(x_822);
lean_dec_ref(x_821);
x_11 = x_798;
x_12 = x_800;
x_13 = x_797;
x_14 = x_796;
x_15 = x_806;
x_16 = x_804;
x_17 = x_805;
x_18 = x_801;
x_19 = x_822;
goto block_166;
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; 
lean_dec(x_814);
lean_dec_ref(x_806);
lean_dec_ref(x_805);
lean_dec(x_804);
lean_dec(x_801);
lean_dec(x_800);
lean_dec_ref(x_798);
lean_dec_ref(x_797);
lean_dec(x_796);
x_823 = lean_ctor_get(x_815, 0);
lean_inc(x_823);
x_824 = lean_ctor_get(x_815, 1);
lean_inc(x_824);
if (lean_is_exclusive(x_815)) {
 lean_ctor_release(x_815, 0);
 lean_ctor_release(x_815, 1);
 x_825 = x_815;
} else {
 lean_dec_ref(x_815);
 x_825 = lean_box(0);
}
if (lean_is_scalar(x_825)) {
 x_826 = lean_alloc_ctor(1, 2, 0);
} else {
 x_826 = x_825;
}
lean_ctor_set(x_826, 0, x_823);
lean_ctor_set(x_826, 1, x_824);
return x_826;
}
}
}
else
{
lean_object* x_827; lean_object* x_828; 
lean_dec_ref(x_797);
x_827 = lean_ctor_get(x_807, 0);
lean_inc(x_827);
lean_dec_ref(x_807);
x_828 = lean_ctor_get(x_827, 1);
lean_inc_ref(x_828);
if (lean_obj_tag(x_828) == 0)
{
lean_object* x_829; 
lean_dec_ref(x_828);
lean_dec_ref(x_802);
lean_dec(x_800);
lean_dec_ref(x_798);
lean_dec(x_795);
lean_dec(x_793);
x_829 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_827, x_796, x_792, x_794, x_803, x_806, x_804, x_805, x_801, x_799);
lean_dec(x_801);
lean_dec_ref(x_805);
lean_dec(x_804);
lean_dec_ref(x_806);
lean_dec(x_803);
lean_dec_ref(x_794);
lean_dec(x_792);
lean_dec(x_796);
return x_829;
}
else
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; uint8_t x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; uint8_t x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; uint8_t x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_830 = lean_ctor_get(x_827, 0);
x_831 = lean_ctor_get(x_828, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_828, 2);
lean_inc_ref(x_832);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 lean_ctor_release(x_828, 2);
 x_833 = x_828;
} else {
 lean_dec_ref(x_828);
 x_833 = lean_box(0);
}
x_834 = lean_int_mul(x_793, x_830);
x_835 = lean_int_mul(x_831, x_795);
x_836 = l_Lean_Meta_Grind_Arith_gcdExt(x_834, x_835);
lean_dec(x_835);
lean_dec(x_834);
x_837 = lean_ctor_get(x_836, 1);
lean_inc(x_837);
x_838 = lean_ctor_get(x_836, 0);
lean_inc(x_838);
lean_dec_ref(x_836);
x_839 = lean_ctor_get(x_837, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_837, 1);
lean_inc(x_840);
lean_dec(x_837);
x_841 = lean_st_ref_take(x_796, x_799);
x_842 = lean_ctor_get(x_841, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_842, 14);
lean_inc_ref(x_843);
x_844 = lean_ctor_get(x_843, 1);
lean_inc_ref(x_844);
x_845 = lean_ctor_get(x_841, 1);
lean_inc(x_845);
lean_dec_ref(x_841);
x_846 = lean_ctor_get(x_842, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_842, 1);
lean_inc_ref(x_847);
x_848 = lean_ctor_get(x_842, 2);
lean_inc(x_848);
x_849 = lean_ctor_get(x_842, 3);
lean_inc_ref(x_849);
x_850 = lean_ctor_get(x_842, 4);
lean_inc_ref(x_850);
x_851 = lean_ctor_get(x_842, 5);
lean_inc_ref(x_851);
x_852 = lean_ctor_get(x_842, 6);
lean_inc_ref(x_852);
x_853 = lean_ctor_get(x_842, 7);
lean_inc_ref(x_853);
x_854 = lean_ctor_get_uint8(x_842, sizeof(void*)*16);
x_855 = lean_ctor_get(x_842, 8);
lean_inc(x_855);
x_856 = lean_ctor_get(x_842, 9);
lean_inc_ref(x_856);
x_857 = lean_ctor_get(x_842, 10);
lean_inc_ref(x_857);
x_858 = lean_ctor_get(x_842, 11);
lean_inc_ref(x_858);
x_859 = lean_ctor_get(x_842, 12);
lean_inc_ref(x_859);
x_860 = lean_ctor_get(x_842, 13);
lean_inc_ref(x_860);
x_861 = lean_ctor_get(x_842, 15);
lean_inc_ref(x_861);
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
 x_862 = x_842;
} else {
 lean_dec_ref(x_842);
 x_862 = lean_box(0);
}
x_863 = lean_ctor_get(x_843, 0);
lean_inc_ref(x_863);
x_864 = lean_ctor_get(x_843, 2);
lean_inc_ref(x_864);
x_865 = lean_ctor_get(x_843, 3);
lean_inc_ref(x_865);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 lean_ctor_release(x_843, 2);
 lean_ctor_release(x_843, 3);
 x_866 = x_843;
} else {
 lean_dec_ref(x_843);
 x_866 = lean_box(0);
}
x_867 = lean_ctor_get(x_844, 0);
lean_inc_ref(x_867);
x_868 = lean_ctor_get(x_844, 1);
lean_inc_ref(x_868);
x_869 = lean_ctor_get(x_844, 2);
lean_inc_ref(x_869);
x_870 = lean_ctor_get(x_844, 3);
lean_inc_ref(x_870);
x_871 = lean_ctor_get(x_844, 4);
lean_inc_ref(x_871);
x_872 = lean_ctor_get(x_844, 5);
lean_inc_ref(x_872);
x_873 = lean_ctor_get(x_844, 6);
lean_inc_ref(x_873);
x_874 = lean_ctor_get(x_844, 7);
lean_inc_ref(x_874);
x_875 = lean_ctor_get(x_844, 8);
lean_inc_ref(x_875);
x_876 = lean_ctor_get(x_844, 9);
lean_inc_ref(x_876);
x_877 = lean_ctor_get(x_844, 10);
lean_inc_ref(x_877);
x_878 = lean_ctor_get(x_844, 11);
lean_inc(x_878);
x_879 = lean_ctor_get(x_844, 12);
lean_inc_ref(x_879);
x_880 = lean_ctor_get(x_844, 13);
lean_inc_ref(x_880);
x_881 = lean_ctor_get(x_844, 14);
lean_inc(x_881);
x_882 = lean_ctor_get_uint8(x_844, sizeof(void*)*22);
x_883 = lean_ctor_get(x_844, 15);
lean_inc(x_883);
x_884 = lean_ctor_get(x_844, 16);
lean_inc_ref(x_884);
x_885 = lean_ctor_get(x_844, 17);
lean_inc_ref(x_885);
x_886 = lean_ctor_get(x_844, 18);
lean_inc_ref(x_886);
x_887 = lean_ctor_get(x_844, 19);
lean_inc_ref(x_887);
x_888 = lean_ctor_get(x_844, 20);
lean_inc_ref(x_888);
x_889 = lean_ctor_get_uint8(x_844, sizeof(void*)*22 + 1);
x_890 = lean_ctor_get(x_844, 21);
lean_inc_ref(x_890);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 lean_ctor_release(x_844, 2);
 lean_ctor_release(x_844, 3);
 lean_ctor_release(x_844, 4);
 lean_ctor_release(x_844, 5);
 lean_ctor_release(x_844, 6);
 lean_ctor_release(x_844, 7);
 lean_ctor_release(x_844, 8);
 lean_ctor_release(x_844, 9);
 lean_ctor_release(x_844, 10);
 lean_ctor_release(x_844, 11);
 lean_ctor_release(x_844, 12);
 lean_ctor_release(x_844, 13);
 lean_ctor_release(x_844, 14);
 lean_ctor_release(x_844, 15);
 lean_ctor_release(x_844, 16);
 lean_ctor_release(x_844, 17);
 lean_ctor_release(x_844, 18);
 lean_ctor_release(x_844, 19);
 lean_ctor_release(x_844, 20);
 lean_ctor_release(x_844, 21);
 x_891 = x_844;
} else {
 lean_dec_ref(x_844);
 x_891 = lean_box(0);
}
x_892 = lean_box(0);
x_893 = l_Lean_PersistentArray_set___redArg(x_873, x_800, x_892);
if (lean_is_scalar(x_891)) {
 x_894 = lean_alloc_ctor(0, 22, 2);
} else {
 x_894 = x_891;
}
lean_ctor_set(x_894, 0, x_867);
lean_ctor_set(x_894, 1, x_868);
lean_ctor_set(x_894, 2, x_869);
lean_ctor_set(x_894, 3, x_870);
lean_ctor_set(x_894, 4, x_871);
lean_ctor_set(x_894, 5, x_872);
lean_ctor_set(x_894, 6, x_893);
lean_ctor_set(x_894, 7, x_874);
lean_ctor_set(x_894, 8, x_875);
lean_ctor_set(x_894, 9, x_876);
lean_ctor_set(x_894, 10, x_877);
lean_ctor_set(x_894, 11, x_878);
lean_ctor_set(x_894, 12, x_879);
lean_ctor_set(x_894, 13, x_880);
lean_ctor_set(x_894, 14, x_881);
lean_ctor_set(x_894, 15, x_883);
lean_ctor_set(x_894, 16, x_884);
lean_ctor_set(x_894, 17, x_885);
lean_ctor_set(x_894, 18, x_886);
lean_ctor_set(x_894, 19, x_887);
lean_ctor_set(x_894, 20, x_888);
lean_ctor_set(x_894, 21, x_890);
lean_ctor_set_uint8(x_894, sizeof(void*)*22, x_882);
lean_ctor_set_uint8(x_894, sizeof(void*)*22 + 1, x_889);
if (lean_is_scalar(x_866)) {
 x_895 = lean_alloc_ctor(0, 4, 0);
} else {
 x_895 = x_866;
}
lean_ctor_set(x_895, 0, x_863);
lean_ctor_set(x_895, 1, x_894);
lean_ctor_set(x_895, 2, x_864);
lean_ctor_set(x_895, 3, x_865);
if (lean_is_scalar(x_862)) {
 x_896 = lean_alloc_ctor(0, 16, 1);
} else {
 x_896 = x_862;
}
lean_ctor_set(x_896, 0, x_846);
lean_ctor_set(x_896, 1, x_847);
lean_ctor_set(x_896, 2, x_848);
lean_ctor_set(x_896, 3, x_849);
lean_ctor_set(x_896, 4, x_850);
lean_ctor_set(x_896, 5, x_851);
lean_ctor_set(x_896, 6, x_852);
lean_ctor_set(x_896, 7, x_853);
lean_ctor_set(x_896, 8, x_855);
lean_ctor_set(x_896, 9, x_856);
lean_ctor_set(x_896, 10, x_857);
lean_ctor_set(x_896, 11, x_858);
lean_ctor_set(x_896, 12, x_859);
lean_ctor_set(x_896, 13, x_860);
lean_ctor_set(x_896, 14, x_895);
lean_ctor_set(x_896, 15, x_861);
lean_ctor_set_uint8(x_896, sizeof(void*)*16, x_854);
x_897 = lean_st_ref_set(x_796, x_896, x_845);
x_898 = lean_ctor_get(x_897, 1);
lean_inc(x_898);
if (lean_is_exclusive(x_897)) {
 lean_ctor_release(x_897, 0);
 lean_ctor_release(x_897, 1);
 x_899 = x_897;
} else {
 lean_dec_ref(x_897);
 x_899 = lean_box(0);
}
x_900 = lean_int_mul(x_839, x_830);
lean_dec(x_839);
lean_inc_ref(x_802);
x_901 = l_Int_Linear_Poly_mul(x_802, x_900);
lean_dec(x_900);
x_902 = lean_int_mul(x_840, x_795);
lean_dec(x_840);
lean_inc_ref(x_832);
x_903 = l_Int_Linear_Poly_mul(x_832, x_902);
lean_dec(x_902);
x_904 = lean_int_mul(x_795, x_830);
lean_dec(x_795);
x_905 = l_Int_Linear_Poly_combine(x_901, x_903);
lean_inc(x_838);
if (lean_is_scalar(x_833)) {
 x_906 = lean_alloc_ctor(1, 3, 0);
} else {
 x_906 = x_833;
}
lean_ctor_set(x_906, 0, x_838);
lean_ctor_set(x_906, 1, x_800);
lean_ctor_set(x_906, 2, x_905);
lean_inc(x_827);
lean_inc_ref(x_798);
if (lean_is_scalar(x_899)) {
 x_907 = lean_alloc_ctor(4, 2, 0);
} else {
 x_907 = x_899;
 lean_ctor_set_tag(x_907, 4);
}
lean_ctor_set(x_907, 0, x_798);
lean_ctor_set(x_907, 1, x_827);
x_908 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_908, 0, x_904);
lean_ctor_set(x_908, 1, x_906);
lean_ctor_set(x_908, 2, x_907);
lean_inc(x_801);
lean_inc_ref(x_805);
lean_inc(x_804);
lean_inc_ref(x_806);
lean_inc(x_803);
lean_inc_ref(x_794);
lean_inc(x_792);
lean_inc(x_796);
x_909 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_908, x_796, x_792, x_794, x_803, x_806, x_804, x_805, x_801, x_898);
if (lean_obj_tag(x_909) == 0)
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_910 = lean_ctor_get(x_909, 1);
lean_inc(x_910);
if (lean_is_exclusive(x_909)) {
 lean_ctor_release(x_909, 0);
 lean_ctor_release(x_909, 1);
 x_911 = x_909;
} else {
 lean_dec_ref(x_909);
 x_911 = lean_box(0);
}
x_912 = l_Int_Linear_Poly_mul(x_802, x_831);
lean_dec(x_831);
x_913 = lean_int_neg(x_793);
lean_dec(x_793);
x_914 = l_Int_Linear_Poly_mul(x_832, x_913);
lean_dec(x_913);
x_915 = l_Int_Linear_Poly_combine(x_912, x_914);
lean_inc(x_827);
if (lean_is_scalar(x_911)) {
 x_916 = lean_alloc_ctor(5, 2, 0);
} else {
 x_916 = x_911;
 lean_ctor_set_tag(x_916, 5);
}
lean_ctor_set(x_916, 0, x_798);
lean_ctor_set(x_916, 1, x_827);
if (lean_is_exclusive(x_827)) {
 lean_ctor_release(x_827, 0);
 lean_ctor_release(x_827, 1);
 lean_ctor_release(x_827, 2);
 x_917 = x_827;
} else {
 lean_dec_ref(x_827);
 x_917 = lean_box(0);
}
if (lean_is_scalar(x_917)) {
 x_918 = lean_alloc_ctor(0, 3, 0);
} else {
 x_918 = x_917;
}
lean_ctor_set(x_918, 0, x_838);
lean_ctor_set(x_918, 1, x_915);
lean_ctor_set(x_918, 2, x_916);
x_1 = x_918;
x_2 = x_796;
x_3 = x_792;
x_4 = x_794;
x_5 = x_803;
x_6 = x_806;
x_7 = x_804;
x_8 = x_805;
x_9 = x_801;
x_10 = x_910;
goto _start;
}
else
{
lean_dec(x_838);
lean_dec_ref(x_832);
lean_dec(x_831);
lean_dec(x_827);
lean_dec_ref(x_806);
lean_dec_ref(x_805);
lean_dec(x_804);
lean_dec(x_803);
lean_dec_ref(x_802);
lean_dec(x_801);
lean_dec_ref(x_798);
lean_dec(x_796);
lean_dec_ref(x_794);
lean_dec(x_793);
lean_dec(x_792);
return x_909;
}
}
}
}
block_954:
{
lean_object* x_942; 
x_942 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_933, x_941);
if (lean_obj_tag(x_942) == 0)
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; uint8_t x_947; 
x_943 = lean_ctor_get(x_942, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_943, 6);
lean_inc_ref(x_944);
lean_dec(x_943);
x_945 = lean_ctor_get(x_942, 1);
lean_inc(x_945);
lean_dec_ref(x_942);
x_946 = lean_ctor_get(x_944, 2);
x_947 = lean_nat_dec_lt(x_929, x_946);
if (x_947 == 0)
{
lean_object* x_948; 
lean_dec_ref(x_944);
x_948 = l_outOfBounds___redArg(x_926);
x_792 = x_934;
x_793 = x_928;
x_794 = x_935;
x_795 = x_930;
x_796 = x_933;
x_797 = x_932;
x_798 = x_927;
x_799 = x_945;
x_800 = x_929;
x_801 = x_940;
x_802 = x_931;
x_803 = x_936;
x_804 = x_938;
x_805 = x_939;
x_806 = x_937;
x_807 = x_948;
goto block_920;
}
else
{
lean_object* x_949; 
x_949 = l_Lean_PersistentArray_get_x21___redArg(x_926, x_944, x_929);
x_792 = x_934;
x_793 = x_928;
x_794 = x_935;
x_795 = x_930;
x_796 = x_933;
x_797 = x_932;
x_798 = x_927;
x_799 = x_945;
x_800 = x_929;
x_801 = x_940;
x_802 = x_931;
x_803 = x_936;
x_804 = x_938;
x_805 = x_939;
x_806 = x_937;
x_807 = x_949;
goto block_920;
}
}
else
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; 
lean_dec(x_940);
lean_dec_ref(x_939);
lean_dec(x_938);
lean_dec_ref(x_937);
lean_dec(x_936);
lean_dec_ref(x_935);
lean_dec(x_934);
lean_dec(x_933);
lean_dec_ref(x_932);
lean_dec_ref(x_931);
lean_dec(x_930);
lean_dec(x_929);
lean_dec(x_928);
lean_dec_ref(x_927);
x_950 = lean_ctor_get(x_942, 0);
lean_inc(x_950);
x_951 = lean_ctor_get(x_942, 1);
lean_inc(x_951);
if (lean_is_exclusive(x_942)) {
 lean_ctor_release(x_942, 0);
 lean_ctor_release(x_942, 1);
 x_952 = x_942;
} else {
 lean_dec_ref(x_942);
 x_952 = lean_box(0);
}
if (lean_is_scalar(x_952)) {
 x_953 = lean_alloc_ctor(1, 2, 0);
} else {
 x_953 = x_952;
}
lean_ctor_set(x_953, 0, x_950);
lean_ctor_set(x_953, 1, x_951);
return x_953;
}
}
block_1030:
{
lean_object* x_964; lean_object* x_965; 
x_964 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_961);
x_965 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_964, x_955, x_956, x_957, x_958, x_959, x_960, x_961, x_962, x_963);
if (lean_obj_tag(x_965) == 0)
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; uint8_t x_970; 
x_966 = lean_ctor_get(x_965, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_965, 1);
lean_inc(x_967);
lean_dec_ref(x_965);
x_968 = lean_ctor_get(x_966, 0);
x_969 = lean_ctor_get(x_966, 1);
lean_inc(x_968);
x_970 = l_Int_Linear_Poly_isUnsatDvd(x_968, x_969);
if (x_970 == 0)
{
uint8_t x_971; 
x_971 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_966);
if (x_971 == 0)
{
lean_dec(x_925);
if (lean_obj_tag(x_969) == 0)
{
lean_object* x_972; 
x_972 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_966, x_955, x_956, x_957, x_958, x_959, x_960, x_961, x_962, x_967);
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_958);
lean_dec_ref(x_957);
lean_dec(x_956);
lean_dec(x_955);
return x_972;
}
else
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; 
lean_inc_ref(x_969);
lean_inc(x_968);
x_973 = lean_ctor_get(x_969, 0);
lean_inc(x_973);
x_974 = lean_ctor_get(x_969, 1);
lean_inc(x_974);
x_975 = lean_ctor_get(x_969, 2);
lean_inc_ref(x_975);
lean_inc(x_966);
x_976 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_966, x_955, x_967);
if (lean_obj_tag(x_976) == 0)
{
lean_object* x_977; lean_object* x_978; uint8_t x_979; uint8_t x_980; uint8_t x_981; 
x_977 = lean_ctor_get(x_976, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_976, 1);
lean_inc(x_978);
lean_dec_ref(x_976);
x_979 = 0;
x_980 = lean_unbox(x_977);
lean_dec(x_977);
x_981 = l_Lean_beqLBool____x40_Lean_Data_LBool_27903016____hygCtx___hyg_9_(x_980, x_979);
if (x_981 == 0)
{
x_927 = x_966;
x_928 = x_973;
x_929 = x_974;
x_930 = x_968;
x_931 = x_975;
x_932 = x_969;
x_933 = x_955;
x_934 = x_956;
x_935 = x_957;
x_936 = x_958;
x_937 = x_959;
x_938 = x_960;
x_939 = x_961;
x_940 = x_962;
x_941 = x_978;
goto block_954;
}
else
{
lean_object* x_982; 
x_982 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_974, x_955, x_978);
if (lean_obj_tag(x_982) == 0)
{
lean_object* x_983; 
x_983 = lean_ctor_get(x_982, 1);
lean_inc(x_983);
lean_dec_ref(x_982);
x_927 = x_966;
x_928 = x_973;
x_929 = x_974;
x_930 = x_968;
x_931 = x_975;
x_932 = x_969;
x_933 = x_955;
x_934 = x_956;
x_935 = x_957;
x_936 = x_958;
x_937 = x_959;
x_938 = x_960;
x_939 = x_961;
x_940 = x_962;
x_941 = x_983;
goto block_954;
}
else
{
lean_dec_ref(x_975);
lean_dec(x_974);
lean_dec(x_973);
lean_dec_ref(x_969);
lean_dec(x_968);
lean_dec(x_966);
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_958);
lean_dec_ref(x_957);
lean_dec(x_956);
lean_dec(x_955);
return x_982;
}
}
}
else
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
lean_dec_ref(x_975);
lean_dec(x_974);
lean_dec(x_973);
lean_dec_ref(x_969);
lean_dec(x_968);
lean_dec(x_966);
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_958);
lean_dec_ref(x_957);
lean_dec(x_956);
lean_dec(x_955);
x_984 = lean_ctor_get(x_976, 0);
lean_inc(x_984);
x_985 = lean_ctor_get(x_976, 1);
lean_inc(x_985);
if (lean_is_exclusive(x_976)) {
 lean_ctor_release(x_976, 0);
 lean_ctor_release(x_976, 1);
 x_986 = x_976;
} else {
 lean_dec_ref(x_976);
 x_986 = lean_box(0);
}
if (lean_is_scalar(x_986)) {
 x_987 = lean_alloc_ctor(1, 2, 0);
} else {
 x_987 = x_986;
}
lean_ctor_set(x_987, 0, x_984);
lean_ctor_set(x_987, 1, x_985);
return x_987;
}
}
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; uint8_t x_991; 
lean_dec(x_958);
lean_dec_ref(x_957);
lean_dec(x_956);
x_988 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_989 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_988, x_961, x_967);
x_990 = lean_ctor_get(x_989, 0);
lean_inc(x_990);
x_991 = lean_unbox(x_990);
lean_dec(x_990);
if (x_991 == 0)
{
lean_object* x_992; 
lean_dec(x_966);
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_955);
lean_dec(x_925);
x_992 = lean_ctor_get(x_989, 1);
lean_inc(x_992);
lean_dec_ref(x_989);
x_186 = x_992;
goto block_189;
}
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_993 = lean_ctor_get(x_989, 1);
lean_inc(x_993);
if (lean_is_exclusive(x_989)) {
 lean_ctor_release(x_989, 0);
 lean_ctor_release(x_989, 1);
 x_994 = x_989;
} else {
 lean_dec_ref(x_989);
 x_994 = lean_box(0);
}
x_995 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_966, x_955, x_993);
lean_dec(x_955);
if (lean_obj_tag(x_995) == 0)
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
x_996 = lean_ctor_get(x_995, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_995, 1);
lean_inc(x_997);
lean_dec_ref(x_995);
x_998 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_994)) {
 x_999 = lean_alloc_ctor(7, 2, 0);
} else {
 x_999 = x_994;
 lean_ctor_set_tag(x_999, 7);
}
lean_ctor_set(x_999, 0, x_998);
lean_ctor_set(x_999, 1, x_996);
if (lean_is_scalar(x_925)) {
 x_1000 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1000 = x_925;
 lean_ctor_set_tag(x_1000, 7);
}
lean_ctor_set(x_1000, 0, x_999);
lean_ctor_set(x_1000, 1, x_998);
x_1001 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_988, x_1000, x_959, x_960, x_961, x_962, x_997);
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec_ref(x_959);
x_1002 = lean_ctor_get(x_1001, 1);
lean_inc(x_1002);
lean_dec_ref(x_1001);
x_186 = x_1002;
goto block_189;
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
lean_dec(x_994);
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_925);
x_1003 = lean_ctor_get(x_995, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_995, 1);
lean_inc(x_1004);
if (lean_is_exclusive(x_995)) {
 lean_ctor_release(x_995, 0);
 lean_ctor_release(x_995, 1);
 x_1005 = x_995;
} else {
 lean_dec_ref(x_995);
 x_1005 = lean_box(0);
}
if (lean_is_scalar(x_1005)) {
 x_1006 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1006 = x_1005;
}
lean_ctor_set(x_1006, 0, x_1003);
lean_ctor_set(x_1006, 1, x_1004);
return x_1006;
}
}
}
}
else
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; uint8_t x_1010; 
x_1007 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_1008 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_1007, x_961, x_967);
x_1009 = lean_ctor_get(x_1008, 0);
lean_inc(x_1009);
x_1010 = lean_unbox(x_1009);
lean_dec(x_1009);
if (x_1010 == 0)
{
lean_object* x_1011; 
lean_dec(x_925);
x_1011 = lean_ctor_get(x_1008, 1);
lean_inc(x_1011);
lean_dec_ref(x_1008);
x_167 = x_966;
x_168 = x_955;
x_169 = x_956;
x_170 = x_957;
x_171 = x_958;
x_172 = x_959;
x_173 = x_960;
x_174 = x_961;
x_175 = x_962;
x_176 = x_1011;
goto block_185;
}
else
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; 
x_1012 = lean_ctor_get(x_1008, 1);
lean_inc(x_1012);
if (lean_is_exclusive(x_1008)) {
 lean_ctor_release(x_1008, 0);
 lean_ctor_release(x_1008, 1);
 x_1013 = x_1008;
} else {
 lean_dec_ref(x_1008);
 x_1013 = lean_box(0);
}
lean_inc(x_966);
x_1014 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_966, x_955, x_1012);
if (lean_obj_tag(x_1014) == 0)
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1015 = lean_ctor_get(x_1014, 0);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_1014, 1);
lean_inc(x_1016);
lean_dec_ref(x_1014);
x_1017 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
if (lean_is_scalar(x_1013)) {
 x_1018 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1018 = x_1013;
 lean_ctor_set_tag(x_1018, 7);
}
lean_ctor_set(x_1018, 0, x_1017);
lean_ctor_set(x_1018, 1, x_1015);
if (lean_is_scalar(x_925)) {
 x_1019 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1019 = x_925;
 lean_ctor_set_tag(x_1019, 7);
}
lean_ctor_set(x_1019, 0, x_1018);
lean_ctor_set(x_1019, 1, x_1017);
x_1020 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_1007, x_1019, x_959, x_960, x_961, x_962, x_1016);
x_1021 = lean_ctor_get(x_1020, 1);
lean_inc(x_1021);
lean_dec_ref(x_1020);
x_167 = x_966;
x_168 = x_955;
x_169 = x_956;
x_170 = x_957;
x_171 = x_958;
x_172 = x_959;
x_173 = x_960;
x_174 = x_961;
x_175 = x_962;
x_176 = x_1021;
goto block_185;
}
else
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
lean_dec(x_1013);
lean_dec(x_966);
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_958);
lean_dec_ref(x_957);
lean_dec(x_956);
lean_dec(x_955);
lean_dec(x_925);
x_1022 = lean_ctor_get(x_1014, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1014, 1);
lean_inc(x_1023);
if (lean_is_exclusive(x_1014)) {
 lean_ctor_release(x_1014, 0);
 lean_ctor_release(x_1014, 1);
 x_1024 = x_1014;
} else {
 lean_dec_ref(x_1014);
 x_1024 = lean_box(0);
}
if (lean_is_scalar(x_1024)) {
 x_1025 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1025 = x_1024;
}
lean_ctor_set(x_1025, 0, x_1022);
lean_ctor_set(x_1025, 1, x_1023);
return x_1025;
}
}
}
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
lean_dec(x_962);
lean_dec_ref(x_961);
lean_dec(x_960);
lean_dec_ref(x_959);
lean_dec(x_958);
lean_dec_ref(x_957);
lean_dec(x_956);
lean_dec(x_955);
lean_dec(x_925);
x_1026 = lean_ctor_get(x_965, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_965, 1);
lean_inc(x_1027);
if (lean_is_exclusive(x_965)) {
 lean_ctor_release(x_965, 0);
 lean_ctor_release(x_965, 1);
 x_1028 = x_965;
} else {
 lean_dec_ref(x_965);
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
else
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_771);
lean_dec(x_770);
lean_dec_ref(x_769);
lean_dec_ref(x_768);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1044 = lean_ctor_get(x_785, 1);
lean_inc(x_1044);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_1045 = x_785;
} else {
 lean_dec_ref(x_785);
 x_1045 = lean_box(0);
}
x_1046 = lean_box(0);
if (lean_is_scalar(x_1045)) {
 x_1047 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1047 = x_1045;
}
lean_ctor_set(x_1047, 0, x_1046);
lean_ctor_set(x_1047, 1, x_1044);
return x_1047;
}
}
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_771);
lean_dec(x_770);
lean_dec_ref(x_769);
lean_dec_ref(x_768);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1048 = lean_ctor_get(x_785, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_785, 1);
lean_inc(x_1049);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_1050 = x_785;
} else {
 lean_dec_ref(x_785);
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
else
{
lean_object* x_1052; 
lean_dec_ref(x_783);
lean_dec(x_781);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_772);
lean_dec(x_771);
lean_dec(x_770);
lean_dec_ref(x_769);
lean_dec_ref(x_768);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1052 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_773, x_10);
return x_1052;
}
}
block_166:
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
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_111 = lean_ctor_get(x_23, 0);
x_112 = lean_ctor_get(x_23, 1);
x_113 = lean_ctor_get(x_23, 2);
x_114 = lean_ctor_get(x_23, 3);
x_115 = lean_ctor_get(x_23, 4);
x_116 = lean_ctor_get(x_23, 5);
x_117 = lean_ctor_get(x_23, 6);
x_118 = lean_ctor_get(x_23, 7);
x_119 = lean_ctor_get_uint8(x_23, sizeof(void*)*16);
x_120 = lean_ctor_get(x_23, 8);
x_121 = lean_ctor_get(x_23, 9);
x_122 = lean_ctor_get(x_23, 10);
x_123 = lean_ctor_get(x_23, 11);
x_124 = lean_ctor_get(x_23, 12);
x_125 = lean_ctor_get(x_23, 13);
x_126 = lean_ctor_get(x_23, 15);
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
x_127 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_24, 3);
lean_inc_ref(x_129);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 x_130 = x_24;
} else {
 lean_dec_ref(x_24);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_25, 4);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_25, 5);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_25, 6);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_25, 7);
lean_inc_ref(x_138);
x_139 = lean_ctor_get(x_25, 8);
lean_inc_ref(x_139);
x_140 = lean_ctor_get(x_25, 9);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_25, 10);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_25, 11);
lean_inc(x_142);
x_143 = lean_ctor_get(x_25, 12);
lean_inc_ref(x_143);
x_144 = lean_ctor_get(x_25, 13);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_25, 14);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_25, sizeof(void*)*22);
x_147 = lean_ctor_get(x_25, 15);
lean_inc(x_147);
x_148 = lean_ctor_get(x_25, 16);
lean_inc_ref(x_148);
x_149 = lean_ctor_get(x_25, 17);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_25, 18);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_25, 19);
lean_inc_ref(x_151);
x_152 = lean_ctor_get(x_25, 20);
lean_inc_ref(x_152);
x_153 = lean_ctor_get_uint8(x_25, sizeof(void*)*22 + 1);
x_154 = lean_ctor_get(x_25, 21);
lean_inc_ref(x_154);
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
 x_155 = x_25;
} else {
 lean_dec_ref(x_25);
 x_155 = lean_box(0);
}
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_11);
x_157 = l_Lean_PersistentArray_set___redArg(x_137, x_12, x_156);
lean_dec(x_12);
if (lean_is_scalar(x_155)) {
 x_158 = lean_alloc_ctor(0, 22, 2);
} else {
 x_158 = x_155;
}
lean_ctor_set(x_158, 0, x_131);
lean_ctor_set(x_158, 1, x_132);
lean_ctor_set(x_158, 2, x_133);
lean_ctor_set(x_158, 3, x_134);
lean_ctor_set(x_158, 4, x_135);
lean_ctor_set(x_158, 5, x_136);
lean_ctor_set(x_158, 6, x_157);
lean_ctor_set(x_158, 7, x_138);
lean_ctor_set(x_158, 8, x_139);
lean_ctor_set(x_158, 9, x_140);
lean_ctor_set(x_158, 10, x_141);
lean_ctor_set(x_158, 11, x_142);
lean_ctor_set(x_158, 12, x_143);
lean_ctor_set(x_158, 13, x_144);
lean_ctor_set(x_158, 14, x_145);
lean_ctor_set(x_158, 15, x_147);
lean_ctor_set(x_158, 16, x_148);
lean_ctor_set(x_158, 17, x_149);
lean_ctor_set(x_158, 18, x_150);
lean_ctor_set(x_158, 19, x_151);
lean_ctor_set(x_158, 20, x_152);
lean_ctor_set(x_158, 21, x_154);
lean_ctor_set_uint8(x_158, sizeof(void*)*22, x_146);
lean_ctor_set_uint8(x_158, sizeof(void*)*22 + 1, x_153);
if (lean_is_scalar(x_130)) {
 x_159 = lean_alloc_ctor(0, 4, 0);
} else {
 x_159 = x_130;
}
lean_ctor_set(x_159, 0, x_127);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_159, 2, x_128);
lean_ctor_set(x_159, 3, x_129);
x_160 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_160, 0, x_111);
lean_ctor_set(x_160, 1, x_112);
lean_ctor_set(x_160, 2, x_113);
lean_ctor_set(x_160, 3, x_114);
lean_ctor_set(x_160, 4, x_115);
lean_ctor_set(x_160, 5, x_116);
lean_ctor_set(x_160, 6, x_117);
lean_ctor_set(x_160, 7, x_118);
lean_ctor_set(x_160, 8, x_120);
lean_ctor_set(x_160, 9, x_121);
lean_ctor_set(x_160, 10, x_122);
lean_ctor_set(x_160, 11, x_123);
lean_ctor_set(x_160, 12, x_124);
lean_ctor_set(x_160, 13, x_125);
lean_ctor_set(x_160, 14, x_159);
lean_ctor_set(x_160, 15, x_126);
lean_ctor_set_uint8(x_160, sizeof(void*)*16, x_119);
x_161 = lean_st_ref_set(x_14, x_160, x_26);
lean_dec(x_14);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
x_164 = lean_box(0);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
return x_165;
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
block_185:
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_167);
x_178 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_177, x_168, x_169, x_170, x_171, x_172, x_173, x_174, x_175, x_176);
if (lean_obj_tag(x_178) == 0)
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_178, 0);
lean_dec(x_180);
x_181 = lean_box(0);
lean_ctor_set(x_178, 0, x_181);
return x_178;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_178, 1);
lean_inc(x_182);
lean_dec(x_178);
x_183 = lean_box(0);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
else
{
return x_178;
}
}
block_189:
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_box(0);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_186);
return x_188;
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1830001947____hygCtx___hyg_8_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

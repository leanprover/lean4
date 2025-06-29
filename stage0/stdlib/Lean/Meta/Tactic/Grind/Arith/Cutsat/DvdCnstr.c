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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__5;
lean_object* l_Lean_Meta_isInstDvdInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__3;
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_OfNat_toIntDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Int_Linear_Poly_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__4;
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_reflBoolTrue;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6;
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
lean_object* l_Int_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__2;
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2765_(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
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
lean_inc(x_32);
x_33 = l_Int_Linear_Poly_isSorted(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Int_Linear_Poly_norm(x_32);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_1);
lean_inc(x_34);
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
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_int_ediv(x_5, x_3);
lean_dec(x_5);
x_8 = l_Int_Linear_Poly_div(x_3, x_2);
lean_dec(x_3);
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
x_17 = l_Int_Linear_Poly_getConst(x_12);
x_18 = lean_int_emod(x_17, x_16);
lean_dec(x_17);
x_19 = lean_int_dec_eq(x_18, x_14);
lean_dec(x_14);
lean_dec(x_18);
if (x_19 == 0)
{
x_2 = x_12;
x_3 = x_16;
x_4 = x_13;
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
x_2 = x_12;
x_3 = x_16;
x_4 = x_13;
x_5 = x_15;
x_6 = x_19;
goto block_11;
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
return x_13;
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
x_12 = x_25;
x_13 = x_23;
x_14 = x_27;
x_15 = x_24;
x_16 = x_26;
goto block_22;
}
else
{
lean_object* x_29; 
x_29 = lean_int_neg(x_26);
lean_dec(x_26);
x_12 = x_25;
x_13 = x_23;
x_14 = x_27;
x_15 = x_24;
x_16 = x_29;
goto block_22;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cutsat", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__3;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_32; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__4;
x_13 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_12, x_9, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
x_20 = lean_int_mul(x_1, x_18);
lean_dec(x_18);
x_21 = lean_nat_abs(x_20);
lean_dec(x_20);
x_22 = lean_nat_to_int(x_21);
x_23 = l_Int_Linear_Poly_mul(x_19, x_1);
x_24 = lean_int_neg(x_4);
x_25 = l_Int_Linear_Poly_mul(x_17, x_24);
lean_dec(x_24);
x_26 = l_Int_Linear_Poly_combine(x_23, x_25);
x_32 = lean_unbox(x_14);
lean_dec(x_14);
if (x_32 == 0)
{
x_27 = x_15;
goto block_31;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(x_2, x_6, x_15);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_3);
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_3, x_6, x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_5);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_5, x_6, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_46 = l_Lean_MessageData_ofExpr(x_35);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_46);
lean_ctor_set(x_41, 0, x_45);
x_47 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__8;
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_47);
lean_ctor_set(x_37, 0, x_41);
lean_ctor_set_tag(x_33, 7);
lean_ctor_set(x_33, 1, x_39);
lean_ctor_set(x_33, 0, x_37);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
x_51 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_12, x_50, x_7, x_8, x_9, x_10, x_44);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_27 = x_52;
goto block_31;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
x_55 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_56 = l_Lean_MessageData_ofExpr(x_35);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__8;
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_58);
lean_ctor_set(x_37, 0, x_57);
lean_ctor_set_tag(x_33, 7);
lean_ctor_set(x_33, 1, x_39);
lean_ctor_set(x_33, 0, x_37);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_33);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
x_62 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_12, x_61, x_7, x_8, x_9, x_10, x_54);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_27 = x_63;
goto block_31;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_64 = lean_ctor_get(x_37, 0);
x_65 = lean_ctor_get(x_37, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_37);
lean_inc(x_5);
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_5, x_6, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_71 = l_Lean_MessageData_ofExpr(x_35);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(7, 2, 0);
} else {
 x_72 = x_69;
 lean_ctor_set_tag(x_72, 7);
}
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__8;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_tag(x_33, 7);
lean_ctor_set(x_33, 1, x_64);
lean_ctor_set(x_33, 0, x_74);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_33);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_67);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_70);
x_78 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_12, x_77, x_7, x_8, x_9, x_10, x_68);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_27 = x_79;
goto block_31;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_80 = lean_ctor_get(x_33, 0);
x_81 = lean_ctor_get(x_33, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_33);
lean_inc(x_3);
x_82 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_3, x_6, x_81);
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
lean_inc(x_5);
x_86 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_5, x_6, x_84);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_91 = l_Lean_MessageData_ofExpr(x_80);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(7, 2, 0);
} else {
 x_92 = x_89;
 lean_ctor_set_tag(x_92, 7);
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__8;
if (lean_is_scalar(x_85)) {
 x_94 = lean_alloc_ctor(7, 2, 0);
} else {
 x_94 = x_85;
 lean_ctor_set_tag(x_94, 7);
}
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_83);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_87);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_90);
x_99 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_12, x_98, x_7, x_8, x_9, x_10, x_88);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_27 = x_100;
goto block_31;
}
}
block_31:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_5);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
if (lean_is_scalar(x_16)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_16;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_23 = lean_ctor_get(x_1, 1);
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
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg(x_39, x_35, x_32, x_34, x_1, x_2, x_3, x_4, x_5, x_6, x_33);
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
x_61 = lean_ctor_get(x_1, 1);
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
x_78 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg(x_77, x_72, x_69, x_71, x_1, x_2, x_3, x_4, x_76, x_6, x_70);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
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
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__0;
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
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__0;
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
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__0;
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
lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_202 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_unbox(x_203);
lean_dec(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_598; lean_object* x_599; uint8_t x_600; 
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
x_206 = lean_unsigned_to_nat(1u);
x_207 = lean_nat_add(x_191, x_206);
lean_dec(x_191);
lean_ctor_set(x_8, 3, x_207);
x_598 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_599 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_598, x_8, x_205);
x_600 = !lean_is_exclusive(x_599);
if (x_600 == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; uint8_t x_725; 
x_601 = lean_ctor_get(x_599, 0);
x_602 = lean_ctor_get(x_599, 1);
x_603 = lean_box(0);
x_725 = lean_unbox(x_601);
lean_dec(x_601);
if (x_725 == 0)
{
lean_free_object(x_599);
x_628 = x_2;
x_629 = x_3;
x_630 = x_4;
x_631 = x_5;
x_632 = x_6;
x_633 = x_7;
x_634 = x_8;
x_635 = x_9;
x_636 = x_602;
goto block_724;
}
else
{
lean_object* x_726; uint8_t x_727; 
lean_inc(x_1);
x_726 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_602);
x_727 = !lean_is_exclusive(x_726);
if (x_727 == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_728 = lean_ctor_get(x_726, 0);
x_729 = lean_ctor_get(x_726, 1);
x_730 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_726, 7);
lean_ctor_set(x_726, 1, x_728);
lean_ctor_set(x_726, 0, x_730);
lean_ctor_set_tag(x_599, 7);
lean_ctor_set(x_599, 1, x_730);
lean_ctor_set(x_599, 0, x_726);
x_731 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_598, x_599, x_6, x_7, x_8, x_9, x_729);
x_732 = lean_ctor_get(x_731, 1);
lean_inc(x_732);
lean_dec(x_731);
x_628 = x_2;
x_629 = x_3;
x_630 = x_4;
x_631 = x_5;
x_632 = x_6;
x_633 = x_7;
x_634 = x_8;
x_635 = x_9;
x_636 = x_732;
goto block_724;
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_733 = lean_ctor_get(x_726, 0);
x_734 = lean_ctor_get(x_726, 1);
lean_inc(x_734);
lean_inc(x_733);
lean_dec(x_726);
x_735 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_736 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_736, 0, x_735);
lean_ctor_set(x_736, 1, x_733);
lean_ctor_set_tag(x_599, 7);
lean_ctor_set(x_599, 1, x_735);
lean_ctor_set(x_599, 0, x_736);
x_737 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_598, x_599, x_6, x_7, x_8, x_9, x_734);
x_738 = lean_ctor_get(x_737, 1);
lean_inc(x_738);
lean_dec(x_737);
x_628 = x_2;
x_629 = x_3;
x_630 = x_4;
x_631 = x_5;
x_632 = x_6;
x_633 = x_7;
x_634 = x_8;
x_635 = x_9;
x_636 = x_738;
goto block_724;
}
}
block_627:
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; 
x_619 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_610, x_618);
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_620, 7);
lean_inc(x_621);
lean_dec(x_620);
x_622 = lean_ctor_get(x_619, 1);
lean_inc(x_622);
lean_dec(x_619);
x_623 = lean_ctor_get(x_621, 2);
lean_inc(x_623);
x_624 = lean_nat_dec_lt(x_608, x_623);
lean_dec(x_623);
if (x_624 == 0)
{
lean_object* x_625; 
lean_dec(x_621);
x_625 = l_outOfBounds___redArg(x_603);
x_208 = x_605;
x_209 = x_614;
x_210 = x_607;
x_211 = x_608;
x_212 = x_615;
x_213 = x_622;
x_214 = x_604;
x_215 = x_606;
x_216 = x_617;
x_217 = x_611;
x_218 = x_616;
x_219 = x_612;
x_220 = x_610;
x_221 = x_613;
x_222 = x_609;
x_223 = x_625;
goto block_597;
}
else
{
lean_object* x_626; 
x_626 = l_Lean_PersistentArray_get_x21___redArg(x_603, x_621, x_608);
x_208 = x_605;
x_209 = x_614;
x_210 = x_607;
x_211 = x_608;
x_212 = x_615;
x_213 = x_622;
x_214 = x_604;
x_215 = x_606;
x_216 = x_617;
x_217 = x_611;
x_218 = x_616;
x_219 = x_612;
x_220 = x_610;
x_221 = x_613;
x_222 = x_609;
x_223 = x_626;
goto block_597;
}
}
block_724:
{
lean_object* x_637; lean_object* x_638; 
x_637 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_634);
x_638 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_637, x_628, x_632, x_633, x_634, x_635, x_636);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; uint8_t x_643; 
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_638, 1);
lean_inc(x_640);
lean_dec(x_638);
x_641 = lean_ctor_get(x_639, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_639, 1);
lean_inc(x_642);
lean_inc(x_641);
x_643 = l_Int_Linear_Poly_isUnsatDvd(x_641, x_642);
if (x_643 == 0)
{
uint8_t x_644; 
x_644 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_639);
if (x_644 == 0)
{
if (lean_obj_tag(x_642) == 0)
{
lean_object* x_645; 
lean_dec(x_642);
lean_dec(x_641);
lean_dec(x_631);
lean_dec(x_630);
lean_dec(x_629);
x_645 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_639, x_628, x_632, x_633, x_634, x_635, x_640);
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_632);
lean_dec(x_628);
return x_645;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; uint8_t x_653; uint8_t x_654; uint8_t x_655; 
x_646 = lean_ctor_get(x_642, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_642, 1);
lean_inc(x_647);
x_648 = lean_ctor_get(x_642, 2);
lean_inc(x_648);
lean_inc(x_639);
x_649 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_639, x_628, x_640);
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_649, 1);
lean_inc(x_651);
lean_dec(x_649);
x_652 = lean_box(0);
x_653 = lean_unbox(x_650);
lean_dec(x_650);
x_654 = lean_unbox(x_652);
x_655 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_653, x_654);
if (x_655 == 0)
{
x_604 = x_642;
x_605 = x_639;
x_606 = x_641;
x_607 = x_646;
x_608 = x_647;
x_609 = x_648;
x_610 = x_628;
x_611 = x_629;
x_612 = x_630;
x_613 = x_631;
x_614 = x_632;
x_615 = x_633;
x_616 = x_634;
x_617 = x_635;
x_618 = x_651;
goto block_627;
}
else
{
lean_object* x_656; lean_object* x_657; 
x_656 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_647, x_628, x_651);
x_657 = lean_ctor_get(x_656, 1);
lean_inc(x_657);
lean_dec(x_656);
x_604 = x_642;
x_605 = x_639;
x_606 = x_641;
x_607 = x_646;
x_608 = x_647;
x_609 = x_648;
x_610 = x_628;
x_611 = x_629;
x_612 = x_630;
x_613 = x_631;
x_614 = x_632;
x_615 = x_633;
x_616 = x_634;
x_617 = x_635;
x_618 = x_657;
goto block_627;
}
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; uint8_t x_661; 
lean_dec(x_642);
lean_dec(x_641);
lean_dec(x_631);
lean_dec(x_630);
lean_dec(x_629);
x_658 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_659 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_658, x_634, x_640);
x_660 = lean_ctor_get(x_659, 0);
lean_inc(x_660);
x_661 = lean_unbox(x_660);
lean_dec(x_660);
if (x_661 == 0)
{
lean_object* x_662; 
lean_dec(x_639);
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_632);
lean_dec(x_628);
x_662 = lean_ctor_get(x_659, 1);
lean_inc(x_662);
lean_dec(x_659);
x_183 = x_662;
goto block_186;
}
else
{
uint8_t x_663; 
x_663 = !lean_is_exclusive(x_659);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; uint8_t x_667; 
x_664 = lean_ctor_get(x_659, 1);
x_665 = lean_ctor_get(x_659, 0);
lean_dec(x_665);
x_666 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_639, x_628, x_664);
lean_dec(x_628);
x_667 = !lean_is_exclusive(x_666);
if (x_667 == 0)
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_668 = lean_ctor_get(x_666, 0);
x_669 = lean_ctor_get(x_666, 1);
x_670 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_666, 7);
lean_ctor_set(x_666, 1, x_668);
lean_ctor_set(x_666, 0, x_670);
lean_ctor_set_tag(x_659, 7);
lean_ctor_set(x_659, 1, x_670);
lean_ctor_set(x_659, 0, x_666);
x_671 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_658, x_659, x_632, x_633, x_634, x_635, x_669);
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_632);
x_672 = lean_ctor_get(x_671, 1);
lean_inc(x_672);
lean_dec(x_671);
x_183 = x_672;
goto block_186;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_673 = lean_ctor_get(x_666, 0);
x_674 = lean_ctor_get(x_666, 1);
lean_inc(x_674);
lean_inc(x_673);
lean_dec(x_666);
x_675 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_676 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_676, 0, x_675);
lean_ctor_set(x_676, 1, x_673);
lean_ctor_set_tag(x_659, 7);
lean_ctor_set(x_659, 1, x_675);
lean_ctor_set(x_659, 0, x_676);
x_677 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_658, x_659, x_632, x_633, x_634, x_635, x_674);
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_632);
x_678 = lean_ctor_get(x_677, 1);
lean_inc(x_678);
lean_dec(x_677);
x_183 = x_678;
goto block_186;
}
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_679 = lean_ctor_get(x_659, 1);
lean_inc(x_679);
lean_dec(x_659);
x_680 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_639, x_628, x_679);
lean_dec(x_628);
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_683 = x_680;
} else {
 lean_dec_ref(x_680);
 x_683 = lean_box(0);
}
x_684 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_683)) {
 x_685 = lean_alloc_ctor(7, 2, 0);
} else {
 x_685 = x_683;
 lean_ctor_set_tag(x_685, 7);
}
lean_ctor_set(x_685, 0, x_684);
lean_ctor_set(x_685, 1, x_681);
x_686 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_686, 0, x_685);
lean_ctor_set(x_686, 1, x_684);
x_687 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_658, x_686, x_632, x_633, x_634, x_635, x_682);
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_632);
x_688 = lean_ctor_get(x_687, 1);
lean_inc(x_688);
lean_dec(x_687);
x_183 = x_688;
goto block_186;
}
}
}
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; uint8_t x_692; 
lean_dec(x_642);
lean_dec(x_641);
x_689 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_690 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_689, x_634, x_640);
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_unbox(x_691);
lean_dec(x_691);
if (x_692 == 0)
{
lean_object* x_693; 
x_693 = lean_ctor_get(x_690, 1);
lean_inc(x_693);
lean_dec(x_690);
x_164 = x_639;
x_165 = x_628;
x_166 = x_629;
x_167 = x_630;
x_168 = x_631;
x_169 = x_632;
x_170 = x_633;
x_171 = x_634;
x_172 = x_635;
x_173 = x_693;
goto block_182;
}
else
{
uint8_t x_694; 
x_694 = !lean_is_exclusive(x_690);
if (x_694 == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; uint8_t x_698; 
x_695 = lean_ctor_get(x_690, 1);
x_696 = lean_ctor_get(x_690, 0);
lean_dec(x_696);
lean_inc(x_639);
x_697 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_639, x_628, x_695);
x_698 = !lean_is_exclusive(x_697);
if (x_698 == 0)
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_699 = lean_ctor_get(x_697, 0);
x_700 = lean_ctor_get(x_697, 1);
x_701 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_697, 7);
lean_ctor_set(x_697, 1, x_699);
lean_ctor_set(x_697, 0, x_701);
lean_ctor_set_tag(x_690, 7);
lean_ctor_set(x_690, 1, x_701);
lean_ctor_set(x_690, 0, x_697);
x_702 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_689, x_690, x_632, x_633, x_634, x_635, x_700);
x_703 = lean_ctor_get(x_702, 1);
lean_inc(x_703);
lean_dec(x_702);
x_164 = x_639;
x_165 = x_628;
x_166 = x_629;
x_167 = x_630;
x_168 = x_631;
x_169 = x_632;
x_170 = x_633;
x_171 = x_634;
x_172 = x_635;
x_173 = x_703;
goto block_182;
}
else
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_704 = lean_ctor_get(x_697, 0);
x_705 = lean_ctor_get(x_697, 1);
lean_inc(x_705);
lean_inc(x_704);
lean_dec(x_697);
x_706 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_707 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_707, 0, x_706);
lean_ctor_set(x_707, 1, x_704);
lean_ctor_set_tag(x_690, 7);
lean_ctor_set(x_690, 1, x_706);
lean_ctor_set(x_690, 0, x_707);
x_708 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_689, x_690, x_632, x_633, x_634, x_635, x_705);
x_709 = lean_ctor_get(x_708, 1);
lean_inc(x_709);
lean_dec(x_708);
x_164 = x_639;
x_165 = x_628;
x_166 = x_629;
x_167 = x_630;
x_168 = x_631;
x_169 = x_632;
x_170 = x_633;
x_171 = x_634;
x_172 = x_635;
x_173 = x_709;
goto block_182;
}
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_710 = lean_ctor_get(x_690, 1);
lean_inc(x_710);
lean_dec(x_690);
lean_inc(x_639);
x_711 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_639, x_628, x_710);
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 1);
lean_inc(x_713);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_714 = x_711;
} else {
 lean_dec_ref(x_711);
 x_714 = lean_box(0);
}
x_715 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_714)) {
 x_716 = lean_alloc_ctor(7, 2, 0);
} else {
 x_716 = x_714;
 lean_ctor_set_tag(x_716, 7);
}
lean_ctor_set(x_716, 0, x_715);
lean_ctor_set(x_716, 1, x_712);
x_717 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_717, 0, x_716);
lean_ctor_set(x_717, 1, x_715);
x_718 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_689, x_717, x_632, x_633, x_634, x_635, x_713);
x_719 = lean_ctor_get(x_718, 1);
lean_inc(x_719);
lean_dec(x_718);
x_164 = x_639;
x_165 = x_628;
x_166 = x_629;
x_167 = x_630;
x_168 = x_631;
x_169 = x_632;
x_170 = x_633;
x_171 = x_634;
x_172 = x_635;
x_173 = x_719;
goto block_182;
}
}
}
}
else
{
uint8_t x_720; 
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_630);
lean_dec(x_629);
lean_dec(x_628);
x_720 = !lean_is_exclusive(x_638);
if (x_720 == 0)
{
return x_638;
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_721 = lean_ctor_get(x_638, 0);
x_722 = lean_ctor_get(x_638, 1);
lean_inc(x_722);
lean_inc(x_721);
lean_dec(x_638);
x_723 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_723, 0, x_721);
lean_ctor_set(x_723, 1, x_722);
return x_723;
}
}
}
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; uint8_t x_833; 
x_739 = lean_ctor_get(x_599, 0);
x_740 = lean_ctor_get(x_599, 1);
lean_inc(x_740);
lean_inc(x_739);
lean_dec(x_599);
x_741 = lean_box(0);
x_833 = lean_unbox(x_739);
lean_dec(x_739);
if (x_833 == 0)
{
x_766 = x_2;
x_767 = x_3;
x_768 = x_4;
x_769 = x_5;
x_770 = x_6;
x_771 = x_7;
x_772 = x_8;
x_773 = x_9;
x_774 = x_740;
goto block_832;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_inc(x_1);
x_834 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_740);
x_835 = lean_ctor_get(x_834, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_834, 1);
lean_inc(x_836);
if (lean_is_exclusive(x_834)) {
 lean_ctor_release(x_834, 0);
 lean_ctor_release(x_834, 1);
 x_837 = x_834;
} else {
 lean_dec_ref(x_834);
 x_837 = lean_box(0);
}
x_838 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_837)) {
 x_839 = lean_alloc_ctor(7, 2, 0);
} else {
 x_839 = x_837;
 lean_ctor_set_tag(x_839, 7);
}
lean_ctor_set(x_839, 0, x_838);
lean_ctor_set(x_839, 1, x_835);
x_840 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_840, 0, x_839);
lean_ctor_set(x_840, 1, x_838);
x_841 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_598, x_840, x_6, x_7, x_8, x_9, x_836);
x_842 = lean_ctor_get(x_841, 1);
lean_inc(x_842);
lean_dec(x_841);
x_766 = x_2;
x_767 = x_3;
x_768 = x_4;
x_769 = x_5;
x_770 = x_6;
x_771 = x_7;
x_772 = x_8;
x_773 = x_9;
x_774 = x_842;
goto block_832;
}
block_765:
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; uint8_t x_762; 
x_757 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_748, x_756);
x_758 = lean_ctor_get(x_757, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_758, 7);
lean_inc(x_759);
lean_dec(x_758);
x_760 = lean_ctor_get(x_757, 1);
lean_inc(x_760);
lean_dec(x_757);
x_761 = lean_ctor_get(x_759, 2);
lean_inc(x_761);
x_762 = lean_nat_dec_lt(x_746, x_761);
lean_dec(x_761);
if (x_762 == 0)
{
lean_object* x_763; 
lean_dec(x_759);
x_763 = l_outOfBounds___redArg(x_741);
x_208 = x_743;
x_209 = x_752;
x_210 = x_745;
x_211 = x_746;
x_212 = x_753;
x_213 = x_760;
x_214 = x_742;
x_215 = x_744;
x_216 = x_755;
x_217 = x_749;
x_218 = x_754;
x_219 = x_750;
x_220 = x_748;
x_221 = x_751;
x_222 = x_747;
x_223 = x_763;
goto block_597;
}
else
{
lean_object* x_764; 
x_764 = l_Lean_PersistentArray_get_x21___redArg(x_741, x_759, x_746);
x_208 = x_743;
x_209 = x_752;
x_210 = x_745;
x_211 = x_746;
x_212 = x_753;
x_213 = x_760;
x_214 = x_742;
x_215 = x_744;
x_216 = x_755;
x_217 = x_749;
x_218 = x_754;
x_219 = x_750;
x_220 = x_748;
x_221 = x_751;
x_222 = x_747;
x_223 = x_764;
goto block_597;
}
}
block_832:
{
lean_object* x_775; lean_object* x_776; 
x_775 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_772);
x_776 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_775, x_766, x_770, x_771, x_772, x_773, x_774);
if (lean_obj_tag(x_776) == 0)
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; uint8_t x_781; 
x_777 = lean_ctor_get(x_776, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_776, 1);
lean_inc(x_778);
lean_dec(x_776);
x_779 = lean_ctor_get(x_777, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_777, 1);
lean_inc(x_780);
lean_inc(x_779);
x_781 = l_Int_Linear_Poly_isUnsatDvd(x_779, x_780);
if (x_781 == 0)
{
uint8_t x_782; 
x_782 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_777);
if (x_782 == 0)
{
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_783; 
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_769);
lean_dec(x_768);
lean_dec(x_767);
x_783 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_777, x_766, x_770, x_771, x_772, x_773, x_778);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_771);
lean_dec(x_770);
lean_dec(x_766);
return x_783;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; uint8_t x_792; uint8_t x_793; 
x_784 = lean_ctor_get(x_780, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_780, 1);
lean_inc(x_785);
x_786 = lean_ctor_get(x_780, 2);
lean_inc(x_786);
lean_inc(x_777);
x_787 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_777, x_766, x_778);
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
x_789 = lean_ctor_get(x_787, 1);
lean_inc(x_789);
lean_dec(x_787);
x_790 = lean_box(0);
x_791 = lean_unbox(x_788);
lean_dec(x_788);
x_792 = lean_unbox(x_790);
x_793 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_791, x_792);
if (x_793 == 0)
{
x_742 = x_780;
x_743 = x_777;
x_744 = x_779;
x_745 = x_784;
x_746 = x_785;
x_747 = x_786;
x_748 = x_766;
x_749 = x_767;
x_750 = x_768;
x_751 = x_769;
x_752 = x_770;
x_753 = x_771;
x_754 = x_772;
x_755 = x_773;
x_756 = x_789;
goto block_765;
}
else
{
lean_object* x_794; lean_object* x_795; 
x_794 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_785, x_766, x_789);
x_795 = lean_ctor_get(x_794, 1);
lean_inc(x_795);
lean_dec(x_794);
x_742 = x_780;
x_743 = x_777;
x_744 = x_779;
x_745 = x_784;
x_746 = x_785;
x_747 = x_786;
x_748 = x_766;
x_749 = x_767;
x_750 = x_768;
x_751 = x_769;
x_752 = x_770;
x_753 = x_771;
x_754 = x_772;
x_755 = x_773;
x_756 = x_795;
goto block_765;
}
}
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; uint8_t x_799; 
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_769);
lean_dec(x_768);
lean_dec(x_767);
x_796 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_797 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_796, x_772, x_778);
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
x_799 = lean_unbox(x_798);
lean_dec(x_798);
if (x_799 == 0)
{
lean_object* x_800; 
lean_dec(x_777);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_771);
lean_dec(x_770);
lean_dec(x_766);
x_800 = lean_ctor_get(x_797, 1);
lean_inc(x_800);
lean_dec(x_797);
x_183 = x_800;
goto block_186;
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_801 = lean_ctor_get(x_797, 1);
lean_inc(x_801);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 x_802 = x_797;
} else {
 lean_dec_ref(x_797);
 x_802 = lean_box(0);
}
x_803 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_777, x_766, x_801);
lean_dec(x_766);
x_804 = lean_ctor_get(x_803, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_803, 1);
lean_inc(x_805);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_806 = x_803;
} else {
 lean_dec_ref(x_803);
 x_806 = lean_box(0);
}
x_807 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_806)) {
 x_808 = lean_alloc_ctor(7, 2, 0);
} else {
 x_808 = x_806;
 lean_ctor_set_tag(x_808, 7);
}
lean_ctor_set(x_808, 0, x_807);
lean_ctor_set(x_808, 1, x_804);
if (lean_is_scalar(x_802)) {
 x_809 = lean_alloc_ctor(7, 2, 0);
} else {
 x_809 = x_802;
 lean_ctor_set_tag(x_809, 7);
}
lean_ctor_set(x_809, 0, x_808);
lean_ctor_set(x_809, 1, x_807);
x_810 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_796, x_809, x_770, x_771, x_772, x_773, x_805);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_771);
lean_dec(x_770);
x_811 = lean_ctor_get(x_810, 1);
lean_inc(x_811);
lean_dec(x_810);
x_183 = x_811;
goto block_186;
}
}
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; 
lean_dec(x_780);
lean_dec(x_779);
x_812 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_813 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_812, x_772, x_778);
x_814 = lean_ctor_get(x_813, 0);
lean_inc(x_814);
x_815 = lean_unbox(x_814);
lean_dec(x_814);
if (x_815 == 0)
{
lean_object* x_816; 
x_816 = lean_ctor_get(x_813, 1);
lean_inc(x_816);
lean_dec(x_813);
x_164 = x_777;
x_165 = x_766;
x_166 = x_767;
x_167 = x_768;
x_168 = x_769;
x_169 = x_770;
x_170 = x_771;
x_171 = x_772;
x_172 = x_773;
x_173 = x_816;
goto block_182;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_817 = lean_ctor_get(x_813, 1);
lean_inc(x_817);
if (lean_is_exclusive(x_813)) {
 lean_ctor_release(x_813, 0);
 lean_ctor_release(x_813, 1);
 x_818 = x_813;
} else {
 lean_dec_ref(x_813);
 x_818 = lean_box(0);
}
lean_inc(x_777);
x_819 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_777, x_766, x_817);
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_819, 1);
lean_inc(x_821);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_822 = x_819;
} else {
 lean_dec_ref(x_819);
 x_822 = lean_box(0);
}
x_823 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_822)) {
 x_824 = lean_alloc_ctor(7, 2, 0);
} else {
 x_824 = x_822;
 lean_ctor_set_tag(x_824, 7);
}
lean_ctor_set(x_824, 0, x_823);
lean_ctor_set(x_824, 1, x_820);
if (lean_is_scalar(x_818)) {
 x_825 = lean_alloc_ctor(7, 2, 0);
} else {
 x_825 = x_818;
 lean_ctor_set_tag(x_825, 7);
}
lean_ctor_set(x_825, 0, x_824);
lean_ctor_set(x_825, 1, x_823);
x_826 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_812, x_825, x_770, x_771, x_772, x_773, x_821);
x_827 = lean_ctor_get(x_826, 1);
lean_inc(x_827);
lean_dec(x_826);
x_164 = x_777;
x_165 = x_766;
x_166 = x_767;
x_167 = x_768;
x_168 = x_769;
x_169 = x_770;
x_170 = x_771;
x_171 = x_772;
x_172 = x_773;
x_173 = x_827;
goto block_182;
}
}
}
else
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; 
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_771);
lean_dec(x_770);
lean_dec(x_769);
lean_dec(x_768);
lean_dec(x_767);
lean_dec(x_766);
x_828 = lean_ctor_get(x_776, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_776, 1);
lean_inc(x_829);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_830 = x_776;
} else {
 lean_dec_ref(x_776);
 x_830 = lean_box(0);
}
if (lean_is_scalar(x_830)) {
 x_831 = lean_alloc_ctor(1, 2, 0);
} else {
 x_831 = x_830;
}
lean_ctor_set(x_831, 0, x_828);
lean_ctor_set(x_831, 1, x_829);
return x_831;
}
}
}
block_597:
{
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_215);
lean_dec(x_210);
x_224 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_225 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_224, x_218, x_213);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_unbox(x_226);
lean_dec(x_226);
if (x_227 == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_225, 1);
lean_inc(x_228);
lean_dec(x_225);
x_11 = x_208;
x_12 = x_214;
x_13 = x_211;
x_14 = x_220;
x_15 = x_209;
x_16 = x_212;
x_17 = x_218;
x_18 = x_216;
x_19 = x_228;
goto block_163;
}
else
{
uint8_t x_229; 
x_229 = !lean_is_exclusive(x_225);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_230 = lean_ctor_get(x_225, 1);
x_231 = lean_ctor_get(x_225, 0);
lean_dec(x_231);
lean_inc(x_208);
x_232 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_208, x_220, x_230);
x_233 = !lean_is_exclusive(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_232, 0);
x_235 = lean_ctor_get(x_232, 1);
x_236 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_232, 7);
lean_ctor_set(x_232, 1, x_234);
lean_ctor_set(x_232, 0, x_236);
lean_ctor_set_tag(x_225, 7);
lean_ctor_set(x_225, 1, x_236);
lean_ctor_set(x_225, 0, x_232);
x_237 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_224, x_225, x_209, x_212, x_218, x_216, x_235);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
x_11 = x_208;
x_12 = x_214;
x_13 = x_211;
x_14 = x_220;
x_15 = x_209;
x_16 = x_212;
x_17 = x_218;
x_18 = x_216;
x_19 = x_238;
goto block_163;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_239 = lean_ctor_get(x_232, 0);
x_240 = lean_ctor_get(x_232, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_232);
x_241 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_242 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_239);
lean_ctor_set_tag(x_225, 7);
lean_ctor_set(x_225, 1, x_241);
lean_ctor_set(x_225, 0, x_242);
x_243 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_224, x_225, x_209, x_212, x_218, x_216, x_240);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_11 = x_208;
x_12 = x_214;
x_13 = x_211;
x_14 = x_220;
x_15 = x_209;
x_16 = x_212;
x_17 = x_218;
x_18 = x_216;
x_19 = x_244;
goto block_163;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_245 = lean_ctor_get(x_225, 1);
lean_inc(x_245);
lean_dec(x_225);
lean_inc(x_208);
x_246 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_208, x_220, x_245);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
x_250 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(7, 2, 0);
} else {
 x_251 = x_249;
 lean_ctor_set_tag(x_251, 7);
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_247);
x_252 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
x_253 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_224, x_252, x_209, x_212, x_218, x_216, x_248);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
x_11 = x_208;
x_12 = x_214;
x_13 = x_211;
x_14 = x_220;
x_15 = x_209;
x_16 = x_212;
x_17 = x_218;
x_18 = x_216;
x_19 = x_254;
goto block_163;
}
}
}
else
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_214);
x_255 = lean_ctor_get(x_223, 0);
lean_inc(x_255);
lean_dec(x_223);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; 
lean_dec(x_256);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_215);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_208);
x_257 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_255, x_220, x_209, x_212, x_218, x_216, x_213);
lean_dec(x_216);
lean_dec(x_218);
lean_dec(x_212);
lean_dec(x_209);
lean_dec(x_220);
return x_257;
}
else
{
lean_object* x_258; uint8_t x_259; 
x_258 = lean_ctor_get(x_255, 0);
lean_inc(x_258);
x_259 = !lean_is_exclusive(x_256);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_260 = lean_ctor_get(x_256, 0);
x_261 = lean_ctor_get(x_256, 2);
x_262 = lean_ctor_get(x_256, 1);
lean_dec(x_262);
x_263 = lean_int_mul(x_210, x_258);
x_264 = lean_int_mul(x_260, x_215);
x_265 = l_Lean_Meta_Grind_Arith_gcdExt(x_263, x_264);
lean_dec(x_264);
lean_dec(x_263);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 0);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_ctor_get(x_266, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
lean_dec(x_266);
x_270 = lean_st_ref_take(x_220, x_213);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_271, 14);
lean_inc(x_272);
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_270, 1);
lean_inc(x_274);
lean_dec(x_270);
x_275 = !lean_is_exclusive(x_271);
if (x_275 == 0)
{
lean_object* x_276; uint8_t x_277; 
x_276 = lean_ctor_get(x_271, 14);
lean_dec(x_276);
x_277 = !lean_is_exclusive(x_272);
if (x_277 == 0)
{
lean_object* x_278; uint8_t x_279; 
x_278 = lean_ctor_get(x_272, 1);
lean_dec(x_278);
x_279 = !lean_is_exclusive(x_273);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_280 = lean_ctor_get(x_273, 7);
x_281 = lean_box(0);
x_282 = l_Lean_PersistentArray_set___redArg(x_280, x_211, x_281);
lean_ctor_set(x_273, 7, x_282);
x_283 = lean_st_ref_set(x_220, x_271, x_274);
x_284 = !lean_is_exclusive(x_283);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_285 = lean_ctor_get(x_283, 1);
x_286 = lean_ctor_get(x_283, 0);
lean_dec(x_286);
x_287 = lean_int_mul(x_268, x_258);
lean_dec(x_268);
lean_inc(x_222);
x_288 = l_Int_Linear_Poly_mul(x_222, x_287);
lean_dec(x_287);
x_289 = lean_int_mul(x_269, x_215);
lean_dec(x_269);
lean_inc(x_261);
x_290 = l_Int_Linear_Poly_mul(x_261, x_289);
lean_dec(x_289);
x_291 = lean_int_mul(x_215, x_258);
lean_dec(x_258);
lean_dec(x_215);
x_292 = l_Int_Linear_Poly_combine(x_288, x_290);
lean_inc(x_267);
lean_ctor_set(x_256, 2, x_292);
lean_ctor_set(x_256, 1, x_211);
lean_ctor_set(x_256, 0, x_267);
lean_inc(x_255);
lean_inc(x_208);
lean_ctor_set_tag(x_283, 4);
lean_ctor_set(x_283, 1, x_255);
lean_ctor_set(x_283, 0, x_208);
x_293 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_256);
lean_ctor_set(x_293, 2, x_283);
lean_inc(x_216);
lean_inc(x_218);
lean_inc(x_212);
lean_inc(x_209);
lean_inc(x_221);
lean_inc(x_219);
lean_inc(x_217);
lean_inc(x_220);
x_294 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_293, x_220, x_217, x_219, x_221, x_209, x_212, x_218, x_216, x_285);
if (lean_obj_tag(x_294) == 0)
{
uint8_t x_295; 
x_295 = !lean_is_exclusive(x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_296 = lean_ctor_get(x_294, 1);
x_297 = lean_ctor_get(x_294, 0);
lean_dec(x_297);
x_298 = l_Int_Linear_Poly_mul(x_222, x_260);
lean_dec(x_260);
x_299 = lean_int_neg(x_210);
lean_dec(x_210);
x_300 = l_Int_Linear_Poly_mul(x_261, x_299);
lean_dec(x_299);
x_301 = l_Int_Linear_Poly_combine(x_298, x_300);
lean_inc(x_255);
lean_ctor_set_tag(x_294, 5);
lean_ctor_set(x_294, 1, x_255);
lean_ctor_set(x_294, 0, x_208);
x_302 = !lean_is_exclusive(x_255);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_255, 2);
lean_dec(x_303);
x_304 = lean_ctor_get(x_255, 1);
lean_dec(x_304);
x_305 = lean_ctor_get(x_255, 0);
lean_dec(x_305);
lean_ctor_set(x_255, 2, x_294);
lean_ctor_set(x_255, 1, x_301);
lean_ctor_set(x_255, 0, x_267);
x_1 = x_255;
x_2 = x_220;
x_3 = x_217;
x_4 = x_219;
x_5 = x_221;
x_6 = x_209;
x_7 = x_212;
x_8 = x_218;
x_9 = x_216;
x_10 = x_296;
goto _start;
}
else
{
lean_object* x_307; 
lean_dec(x_255);
x_307 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_307, 0, x_267);
lean_ctor_set(x_307, 1, x_301);
lean_ctor_set(x_307, 2, x_294);
x_1 = x_307;
x_2 = x_220;
x_3 = x_217;
x_4 = x_219;
x_5 = x_221;
x_6 = x_209;
x_7 = x_212;
x_8 = x_218;
x_9 = x_216;
x_10 = x_296;
goto _start;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_309 = lean_ctor_get(x_294, 1);
lean_inc(x_309);
lean_dec(x_294);
x_310 = l_Int_Linear_Poly_mul(x_222, x_260);
lean_dec(x_260);
x_311 = lean_int_neg(x_210);
lean_dec(x_210);
x_312 = l_Int_Linear_Poly_mul(x_261, x_311);
lean_dec(x_311);
x_313 = l_Int_Linear_Poly_combine(x_310, x_312);
lean_inc(x_255);
x_314 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_314, 0, x_208);
lean_ctor_set(x_314, 1, x_255);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 x_315 = x_255;
} else {
 lean_dec_ref(x_255);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(0, 3, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_267);
lean_ctor_set(x_316, 1, x_313);
lean_ctor_set(x_316, 2, x_314);
x_1 = x_316;
x_2 = x_220;
x_3 = x_217;
x_4 = x_219;
x_5 = x_221;
x_6 = x_209;
x_7 = x_212;
x_8 = x_218;
x_9 = x_216;
x_10 = x_309;
goto _start;
}
}
else
{
lean_dec(x_267);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_255);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_212);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
return x_294;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_318 = lean_ctor_get(x_283, 1);
lean_inc(x_318);
lean_dec(x_283);
x_319 = lean_int_mul(x_268, x_258);
lean_dec(x_268);
lean_inc(x_222);
x_320 = l_Int_Linear_Poly_mul(x_222, x_319);
lean_dec(x_319);
x_321 = lean_int_mul(x_269, x_215);
lean_dec(x_269);
lean_inc(x_261);
x_322 = l_Int_Linear_Poly_mul(x_261, x_321);
lean_dec(x_321);
x_323 = lean_int_mul(x_215, x_258);
lean_dec(x_258);
lean_dec(x_215);
x_324 = l_Int_Linear_Poly_combine(x_320, x_322);
lean_inc(x_267);
lean_ctor_set(x_256, 2, x_324);
lean_ctor_set(x_256, 1, x_211);
lean_ctor_set(x_256, 0, x_267);
lean_inc(x_255);
lean_inc(x_208);
x_325 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_325, 0, x_208);
lean_ctor_set(x_325, 1, x_255);
x_326 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_326, 0, x_323);
lean_ctor_set(x_326, 1, x_256);
lean_ctor_set(x_326, 2, x_325);
lean_inc(x_216);
lean_inc(x_218);
lean_inc(x_212);
lean_inc(x_209);
lean_inc(x_221);
lean_inc(x_219);
lean_inc(x_217);
lean_inc(x_220);
x_327 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_326, x_220, x_217, x_219, x_221, x_209, x_212, x_218, x_216, x_318);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_329 = x_327;
} else {
 lean_dec_ref(x_327);
 x_329 = lean_box(0);
}
x_330 = l_Int_Linear_Poly_mul(x_222, x_260);
lean_dec(x_260);
x_331 = lean_int_neg(x_210);
lean_dec(x_210);
x_332 = l_Int_Linear_Poly_mul(x_261, x_331);
lean_dec(x_331);
x_333 = l_Int_Linear_Poly_combine(x_330, x_332);
lean_inc(x_255);
if (lean_is_scalar(x_329)) {
 x_334 = lean_alloc_ctor(5, 2, 0);
} else {
 x_334 = x_329;
 lean_ctor_set_tag(x_334, 5);
}
lean_ctor_set(x_334, 0, x_208);
lean_ctor_set(x_334, 1, x_255);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 x_335 = x_255;
} else {
 lean_dec_ref(x_255);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(0, 3, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_267);
lean_ctor_set(x_336, 1, x_333);
lean_ctor_set(x_336, 2, x_334);
x_1 = x_336;
x_2 = x_220;
x_3 = x_217;
x_4 = x_219;
x_5 = x_221;
x_6 = x_209;
x_7 = x_212;
x_8 = x_218;
x_9 = x_216;
x_10 = x_328;
goto _start;
}
else
{
lean_dec(x_267);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_255);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_212);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
return x_327;
}
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_338 = lean_ctor_get(x_273, 0);
x_339 = lean_ctor_get(x_273, 1);
x_340 = lean_ctor_get(x_273, 2);
x_341 = lean_ctor_get(x_273, 3);
x_342 = lean_ctor_get(x_273, 4);
x_343 = lean_ctor_get(x_273, 5);
x_344 = lean_ctor_get(x_273, 6);
x_345 = lean_ctor_get(x_273, 7);
x_346 = lean_ctor_get(x_273, 8);
x_347 = lean_ctor_get(x_273, 9);
x_348 = lean_ctor_get(x_273, 10);
x_349 = lean_ctor_get(x_273, 11);
x_350 = lean_ctor_get(x_273, 12);
x_351 = lean_ctor_get(x_273, 13);
x_352 = lean_ctor_get(x_273, 14);
x_353 = lean_ctor_get(x_273, 15);
x_354 = lean_ctor_get_uint8(x_273, sizeof(void*)*21);
x_355 = lean_ctor_get(x_273, 16);
x_356 = lean_ctor_get(x_273, 17);
x_357 = lean_ctor_get(x_273, 18);
x_358 = lean_ctor_get(x_273, 19);
x_359 = lean_ctor_get(x_273, 20);
x_360 = lean_ctor_get_uint8(x_273, sizeof(void*)*21 + 1);
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
lean_inc(x_338);
lean_dec(x_273);
x_361 = lean_box(0);
x_362 = l_Lean_PersistentArray_set___redArg(x_345, x_211, x_361);
x_363 = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(x_363, 0, x_338);
lean_ctor_set(x_363, 1, x_339);
lean_ctor_set(x_363, 2, x_340);
lean_ctor_set(x_363, 3, x_341);
lean_ctor_set(x_363, 4, x_342);
lean_ctor_set(x_363, 5, x_343);
lean_ctor_set(x_363, 6, x_344);
lean_ctor_set(x_363, 7, x_362);
lean_ctor_set(x_363, 8, x_346);
lean_ctor_set(x_363, 9, x_347);
lean_ctor_set(x_363, 10, x_348);
lean_ctor_set(x_363, 11, x_349);
lean_ctor_set(x_363, 12, x_350);
lean_ctor_set(x_363, 13, x_351);
lean_ctor_set(x_363, 14, x_352);
lean_ctor_set(x_363, 15, x_353);
lean_ctor_set(x_363, 16, x_355);
lean_ctor_set(x_363, 17, x_356);
lean_ctor_set(x_363, 18, x_357);
lean_ctor_set(x_363, 19, x_358);
lean_ctor_set(x_363, 20, x_359);
lean_ctor_set_uint8(x_363, sizeof(void*)*21, x_354);
lean_ctor_set_uint8(x_363, sizeof(void*)*21 + 1, x_360);
lean_ctor_set(x_272, 1, x_363);
x_364 = lean_st_ref_set(x_220, x_271, x_274);
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_366 = x_364;
} else {
 lean_dec_ref(x_364);
 x_366 = lean_box(0);
}
x_367 = lean_int_mul(x_268, x_258);
lean_dec(x_268);
lean_inc(x_222);
x_368 = l_Int_Linear_Poly_mul(x_222, x_367);
lean_dec(x_367);
x_369 = lean_int_mul(x_269, x_215);
lean_dec(x_269);
lean_inc(x_261);
x_370 = l_Int_Linear_Poly_mul(x_261, x_369);
lean_dec(x_369);
x_371 = lean_int_mul(x_215, x_258);
lean_dec(x_258);
lean_dec(x_215);
x_372 = l_Int_Linear_Poly_combine(x_368, x_370);
lean_inc(x_267);
lean_ctor_set(x_256, 2, x_372);
lean_ctor_set(x_256, 1, x_211);
lean_ctor_set(x_256, 0, x_267);
lean_inc(x_255);
lean_inc(x_208);
if (lean_is_scalar(x_366)) {
 x_373 = lean_alloc_ctor(4, 2, 0);
} else {
 x_373 = x_366;
 lean_ctor_set_tag(x_373, 4);
}
lean_ctor_set(x_373, 0, x_208);
lean_ctor_set(x_373, 1, x_255);
x_374 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_256);
lean_ctor_set(x_374, 2, x_373);
lean_inc(x_216);
lean_inc(x_218);
lean_inc(x_212);
lean_inc(x_209);
lean_inc(x_221);
lean_inc(x_219);
lean_inc(x_217);
lean_inc(x_220);
x_375 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_374, x_220, x_217, x_219, x_221, x_209, x_212, x_218, x_216, x_365);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_377 = x_375;
} else {
 lean_dec_ref(x_375);
 x_377 = lean_box(0);
}
x_378 = l_Int_Linear_Poly_mul(x_222, x_260);
lean_dec(x_260);
x_379 = lean_int_neg(x_210);
lean_dec(x_210);
x_380 = l_Int_Linear_Poly_mul(x_261, x_379);
lean_dec(x_379);
x_381 = l_Int_Linear_Poly_combine(x_378, x_380);
lean_inc(x_255);
if (lean_is_scalar(x_377)) {
 x_382 = lean_alloc_ctor(5, 2, 0);
} else {
 x_382 = x_377;
 lean_ctor_set_tag(x_382, 5);
}
lean_ctor_set(x_382, 0, x_208);
lean_ctor_set(x_382, 1, x_255);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 x_383 = x_255;
} else {
 lean_dec_ref(x_255);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(0, 3, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_267);
lean_ctor_set(x_384, 1, x_381);
lean_ctor_set(x_384, 2, x_382);
x_1 = x_384;
x_2 = x_220;
x_3 = x_217;
x_4 = x_219;
x_5 = x_221;
x_6 = x_209;
x_7 = x_212;
x_8 = x_218;
x_9 = x_216;
x_10 = x_376;
goto _start;
}
else
{
lean_dec(x_267);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_255);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_212);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
return x_375;
}
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_386 = lean_ctor_get(x_272, 0);
x_387 = lean_ctor_get(x_272, 2);
x_388 = lean_ctor_get(x_272, 3);
lean_inc(x_388);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_272);
x_389 = lean_ctor_get(x_273, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_273, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_273, 2);
lean_inc(x_391);
x_392 = lean_ctor_get(x_273, 3);
lean_inc(x_392);
x_393 = lean_ctor_get(x_273, 4);
lean_inc(x_393);
x_394 = lean_ctor_get(x_273, 5);
lean_inc(x_394);
x_395 = lean_ctor_get(x_273, 6);
lean_inc(x_395);
x_396 = lean_ctor_get(x_273, 7);
lean_inc(x_396);
x_397 = lean_ctor_get(x_273, 8);
lean_inc(x_397);
x_398 = lean_ctor_get(x_273, 9);
lean_inc(x_398);
x_399 = lean_ctor_get(x_273, 10);
lean_inc(x_399);
x_400 = lean_ctor_get(x_273, 11);
lean_inc(x_400);
x_401 = lean_ctor_get(x_273, 12);
lean_inc(x_401);
x_402 = lean_ctor_get(x_273, 13);
lean_inc(x_402);
x_403 = lean_ctor_get(x_273, 14);
lean_inc(x_403);
x_404 = lean_ctor_get(x_273, 15);
lean_inc(x_404);
x_405 = lean_ctor_get_uint8(x_273, sizeof(void*)*21);
x_406 = lean_ctor_get(x_273, 16);
lean_inc(x_406);
x_407 = lean_ctor_get(x_273, 17);
lean_inc(x_407);
x_408 = lean_ctor_get(x_273, 18);
lean_inc(x_408);
x_409 = lean_ctor_get(x_273, 19);
lean_inc(x_409);
x_410 = lean_ctor_get(x_273, 20);
lean_inc(x_410);
x_411 = lean_ctor_get_uint8(x_273, sizeof(void*)*21 + 1);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 lean_ctor_release(x_273, 2);
 lean_ctor_release(x_273, 3);
 lean_ctor_release(x_273, 4);
 lean_ctor_release(x_273, 5);
 lean_ctor_release(x_273, 6);
 lean_ctor_release(x_273, 7);
 lean_ctor_release(x_273, 8);
 lean_ctor_release(x_273, 9);
 lean_ctor_release(x_273, 10);
 lean_ctor_release(x_273, 11);
 lean_ctor_release(x_273, 12);
 lean_ctor_release(x_273, 13);
 lean_ctor_release(x_273, 14);
 lean_ctor_release(x_273, 15);
 lean_ctor_release(x_273, 16);
 lean_ctor_release(x_273, 17);
 lean_ctor_release(x_273, 18);
 lean_ctor_release(x_273, 19);
 lean_ctor_release(x_273, 20);
 x_412 = x_273;
} else {
 lean_dec_ref(x_273);
 x_412 = lean_box(0);
}
x_413 = lean_box(0);
x_414 = l_Lean_PersistentArray_set___redArg(x_396, x_211, x_413);
if (lean_is_scalar(x_412)) {
 x_415 = lean_alloc_ctor(0, 21, 2);
} else {
 x_415 = x_412;
}
lean_ctor_set(x_415, 0, x_389);
lean_ctor_set(x_415, 1, x_390);
lean_ctor_set(x_415, 2, x_391);
lean_ctor_set(x_415, 3, x_392);
lean_ctor_set(x_415, 4, x_393);
lean_ctor_set(x_415, 5, x_394);
lean_ctor_set(x_415, 6, x_395);
lean_ctor_set(x_415, 7, x_414);
lean_ctor_set(x_415, 8, x_397);
lean_ctor_set(x_415, 9, x_398);
lean_ctor_set(x_415, 10, x_399);
lean_ctor_set(x_415, 11, x_400);
lean_ctor_set(x_415, 12, x_401);
lean_ctor_set(x_415, 13, x_402);
lean_ctor_set(x_415, 14, x_403);
lean_ctor_set(x_415, 15, x_404);
lean_ctor_set(x_415, 16, x_406);
lean_ctor_set(x_415, 17, x_407);
lean_ctor_set(x_415, 18, x_408);
lean_ctor_set(x_415, 19, x_409);
lean_ctor_set(x_415, 20, x_410);
lean_ctor_set_uint8(x_415, sizeof(void*)*21, x_405);
lean_ctor_set_uint8(x_415, sizeof(void*)*21 + 1, x_411);
x_416 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_416, 0, x_386);
lean_ctor_set(x_416, 1, x_415);
lean_ctor_set(x_416, 2, x_387);
lean_ctor_set(x_416, 3, x_388);
lean_ctor_set(x_271, 14, x_416);
x_417 = lean_st_ref_set(x_220, x_271, x_274);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_419 = x_417;
} else {
 lean_dec_ref(x_417);
 x_419 = lean_box(0);
}
x_420 = lean_int_mul(x_268, x_258);
lean_dec(x_268);
lean_inc(x_222);
x_421 = l_Int_Linear_Poly_mul(x_222, x_420);
lean_dec(x_420);
x_422 = lean_int_mul(x_269, x_215);
lean_dec(x_269);
lean_inc(x_261);
x_423 = l_Int_Linear_Poly_mul(x_261, x_422);
lean_dec(x_422);
x_424 = lean_int_mul(x_215, x_258);
lean_dec(x_258);
lean_dec(x_215);
x_425 = l_Int_Linear_Poly_combine(x_421, x_423);
lean_inc(x_267);
lean_ctor_set(x_256, 2, x_425);
lean_ctor_set(x_256, 1, x_211);
lean_ctor_set(x_256, 0, x_267);
lean_inc(x_255);
lean_inc(x_208);
if (lean_is_scalar(x_419)) {
 x_426 = lean_alloc_ctor(4, 2, 0);
} else {
 x_426 = x_419;
 lean_ctor_set_tag(x_426, 4);
}
lean_ctor_set(x_426, 0, x_208);
lean_ctor_set(x_426, 1, x_255);
x_427 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_427, 0, x_424);
lean_ctor_set(x_427, 1, x_256);
lean_ctor_set(x_427, 2, x_426);
lean_inc(x_216);
lean_inc(x_218);
lean_inc(x_212);
lean_inc(x_209);
lean_inc(x_221);
lean_inc(x_219);
lean_inc(x_217);
lean_inc(x_220);
x_428 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_427, x_220, x_217, x_219, x_221, x_209, x_212, x_218, x_216, x_418);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_429 = lean_ctor_get(x_428, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_430 = x_428;
} else {
 lean_dec_ref(x_428);
 x_430 = lean_box(0);
}
x_431 = l_Int_Linear_Poly_mul(x_222, x_260);
lean_dec(x_260);
x_432 = lean_int_neg(x_210);
lean_dec(x_210);
x_433 = l_Int_Linear_Poly_mul(x_261, x_432);
lean_dec(x_432);
x_434 = l_Int_Linear_Poly_combine(x_431, x_433);
lean_inc(x_255);
if (lean_is_scalar(x_430)) {
 x_435 = lean_alloc_ctor(5, 2, 0);
} else {
 x_435 = x_430;
 lean_ctor_set_tag(x_435, 5);
}
lean_ctor_set(x_435, 0, x_208);
lean_ctor_set(x_435, 1, x_255);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 x_436 = x_255;
} else {
 lean_dec_ref(x_255);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(0, 3, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_267);
lean_ctor_set(x_437, 1, x_434);
lean_ctor_set(x_437, 2, x_435);
x_1 = x_437;
x_2 = x_220;
x_3 = x_217;
x_4 = x_219;
x_5 = x_221;
x_6 = x_209;
x_7 = x_212;
x_8 = x_218;
x_9 = x_216;
x_10 = x_429;
goto _start;
}
else
{
lean_dec(x_267);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_255);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_212);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
return x_428;
}
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_439 = lean_ctor_get(x_271, 0);
x_440 = lean_ctor_get(x_271, 1);
x_441 = lean_ctor_get(x_271, 2);
x_442 = lean_ctor_get(x_271, 3);
x_443 = lean_ctor_get(x_271, 4);
x_444 = lean_ctor_get(x_271, 5);
x_445 = lean_ctor_get(x_271, 6);
x_446 = lean_ctor_get(x_271, 7);
x_447 = lean_ctor_get_uint8(x_271, sizeof(void*)*16);
x_448 = lean_ctor_get(x_271, 8);
x_449 = lean_ctor_get(x_271, 9);
x_450 = lean_ctor_get(x_271, 10);
x_451 = lean_ctor_get(x_271, 11);
x_452 = lean_ctor_get(x_271, 12);
x_453 = lean_ctor_get(x_271, 13);
x_454 = lean_ctor_get(x_271, 15);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
lean_inc(x_449);
lean_inc(x_448);
lean_inc(x_446);
lean_inc(x_445);
lean_inc(x_444);
lean_inc(x_443);
lean_inc(x_442);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_271);
x_455 = lean_ctor_get(x_272, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_272, 2);
lean_inc(x_456);
x_457 = lean_ctor_get(x_272, 3);
lean_inc(x_457);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 x_458 = x_272;
} else {
 lean_dec_ref(x_272);
 x_458 = lean_box(0);
}
x_459 = lean_ctor_get(x_273, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_273, 1);
lean_inc(x_460);
x_461 = lean_ctor_get(x_273, 2);
lean_inc(x_461);
x_462 = lean_ctor_get(x_273, 3);
lean_inc(x_462);
x_463 = lean_ctor_get(x_273, 4);
lean_inc(x_463);
x_464 = lean_ctor_get(x_273, 5);
lean_inc(x_464);
x_465 = lean_ctor_get(x_273, 6);
lean_inc(x_465);
x_466 = lean_ctor_get(x_273, 7);
lean_inc(x_466);
x_467 = lean_ctor_get(x_273, 8);
lean_inc(x_467);
x_468 = lean_ctor_get(x_273, 9);
lean_inc(x_468);
x_469 = lean_ctor_get(x_273, 10);
lean_inc(x_469);
x_470 = lean_ctor_get(x_273, 11);
lean_inc(x_470);
x_471 = lean_ctor_get(x_273, 12);
lean_inc(x_471);
x_472 = lean_ctor_get(x_273, 13);
lean_inc(x_472);
x_473 = lean_ctor_get(x_273, 14);
lean_inc(x_473);
x_474 = lean_ctor_get(x_273, 15);
lean_inc(x_474);
x_475 = lean_ctor_get_uint8(x_273, sizeof(void*)*21);
x_476 = lean_ctor_get(x_273, 16);
lean_inc(x_476);
x_477 = lean_ctor_get(x_273, 17);
lean_inc(x_477);
x_478 = lean_ctor_get(x_273, 18);
lean_inc(x_478);
x_479 = lean_ctor_get(x_273, 19);
lean_inc(x_479);
x_480 = lean_ctor_get(x_273, 20);
lean_inc(x_480);
x_481 = lean_ctor_get_uint8(x_273, sizeof(void*)*21 + 1);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 lean_ctor_release(x_273, 2);
 lean_ctor_release(x_273, 3);
 lean_ctor_release(x_273, 4);
 lean_ctor_release(x_273, 5);
 lean_ctor_release(x_273, 6);
 lean_ctor_release(x_273, 7);
 lean_ctor_release(x_273, 8);
 lean_ctor_release(x_273, 9);
 lean_ctor_release(x_273, 10);
 lean_ctor_release(x_273, 11);
 lean_ctor_release(x_273, 12);
 lean_ctor_release(x_273, 13);
 lean_ctor_release(x_273, 14);
 lean_ctor_release(x_273, 15);
 lean_ctor_release(x_273, 16);
 lean_ctor_release(x_273, 17);
 lean_ctor_release(x_273, 18);
 lean_ctor_release(x_273, 19);
 lean_ctor_release(x_273, 20);
 x_482 = x_273;
} else {
 lean_dec_ref(x_273);
 x_482 = lean_box(0);
}
x_483 = lean_box(0);
x_484 = l_Lean_PersistentArray_set___redArg(x_466, x_211, x_483);
if (lean_is_scalar(x_482)) {
 x_485 = lean_alloc_ctor(0, 21, 2);
} else {
 x_485 = x_482;
}
lean_ctor_set(x_485, 0, x_459);
lean_ctor_set(x_485, 1, x_460);
lean_ctor_set(x_485, 2, x_461);
lean_ctor_set(x_485, 3, x_462);
lean_ctor_set(x_485, 4, x_463);
lean_ctor_set(x_485, 5, x_464);
lean_ctor_set(x_485, 6, x_465);
lean_ctor_set(x_485, 7, x_484);
lean_ctor_set(x_485, 8, x_467);
lean_ctor_set(x_485, 9, x_468);
lean_ctor_set(x_485, 10, x_469);
lean_ctor_set(x_485, 11, x_470);
lean_ctor_set(x_485, 12, x_471);
lean_ctor_set(x_485, 13, x_472);
lean_ctor_set(x_485, 14, x_473);
lean_ctor_set(x_485, 15, x_474);
lean_ctor_set(x_485, 16, x_476);
lean_ctor_set(x_485, 17, x_477);
lean_ctor_set(x_485, 18, x_478);
lean_ctor_set(x_485, 19, x_479);
lean_ctor_set(x_485, 20, x_480);
lean_ctor_set_uint8(x_485, sizeof(void*)*21, x_475);
lean_ctor_set_uint8(x_485, sizeof(void*)*21 + 1, x_481);
if (lean_is_scalar(x_458)) {
 x_486 = lean_alloc_ctor(0, 4, 0);
} else {
 x_486 = x_458;
}
lean_ctor_set(x_486, 0, x_455);
lean_ctor_set(x_486, 1, x_485);
lean_ctor_set(x_486, 2, x_456);
lean_ctor_set(x_486, 3, x_457);
x_487 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_487, 0, x_439);
lean_ctor_set(x_487, 1, x_440);
lean_ctor_set(x_487, 2, x_441);
lean_ctor_set(x_487, 3, x_442);
lean_ctor_set(x_487, 4, x_443);
lean_ctor_set(x_487, 5, x_444);
lean_ctor_set(x_487, 6, x_445);
lean_ctor_set(x_487, 7, x_446);
lean_ctor_set(x_487, 8, x_448);
lean_ctor_set(x_487, 9, x_449);
lean_ctor_set(x_487, 10, x_450);
lean_ctor_set(x_487, 11, x_451);
lean_ctor_set(x_487, 12, x_452);
lean_ctor_set(x_487, 13, x_453);
lean_ctor_set(x_487, 14, x_486);
lean_ctor_set(x_487, 15, x_454);
lean_ctor_set_uint8(x_487, sizeof(void*)*16, x_447);
x_488 = lean_st_ref_set(x_220, x_487, x_274);
x_489 = lean_ctor_get(x_488, 1);
lean_inc(x_489);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_490 = x_488;
} else {
 lean_dec_ref(x_488);
 x_490 = lean_box(0);
}
x_491 = lean_int_mul(x_268, x_258);
lean_dec(x_268);
lean_inc(x_222);
x_492 = l_Int_Linear_Poly_mul(x_222, x_491);
lean_dec(x_491);
x_493 = lean_int_mul(x_269, x_215);
lean_dec(x_269);
lean_inc(x_261);
x_494 = l_Int_Linear_Poly_mul(x_261, x_493);
lean_dec(x_493);
x_495 = lean_int_mul(x_215, x_258);
lean_dec(x_258);
lean_dec(x_215);
x_496 = l_Int_Linear_Poly_combine(x_492, x_494);
lean_inc(x_267);
lean_ctor_set(x_256, 2, x_496);
lean_ctor_set(x_256, 1, x_211);
lean_ctor_set(x_256, 0, x_267);
lean_inc(x_255);
lean_inc(x_208);
if (lean_is_scalar(x_490)) {
 x_497 = lean_alloc_ctor(4, 2, 0);
} else {
 x_497 = x_490;
 lean_ctor_set_tag(x_497, 4);
}
lean_ctor_set(x_497, 0, x_208);
lean_ctor_set(x_497, 1, x_255);
x_498 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_498, 0, x_495);
lean_ctor_set(x_498, 1, x_256);
lean_ctor_set(x_498, 2, x_497);
lean_inc(x_216);
lean_inc(x_218);
lean_inc(x_212);
lean_inc(x_209);
lean_inc(x_221);
lean_inc(x_219);
lean_inc(x_217);
lean_inc(x_220);
x_499 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_498, x_220, x_217, x_219, x_221, x_209, x_212, x_218, x_216, x_489);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_500 = lean_ctor_get(x_499, 1);
lean_inc(x_500);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_501 = x_499;
} else {
 lean_dec_ref(x_499);
 x_501 = lean_box(0);
}
x_502 = l_Int_Linear_Poly_mul(x_222, x_260);
lean_dec(x_260);
x_503 = lean_int_neg(x_210);
lean_dec(x_210);
x_504 = l_Int_Linear_Poly_mul(x_261, x_503);
lean_dec(x_503);
x_505 = l_Int_Linear_Poly_combine(x_502, x_504);
lean_inc(x_255);
if (lean_is_scalar(x_501)) {
 x_506 = lean_alloc_ctor(5, 2, 0);
} else {
 x_506 = x_501;
 lean_ctor_set_tag(x_506, 5);
}
lean_ctor_set(x_506, 0, x_208);
lean_ctor_set(x_506, 1, x_255);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 x_507 = x_255;
} else {
 lean_dec_ref(x_255);
 x_507 = lean_box(0);
}
if (lean_is_scalar(x_507)) {
 x_508 = lean_alloc_ctor(0, 3, 0);
} else {
 x_508 = x_507;
}
lean_ctor_set(x_508, 0, x_267);
lean_ctor_set(x_508, 1, x_505);
lean_ctor_set(x_508, 2, x_506);
x_1 = x_508;
x_2 = x_220;
x_3 = x_217;
x_4 = x_219;
x_5 = x_221;
x_6 = x_209;
x_7 = x_212;
x_8 = x_218;
x_9 = x_216;
x_10 = x_500;
goto _start;
}
else
{
lean_dec(x_267);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_255);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_212);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
return x_499;
}
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; uint8_t x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; uint8_t x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_510 = lean_ctor_get(x_256, 0);
x_511 = lean_ctor_get(x_256, 2);
lean_inc(x_511);
lean_inc(x_510);
lean_dec(x_256);
x_512 = lean_int_mul(x_210, x_258);
x_513 = lean_int_mul(x_510, x_215);
x_514 = l_Lean_Meta_Grind_Arith_gcdExt(x_512, x_513);
lean_dec(x_513);
lean_dec(x_512);
x_515 = lean_ctor_get(x_514, 1);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 0);
lean_inc(x_516);
lean_dec(x_514);
x_517 = lean_ctor_get(x_515, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_515, 1);
lean_inc(x_518);
lean_dec(x_515);
x_519 = lean_st_ref_take(x_220, x_213);
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_520, 14);
lean_inc(x_521);
x_522 = lean_ctor_get(x_521, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_519, 1);
lean_inc(x_523);
lean_dec(x_519);
x_524 = lean_ctor_get(x_520, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_520, 1);
lean_inc(x_525);
x_526 = lean_ctor_get(x_520, 2);
lean_inc(x_526);
x_527 = lean_ctor_get(x_520, 3);
lean_inc(x_527);
x_528 = lean_ctor_get(x_520, 4);
lean_inc(x_528);
x_529 = lean_ctor_get(x_520, 5);
lean_inc(x_529);
x_530 = lean_ctor_get(x_520, 6);
lean_inc(x_530);
x_531 = lean_ctor_get(x_520, 7);
lean_inc(x_531);
x_532 = lean_ctor_get_uint8(x_520, sizeof(void*)*16);
x_533 = lean_ctor_get(x_520, 8);
lean_inc(x_533);
x_534 = lean_ctor_get(x_520, 9);
lean_inc(x_534);
x_535 = lean_ctor_get(x_520, 10);
lean_inc(x_535);
x_536 = lean_ctor_get(x_520, 11);
lean_inc(x_536);
x_537 = lean_ctor_get(x_520, 12);
lean_inc(x_537);
x_538 = lean_ctor_get(x_520, 13);
lean_inc(x_538);
x_539 = lean_ctor_get(x_520, 15);
lean_inc(x_539);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 lean_ctor_release(x_520, 1);
 lean_ctor_release(x_520, 2);
 lean_ctor_release(x_520, 3);
 lean_ctor_release(x_520, 4);
 lean_ctor_release(x_520, 5);
 lean_ctor_release(x_520, 6);
 lean_ctor_release(x_520, 7);
 lean_ctor_release(x_520, 8);
 lean_ctor_release(x_520, 9);
 lean_ctor_release(x_520, 10);
 lean_ctor_release(x_520, 11);
 lean_ctor_release(x_520, 12);
 lean_ctor_release(x_520, 13);
 lean_ctor_release(x_520, 14);
 lean_ctor_release(x_520, 15);
 x_540 = x_520;
} else {
 lean_dec_ref(x_520);
 x_540 = lean_box(0);
}
x_541 = lean_ctor_get(x_521, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_521, 2);
lean_inc(x_542);
x_543 = lean_ctor_get(x_521, 3);
lean_inc(x_543);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 lean_ctor_release(x_521, 2);
 lean_ctor_release(x_521, 3);
 x_544 = x_521;
} else {
 lean_dec_ref(x_521);
 x_544 = lean_box(0);
}
x_545 = lean_ctor_get(x_522, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_522, 1);
lean_inc(x_546);
x_547 = lean_ctor_get(x_522, 2);
lean_inc(x_547);
x_548 = lean_ctor_get(x_522, 3);
lean_inc(x_548);
x_549 = lean_ctor_get(x_522, 4);
lean_inc(x_549);
x_550 = lean_ctor_get(x_522, 5);
lean_inc(x_550);
x_551 = lean_ctor_get(x_522, 6);
lean_inc(x_551);
x_552 = lean_ctor_get(x_522, 7);
lean_inc(x_552);
x_553 = lean_ctor_get(x_522, 8);
lean_inc(x_553);
x_554 = lean_ctor_get(x_522, 9);
lean_inc(x_554);
x_555 = lean_ctor_get(x_522, 10);
lean_inc(x_555);
x_556 = lean_ctor_get(x_522, 11);
lean_inc(x_556);
x_557 = lean_ctor_get(x_522, 12);
lean_inc(x_557);
x_558 = lean_ctor_get(x_522, 13);
lean_inc(x_558);
x_559 = lean_ctor_get(x_522, 14);
lean_inc(x_559);
x_560 = lean_ctor_get(x_522, 15);
lean_inc(x_560);
x_561 = lean_ctor_get_uint8(x_522, sizeof(void*)*21);
x_562 = lean_ctor_get(x_522, 16);
lean_inc(x_562);
x_563 = lean_ctor_get(x_522, 17);
lean_inc(x_563);
x_564 = lean_ctor_get(x_522, 18);
lean_inc(x_564);
x_565 = lean_ctor_get(x_522, 19);
lean_inc(x_565);
x_566 = lean_ctor_get(x_522, 20);
lean_inc(x_566);
x_567 = lean_ctor_get_uint8(x_522, sizeof(void*)*21 + 1);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 lean_ctor_release(x_522, 1);
 lean_ctor_release(x_522, 2);
 lean_ctor_release(x_522, 3);
 lean_ctor_release(x_522, 4);
 lean_ctor_release(x_522, 5);
 lean_ctor_release(x_522, 6);
 lean_ctor_release(x_522, 7);
 lean_ctor_release(x_522, 8);
 lean_ctor_release(x_522, 9);
 lean_ctor_release(x_522, 10);
 lean_ctor_release(x_522, 11);
 lean_ctor_release(x_522, 12);
 lean_ctor_release(x_522, 13);
 lean_ctor_release(x_522, 14);
 lean_ctor_release(x_522, 15);
 lean_ctor_release(x_522, 16);
 lean_ctor_release(x_522, 17);
 lean_ctor_release(x_522, 18);
 lean_ctor_release(x_522, 19);
 lean_ctor_release(x_522, 20);
 x_568 = x_522;
} else {
 lean_dec_ref(x_522);
 x_568 = lean_box(0);
}
x_569 = lean_box(0);
x_570 = l_Lean_PersistentArray_set___redArg(x_552, x_211, x_569);
if (lean_is_scalar(x_568)) {
 x_571 = lean_alloc_ctor(0, 21, 2);
} else {
 x_571 = x_568;
}
lean_ctor_set(x_571, 0, x_545);
lean_ctor_set(x_571, 1, x_546);
lean_ctor_set(x_571, 2, x_547);
lean_ctor_set(x_571, 3, x_548);
lean_ctor_set(x_571, 4, x_549);
lean_ctor_set(x_571, 5, x_550);
lean_ctor_set(x_571, 6, x_551);
lean_ctor_set(x_571, 7, x_570);
lean_ctor_set(x_571, 8, x_553);
lean_ctor_set(x_571, 9, x_554);
lean_ctor_set(x_571, 10, x_555);
lean_ctor_set(x_571, 11, x_556);
lean_ctor_set(x_571, 12, x_557);
lean_ctor_set(x_571, 13, x_558);
lean_ctor_set(x_571, 14, x_559);
lean_ctor_set(x_571, 15, x_560);
lean_ctor_set(x_571, 16, x_562);
lean_ctor_set(x_571, 17, x_563);
lean_ctor_set(x_571, 18, x_564);
lean_ctor_set(x_571, 19, x_565);
lean_ctor_set(x_571, 20, x_566);
lean_ctor_set_uint8(x_571, sizeof(void*)*21, x_561);
lean_ctor_set_uint8(x_571, sizeof(void*)*21 + 1, x_567);
if (lean_is_scalar(x_544)) {
 x_572 = lean_alloc_ctor(0, 4, 0);
} else {
 x_572 = x_544;
}
lean_ctor_set(x_572, 0, x_541);
lean_ctor_set(x_572, 1, x_571);
lean_ctor_set(x_572, 2, x_542);
lean_ctor_set(x_572, 3, x_543);
if (lean_is_scalar(x_540)) {
 x_573 = lean_alloc_ctor(0, 16, 1);
} else {
 x_573 = x_540;
}
lean_ctor_set(x_573, 0, x_524);
lean_ctor_set(x_573, 1, x_525);
lean_ctor_set(x_573, 2, x_526);
lean_ctor_set(x_573, 3, x_527);
lean_ctor_set(x_573, 4, x_528);
lean_ctor_set(x_573, 5, x_529);
lean_ctor_set(x_573, 6, x_530);
lean_ctor_set(x_573, 7, x_531);
lean_ctor_set(x_573, 8, x_533);
lean_ctor_set(x_573, 9, x_534);
lean_ctor_set(x_573, 10, x_535);
lean_ctor_set(x_573, 11, x_536);
lean_ctor_set(x_573, 12, x_537);
lean_ctor_set(x_573, 13, x_538);
lean_ctor_set(x_573, 14, x_572);
lean_ctor_set(x_573, 15, x_539);
lean_ctor_set_uint8(x_573, sizeof(void*)*16, x_532);
x_574 = lean_st_ref_set(x_220, x_573, x_523);
x_575 = lean_ctor_get(x_574, 1);
lean_inc(x_575);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_576 = x_574;
} else {
 lean_dec_ref(x_574);
 x_576 = lean_box(0);
}
x_577 = lean_int_mul(x_517, x_258);
lean_dec(x_517);
lean_inc(x_222);
x_578 = l_Int_Linear_Poly_mul(x_222, x_577);
lean_dec(x_577);
x_579 = lean_int_mul(x_518, x_215);
lean_dec(x_518);
lean_inc(x_511);
x_580 = l_Int_Linear_Poly_mul(x_511, x_579);
lean_dec(x_579);
x_581 = lean_int_mul(x_215, x_258);
lean_dec(x_258);
lean_dec(x_215);
x_582 = l_Int_Linear_Poly_combine(x_578, x_580);
lean_inc(x_516);
x_583 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_583, 0, x_516);
lean_ctor_set(x_583, 1, x_211);
lean_ctor_set(x_583, 2, x_582);
lean_inc(x_255);
lean_inc(x_208);
if (lean_is_scalar(x_576)) {
 x_584 = lean_alloc_ctor(4, 2, 0);
} else {
 x_584 = x_576;
 lean_ctor_set_tag(x_584, 4);
}
lean_ctor_set(x_584, 0, x_208);
lean_ctor_set(x_584, 1, x_255);
x_585 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_585, 0, x_581);
lean_ctor_set(x_585, 1, x_583);
lean_ctor_set(x_585, 2, x_584);
lean_inc(x_216);
lean_inc(x_218);
lean_inc(x_212);
lean_inc(x_209);
lean_inc(x_221);
lean_inc(x_219);
lean_inc(x_217);
lean_inc(x_220);
x_586 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_585, x_220, x_217, x_219, x_221, x_209, x_212, x_218, x_216, x_575);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_587 = lean_ctor_get(x_586, 1);
lean_inc(x_587);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 x_588 = x_586;
} else {
 lean_dec_ref(x_586);
 x_588 = lean_box(0);
}
x_589 = l_Int_Linear_Poly_mul(x_222, x_510);
lean_dec(x_510);
x_590 = lean_int_neg(x_210);
lean_dec(x_210);
x_591 = l_Int_Linear_Poly_mul(x_511, x_590);
lean_dec(x_590);
x_592 = l_Int_Linear_Poly_combine(x_589, x_591);
lean_inc(x_255);
if (lean_is_scalar(x_588)) {
 x_593 = lean_alloc_ctor(5, 2, 0);
} else {
 x_593 = x_588;
 lean_ctor_set_tag(x_593, 5);
}
lean_ctor_set(x_593, 0, x_208);
lean_ctor_set(x_593, 1, x_255);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 x_594 = x_255;
} else {
 lean_dec_ref(x_255);
 x_594 = lean_box(0);
}
if (lean_is_scalar(x_594)) {
 x_595 = lean_alloc_ctor(0, 3, 0);
} else {
 x_595 = x_594;
}
lean_ctor_set(x_595, 0, x_516);
lean_ctor_set(x_595, 1, x_592);
lean_ctor_set(x_595, 2, x_593);
x_1 = x_595;
x_2 = x_220;
x_3 = x_217;
x_4 = x_219;
x_5 = x_221;
x_6 = x_209;
x_7 = x_212;
x_8 = x_218;
x_9 = x_216;
x_10 = x_587;
goto _start;
}
else
{
lean_dec(x_516);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_255);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_212);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
return x_586;
}
}
}
}
}
}
else
{
uint8_t x_843; 
lean_free_object(x_8);
lean_dec(x_200);
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
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_843 = !lean_is_exclusive(x_202);
if (x_843 == 0)
{
lean_object* x_844; lean_object* x_845; 
x_844 = lean_ctor_get(x_202, 0);
lean_dec(x_844);
x_845 = lean_box(0);
lean_ctor_set(x_202, 0, x_845);
return x_202;
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_846 = lean_ctor_get(x_202, 1);
lean_inc(x_846);
lean_dec(x_202);
x_847 = lean_box(0);
x_848 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_848, 0, x_847);
lean_ctor_set(x_848, 1, x_846);
return x_848;
}
}
}
else
{
lean_object* x_849; 
lean_free_object(x_8);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_849 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_193, x_10);
return x_849;
}
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; uint8_t x_861; lean_object* x_862; uint8_t x_863; lean_object* x_864; uint8_t x_865; 
x_850 = lean_ctor_get(x_8, 0);
x_851 = lean_ctor_get(x_8, 1);
x_852 = lean_ctor_get(x_8, 2);
x_853 = lean_ctor_get(x_8, 3);
x_854 = lean_ctor_get(x_8, 4);
x_855 = lean_ctor_get(x_8, 5);
x_856 = lean_ctor_get(x_8, 6);
x_857 = lean_ctor_get(x_8, 7);
x_858 = lean_ctor_get(x_8, 8);
x_859 = lean_ctor_get(x_8, 9);
x_860 = lean_ctor_get(x_8, 10);
x_861 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_862 = lean_ctor_get(x_8, 11);
x_863 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_864 = lean_ctor_get(x_8, 12);
lean_inc(x_864);
lean_inc(x_862);
lean_inc(x_860);
lean_inc(x_859);
lean_inc(x_858);
lean_inc(x_857);
lean_inc(x_856);
lean_inc(x_855);
lean_inc(x_854);
lean_inc(x_853);
lean_inc(x_852);
lean_inc(x_851);
lean_inc(x_850);
lean_dec(x_8);
x_865 = lean_nat_dec_eq(x_853, x_854);
if (x_865 == 0)
{
lean_object* x_866; lean_object* x_867; uint8_t x_868; 
x_866 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_867 = lean_ctor_get(x_866, 0);
lean_inc(x_867);
x_868 = lean_unbox(x_867);
lean_dec(x_867);
if (x_868 == 0)
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; uint8_t x_1095; 
x_869 = lean_ctor_get(x_866, 1);
lean_inc(x_869);
lean_dec(x_866);
x_870 = lean_unsigned_to_nat(1u);
x_871 = lean_nat_add(x_853, x_870);
lean_dec(x_853);
x_872 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_872, 0, x_850);
lean_ctor_set(x_872, 1, x_851);
lean_ctor_set(x_872, 2, x_852);
lean_ctor_set(x_872, 3, x_871);
lean_ctor_set(x_872, 4, x_854);
lean_ctor_set(x_872, 5, x_855);
lean_ctor_set(x_872, 6, x_856);
lean_ctor_set(x_872, 7, x_857);
lean_ctor_set(x_872, 8, x_858);
lean_ctor_set(x_872, 9, x_859);
lean_ctor_set(x_872, 10, x_860);
lean_ctor_set(x_872, 11, x_862);
lean_ctor_set(x_872, 12, x_864);
lean_ctor_set_uint8(x_872, sizeof(void*)*13, x_861);
lean_ctor_set_uint8(x_872, sizeof(void*)*13 + 1, x_863);
x_998 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_999 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_998, x_872, x_869);
x_1000 = lean_ctor_get(x_999, 0);
lean_inc(x_1000);
x_1001 = lean_ctor_get(x_999, 1);
lean_inc(x_1001);
if (lean_is_exclusive(x_999)) {
 lean_ctor_release(x_999, 0);
 lean_ctor_release(x_999, 1);
 x_1002 = x_999;
} else {
 lean_dec_ref(x_999);
 x_1002 = lean_box(0);
}
x_1003 = lean_box(0);
x_1095 = lean_unbox(x_1000);
lean_dec(x_1000);
if (x_1095 == 0)
{
lean_dec(x_1002);
x_1028 = x_2;
x_1029 = x_3;
x_1030 = x_4;
x_1031 = x_5;
x_1032 = x_6;
x_1033 = x_7;
x_1034 = x_872;
x_1035 = x_9;
x_1036 = x_1001;
goto block_1094;
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; 
lean_inc(x_1);
x_1096 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_1001);
x_1097 = lean_ctor_get(x_1096, 0);
lean_inc(x_1097);
x_1098 = lean_ctor_get(x_1096, 1);
lean_inc(x_1098);
if (lean_is_exclusive(x_1096)) {
 lean_ctor_release(x_1096, 0);
 lean_ctor_release(x_1096, 1);
 x_1099 = x_1096;
} else {
 lean_dec_ref(x_1096);
 x_1099 = lean_box(0);
}
x_1100 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1099)) {
 x_1101 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1101 = x_1099;
 lean_ctor_set_tag(x_1101, 7);
}
lean_ctor_set(x_1101, 0, x_1100);
lean_ctor_set(x_1101, 1, x_1097);
if (lean_is_scalar(x_1002)) {
 x_1102 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1102 = x_1002;
 lean_ctor_set_tag(x_1102, 7);
}
lean_ctor_set(x_1102, 0, x_1101);
lean_ctor_set(x_1102, 1, x_1100);
x_1103 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_998, x_1102, x_6, x_7, x_872, x_9, x_1098);
x_1104 = lean_ctor_get(x_1103, 1);
lean_inc(x_1104);
lean_dec(x_1103);
x_1028 = x_2;
x_1029 = x_3;
x_1030 = x_4;
x_1031 = x_5;
x_1032 = x_6;
x_1033 = x_7;
x_1034 = x_872;
x_1035 = x_9;
x_1036 = x_1104;
goto block_1094;
}
block_997:
{
if (lean_obj_tag(x_888) == 0)
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; uint8_t x_892; 
lean_dec(x_887);
lean_dec(x_886);
lean_dec(x_884);
lean_dec(x_882);
lean_dec(x_880);
lean_dec(x_875);
x_889 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_890 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_889, x_883, x_878);
x_891 = lean_ctor_get(x_890, 0);
lean_inc(x_891);
x_892 = lean_unbox(x_891);
lean_dec(x_891);
if (x_892 == 0)
{
lean_object* x_893; 
x_893 = lean_ctor_get(x_890, 1);
lean_inc(x_893);
lean_dec(x_890);
x_11 = x_873;
x_12 = x_879;
x_13 = x_876;
x_14 = x_885;
x_15 = x_874;
x_16 = x_877;
x_17 = x_883;
x_18 = x_881;
x_19 = x_893;
goto block_163;
}
else
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_894 = lean_ctor_get(x_890, 1);
lean_inc(x_894);
if (lean_is_exclusive(x_890)) {
 lean_ctor_release(x_890, 0);
 lean_ctor_release(x_890, 1);
 x_895 = x_890;
} else {
 lean_dec_ref(x_890);
 x_895 = lean_box(0);
}
lean_inc(x_873);
x_896 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_873, x_885, x_894);
x_897 = lean_ctor_get(x_896, 0);
lean_inc(x_897);
x_898 = lean_ctor_get(x_896, 1);
lean_inc(x_898);
if (lean_is_exclusive(x_896)) {
 lean_ctor_release(x_896, 0);
 lean_ctor_release(x_896, 1);
 x_899 = x_896;
} else {
 lean_dec_ref(x_896);
 x_899 = lean_box(0);
}
x_900 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_899)) {
 x_901 = lean_alloc_ctor(7, 2, 0);
} else {
 x_901 = x_899;
 lean_ctor_set_tag(x_901, 7);
}
lean_ctor_set(x_901, 0, x_900);
lean_ctor_set(x_901, 1, x_897);
if (lean_is_scalar(x_895)) {
 x_902 = lean_alloc_ctor(7, 2, 0);
} else {
 x_902 = x_895;
 lean_ctor_set_tag(x_902, 7);
}
lean_ctor_set(x_902, 0, x_901);
lean_ctor_set(x_902, 1, x_900);
x_903 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_889, x_902, x_874, x_877, x_883, x_881, x_898);
x_904 = lean_ctor_get(x_903, 1);
lean_inc(x_904);
lean_dec(x_903);
x_11 = x_873;
x_12 = x_879;
x_13 = x_876;
x_14 = x_885;
x_15 = x_874;
x_16 = x_877;
x_17 = x_883;
x_18 = x_881;
x_19 = x_904;
goto block_163;
}
}
else
{
lean_object* x_905; lean_object* x_906; 
lean_dec(x_879);
x_905 = lean_ctor_get(x_888, 0);
lean_inc(x_905);
lean_dec(x_888);
x_906 = lean_ctor_get(x_905, 1);
lean_inc(x_906);
if (lean_obj_tag(x_906) == 0)
{
lean_object* x_907; 
lean_dec(x_906);
lean_dec(x_887);
lean_dec(x_886);
lean_dec(x_884);
lean_dec(x_882);
lean_dec(x_880);
lean_dec(x_876);
lean_dec(x_875);
lean_dec(x_873);
x_907 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_905, x_885, x_874, x_877, x_883, x_881, x_878);
lean_dec(x_881);
lean_dec(x_883);
lean_dec(x_877);
lean_dec(x_874);
lean_dec(x_885);
return x_907;
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; uint8_t x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; uint8_t x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; uint8_t x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; 
x_908 = lean_ctor_get(x_905, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_906, 0);
lean_inc(x_909);
x_910 = lean_ctor_get(x_906, 2);
lean_inc(x_910);
if (lean_is_exclusive(x_906)) {
 lean_ctor_release(x_906, 0);
 lean_ctor_release(x_906, 1);
 lean_ctor_release(x_906, 2);
 x_911 = x_906;
} else {
 lean_dec_ref(x_906);
 x_911 = lean_box(0);
}
x_912 = lean_int_mul(x_875, x_908);
x_913 = lean_int_mul(x_909, x_880);
x_914 = l_Lean_Meta_Grind_Arith_gcdExt(x_912, x_913);
lean_dec(x_913);
lean_dec(x_912);
x_915 = lean_ctor_get(x_914, 1);
lean_inc(x_915);
x_916 = lean_ctor_get(x_914, 0);
lean_inc(x_916);
lean_dec(x_914);
x_917 = lean_ctor_get(x_915, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_915, 1);
lean_inc(x_918);
lean_dec(x_915);
x_919 = lean_st_ref_take(x_885, x_878);
x_920 = lean_ctor_get(x_919, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_920, 14);
lean_inc(x_921);
x_922 = lean_ctor_get(x_921, 1);
lean_inc(x_922);
x_923 = lean_ctor_get(x_919, 1);
lean_inc(x_923);
lean_dec(x_919);
x_924 = lean_ctor_get(x_920, 0);
lean_inc(x_924);
x_925 = lean_ctor_get(x_920, 1);
lean_inc(x_925);
x_926 = lean_ctor_get(x_920, 2);
lean_inc(x_926);
x_927 = lean_ctor_get(x_920, 3);
lean_inc(x_927);
x_928 = lean_ctor_get(x_920, 4);
lean_inc(x_928);
x_929 = lean_ctor_get(x_920, 5);
lean_inc(x_929);
x_930 = lean_ctor_get(x_920, 6);
lean_inc(x_930);
x_931 = lean_ctor_get(x_920, 7);
lean_inc(x_931);
x_932 = lean_ctor_get_uint8(x_920, sizeof(void*)*16);
x_933 = lean_ctor_get(x_920, 8);
lean_inc(x_933);
x_934 = lean_ctor_get(x_920, 9);
lean_inc(x_934);
x_935 = lean_ctor_get(x_920, 10);
lean_inc(x_935);
x_936 = lean_ctor_get(x_920, 11);
lean_inc(x_936);
x_937 = lean_ctor_get(x_920, 12);
lean_inc(x_937);
x_938 = lean_ctor_get(x_920, 13);
lean_inc(x_938);
x_939 = lean_ctor_get(x_920, 15);
lean_inc(x_939);
if (lean_is_exclusive(x_920)) {
 lean_ctor_release(x_920, 0);
 lean_ctor_release(x_920, 1);
 lean_ctor_release(x_920, 2);
 lean_ctor_release(x_920, 3);
 lean_ctor_release(x_920, 4);
 lean_ctor_release(x_920, 5);
 lean_ctor_release(x_920, 6);
 lean_ctor_release(x_920, 7);
 lean_ctor_release(x_920, 8);
 lean_ctor_release(x_920, 9);
 lean_ctor_release(x_920, 10);
 lean_ctor_release(x_920, 11);
 lean_ctor_release(x_920, 12);
 lean_ctor_release(x_920, 13);
 lean_ctor_release(x_920, 14);
 lean_ctor_release(x_920, 15);
 x_940 = x_920;
} else {
 lean_dec_ref(x_920);
 x_940 = lean_box(0);
}
x_941 = lean_ctor_get(x_921, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_921, 2);
lean_inc(x_942);
x_943 = lean_ctor_get(x_921, 3);
lean_inc(x_943);
if (lean_is_exclusive(x_921)) {
 lean_ctor_release(x_921, 0);
 lean_ctor_release(x_921, 1);
 lean_ctor_release(x_921, 2);
 lean_ctor_release(x_921, 3);
 x_944 = x_921;
} else {
 lean_dec_ref(x_921);
 x_944 = lean_box(0);
}
x_945 = lean_ctor_get(x_922, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_922, 1);
lean_inc(x_946);
x_947 = lean_ctor_get(x_922, 2);
lean_inc(x_947);
x_948 = lean_ctor_get(x_922, 3);
lean_inc(x_948);
x_949 = lean_ctor_get(x_922, 4);
lean_inc(x_949);
x_950 = lean_ctor_get(x_922, 5);
lean_inc(x_950);
x_951 = lean_ctor_get(x_922, 6);
lean_inc(x_951);
x_952 = lean_ctor_get(x_922, 7);
lean_inc(x_952);
x_953 = lean_ctor_get(x_922, 8);
lean_inc(x_953);
x_954 = lean_ctor_get(x_922, 9);
lean_inc(x_954);
x_955 = lean_ctor_get(x_922, 10);
lean_inc(x_955);
x_956 = lean_ctor_get(x_922, 11);
lean_inc(x_956);
x_957 = lean_ctor_get(x_922, 12);
lean_inc(x_957);
x_958 = lean_ctor_get(x_922, 13);
lean_inc(x_958);
x_959 = lean_ctor_get(x_922, 14);
lean_inc(x_959);
x_960 = lean_ctor_get(x_922, 15);
lean_inc(x_960);
x_961 = lean_ctor_get_uint8(x_922, sizeof(void*)*21);
x_962 = lean_ctor_get(x_922, 16);
lean_inc(x_962);
x_963 = lean_ctor_get(x_922, 17);
lean_inc(x_963);
x_964 = lean_ctor_get(x_922, 18);
lean_inc(x_964);
x_965 = lean_ctor_get(x_922, 19);
lean_inc(x_965);
x_966 = lean_ctor_get(x_922, 20);
lean_inc(x_966);
x_967 = lean_ctor_get_uint8(x_922, sizeof(void*)*21 + 1);
if (lean_is_exclusive(x_922)) {
 lean_ctor_release(x_922, 0);
 lean_ctor_release(x_922, 1);
 lean_ctor_release(x_922, 2);
 lean_ctor_release(x_922, 3);
 lean_ctor_release(x_922, 4);
 lean_ctor_release(x_922, 5);
 lean_ctor_release(x_922, 6);
 lean_ctor_release(x_922, 7);
 lean_ctor_release(x_922, 8);
 lean_ctor_release(x_922, 9);
 lean_ctor_release(x_922, 10);
 lean_ctor_release(x_922, 11);
 lean_ctor_release(x_922, 12);
 lean_ctor_release(x_922, 13);
 lean_ctor_release(x_922, 14);
 lean_ctor_release(x_922, 15);
 lean_ctor_release(x_922, 16);
 lean_ctor_release(x_922, 17);
 lean_ctor_release(x_922, 18);
 lean_ctor_release(x_922, 19);
 lean_ctor_release(x_922, 20);
 x_968 = x_922;
} else {
 lean_dec_ref(x_922);
 x_968 = lean_box(0);
}
x_969 = lean_box(0);
x_970 = l_Lean_PersistentArray_set___redArg(x_952, x_876, x_969);
if (lean_is_scalar(x_968)) {
 x_971 = lean_alloc_ctor(0, 21, 2);
} else {
 x_971 = x_968;
}
lean_ctor_set(x_971, 0, x_945);
lean_ctor_set(x_971, 1, x_946);
lean_ctor_set(x_971, 2, x_947);
lean_ctor_set(x_971, 3, x_948);
lean_ctor_set(x_971, 4, x_949);
lean_ctor_set(x_971, 5, x_950);
lean_ctor_set(x_971, 6, x_951);
lean_ctor_set(x_971, 7, x_970);
lean_ctor_set(x_971, 8, x_953);
lean_ctor_set(x_971, 9, x_954);
lean_ctor_set(x_971, 10, x_955);
lean_ctor_set(x_971, 11, x_956);
lean_ctor_set(x_971, 12, x_957);
lean_ctor_set(x_971, 13, x_958);
lean_ctor_set(x_971, 14, x_959);
lean_ctor_set(x_971, 15, x_960);
lean_ctor_set(x_971, 16, x_962);
lean_ctor_set(x_971, 17, x_963);
lean_ctor_set(x_971, 18, x_964);
lean_ctor_set(x_971, 19, x_965);
lean_ctor_set(x_971, 20, x_966);
lean_ctor_set_uint8(x_971, sizeof(void*)*21, x_961);
lean_ctor_set_uint8(x_971, sizeof(void*)*21 + 1, x_967);
if (lean_is_scalar(x_944)) {
 x_972 = lean_alloc_ctor(0, 4, 0);
} else {
 x_972 = x_944;
}
lean_ctor_set(x_972, 0, x_941);
lean_ctor_set(x_972, 1, x_971);
lean_ctor_set(x_972, 2, x_942);
lean_ctor_set(x_972, 3, x_943);
if (lean_is_scalar(x_940)) {
 x_973 = lean_alloc_ctor(0, 16, 1);
} else {
 x_973 = x_940;
}
lean_ctor_set(x_973, 0, x_924);
lean_ctor_set(x_973, 1, x_925);
lean_ctor_set(x_973, 2, x_926);
lean_ctor_set(x_973, 3, x_927);
lean_ctor_set(x_973, 4, x_928);
lean_ctor_set(x_973, 5, x_929);
lean_ctor_set(x_973, 6, x_930);
lean_ctor_set(x_973, 7, x_931);
lean_ctor_set(x_973, 8, x_933);
lean_ctor_set(x_973, 9, x_934);
lean_ctor_set(x_973, 10, x_935);
lean_ctor_set(x_973, 11, x_936);
lean_ctor_set(x_973, 12, x_937);
lean_ctor_set(x_973, 13, x_938);
lean_ctor_set(x_973, 14, x_972);
lean_ctor_set(x_973, 15, x_939);
lean_ctor_set_uint8(x_973, sizeof(void*)*16, x_932);
x_974 = lean_st_ref_set(x_885, x_973, x_923);
x_975 = lean_ctor_get(x_974, 1);
lean_inc(x_975);
if (lean_is_exclusive(x_974)) {
 lean_ctor_release(x_974, 0);
 lean_ctor_release(x_974, 1);
 x_976 = x_974;
} else {
 lean_dec_ref(x_974);
 x_976 = lean_box(0);
}
x_977 = lean_int_mul(x_917, x_908);
lean_dec(x_917);
lean_inc(x_887);
x_978 = l_Int_Linear_Poly_mul(x_887, x_977);
lean_dec(x_977);
x_979 = lean_int_mul(x_918, x_880);
lean_dec(x_918);
lean_inc(x_910);
x_980 = l_Int_Linear_Poly_mul(x_910, x_979);
lean_dec(x_979);
x_981 = lean_int_mul(x_880, x_908);
lean_dec(x_908);
lean_dec(x_880);
x_982 = l_Int_Linear_Poly_combine(x_978, x_980);
lean_inc(x_916);
if (lean_is_scalar(x_911)) {
 x_983 = lean_alloc_ctor(1, 3, 0);
} else {
 x_983 = x_911;
}
lean_ctor_set(x_983, 0, x_916);
lean_ctor_set(x_983, 1, x_876);
lean_ctor_set(x_983, 2, x_982);
lean_inc(x_905);
lean_inc(x_873);
if (lean_is_scalar(x_976)) {
 x_984 = lean_alloc_ctor(4, 2, 0);
} else {
 x_984 = x_976;
 lean_ctor_set_tag(x_984, 4);
}
lean_ctor_set(x_984, 0, x_873);
lean_ctor_set(x_984, 1, x_905);
x_985 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_985, 0, x_981);
lean_ctor_set(x_985, 1, x_983);
lean_ctor_set(x_985, 2, x_984);
lean_inc(x_881);
lean_inc(x_883);
lean_inc(x_877);
lean_inc(x_874);
lean_inc(x_886);
lean_inc(x_884);
lean_inc(x_882);
lean_inc(x_885);
x_986 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_985, x_885, x_882, x_884, x_886, x_874, x_877, x_883, x_881, x_975);
if (lean_obj_tag(x_986) == 0)
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_987 = lean_ctor_get(x_986, 1);
lean_inc(x_987);
if (lean_is_exclusive(x_986)) {
 lean_ctor_release(x_986, 0);
 lean_ctor_release(x_986, 1);
 x_988 = x_986;
} else {
 lean_dec_ref(x_986);
 x_988 = lean_box(0);
}
x_989 = l_Int_Linear_Poly_mul(x_887, x_909);
lean_dec(x_909);
x_990 = lean_int_neg(x_875);
lean_dec(x_875);
x_991 = l_Int_Linear_Poly_mul(x_910, x_990);
lean_dec(x_990);
x_992 = l_Int_Linear_Poly_combine(x_989, x_991);
lean_inc(x_905);
if (lean_is_scalar(x_988)) {
 x_993 = lean_alloc_ctor(5, 2, 0);
} else {
 x_993 = x_988;
 lean_ctor_set_tag(x_993, 5);
}
lean_ctor_set(x_993, 0, x_873);
lean_ctor_set(x_993, 1, x_905);
if (lean_is_exclusive(x_905)) {
 lean_ctor_release(x_905, 0);
 lean_ctor_release(x_905, 1);
 lean_ctor_release(x_905, 2);
 x_994 = x_905;
} else {
 lean_dec_ref(x_905);
 x_994 = lean_box(0);
}
if (lean_is_scalar(x_994)) {
 x_995 = lean_alloc_ctor(0, 3, 0);
} else {
 x_995 = x_994;
}
lean_ctor_set(x_995, 0, x_916);
lean_ctor_set(x_995, 1, x_992);
lean_ctor_set(x_995, 2, x_993);
x_1 = x_995;
x_2 = x_885;
x_3 = x_882;
x_4 = x_884;
x_5 = x_886;
x_6 = x_874;
x_7 = x_877;
x_8 = x_883;
x_9 = x_881;
x_10 = x_987;
goto _start;
}
else
{
lean_dec(x_916);
lean_dec(x_910);
lean_dec(x_909);
lean_dec(x_905);
lean_dec(x_887);
lean_dec(x_886);
lean_dec(x_885);
lean_dec(x_884);
lean_dec(x_883);
lean_dec(x_882);
lean_dec(x_881);
lean_dec(x_877);
lean_dec(x_875);
lean_dec(x_874);
lean_dec(x_873);
return x_986;
}
}
}
}
block_1027:
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; uint8_t x_1024; 
x_1019 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_1010, x_1018);
x_1020 = lean_ctor_get(x_1019, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1020, 7);
lean_inc(x_1021);
lean_dec(x_1020);
x_1022 = lean_ctor_get(x_1019, 1);
lean_inc(x_1022);
lean_dec(x_1019);
x_1023 = lean_ctor_get(x_1021, 2);
lean_inc(x_1023);
x_1024 = lean_nat_dec_lt(x_1008, x_1023);
lean_dec(x_1023);
if (x_1024 == 0)
{
lean_object* x_1025; 
lean_dec(x_1021);
x_1025 = l_outOfBounds___redArg(x_1003);
x_873 = x_1005;
x_874 = x_1014;
x_875 = x_1007;
x_876 = x_1008;
x_877 = x_1015;
x_878 = x_1022;
x_879 = x_1004;
x_880 = x_1006;
x_881 = x_1017;
x_882 = x_1011;
x_883 = x_1016;
x_884 = x_1012;
x_885 = x_1010;
x_886 = x_1013;
x_887 = x_1009;
x_888 = x_1025;
goto block_997;
}
else
{
lean_object* x_1026; 
x_1026 = l_Lean_PersistentArray_get_x21___redArg(x_1003, x_1021, x_1008);
x_873 = x_1005;
x_874 = x_1014;
x_875 = x_1007;
x_876 = x_1008;
x_877 = x_1015;
x_878 = x_1022;
x_879 = x_1004;
x_880 = x_1006;
x_881 = x_1017;
x_882 = x_1011;
x_883 = x_1016;
x_884 = x_1012;
x_885 = x_1010;
x_886 = x_1013;
x_887 = x_1009;
x_888 = x_1026;
goto block_997;
}
}
block_1094:
{
lean_object* x_1037; lean_object* x_1038; 
x_1037 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_1034);
x_1038 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_1037, x_1028, x_1032, x_1033, x_1034, x_1035, x_1036);
if (lean_obj_tag(x_1038) == 0)
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; uint8_t x_1043; 
x_1039 = lean_ctor_get(x_1038, 0);
lean_inc(x_1039);
x_1040 = lean_ctor_get(x_1038, 1);
lean_inc(x_1040);
lean_dec(x_1038);
x_1041 = lean_ctor_get(x_1039, 0);
lean_inc(x_1041);
x_1042 = lean_ctor_get(x_1039, 1);
lean_inc(x_1042);
lean_inc(x_1041);
x_1043 = l_Int_Linear_Poly_isUnsatDvd(x_1041, x_1042);
if (x_1043 == 0)
{
uint8_t x_1044; 
x_1044 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_1039);
if (x_1044 == 0)
{
if (lean_obj_tag(x_1042) == 0)
{
lean_object* x_1045; 
lean_dec(x_1042);
lean_dec(x_1041);
lean_dec(x_1031);
lean_dec(x_1030);
lean_dec(x_1029);
x_1045 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_1039, x_1028, x_1032, x_1033, x_1034, x_1035, x_1040);
lean_dec(x_1035);
lean_dec(x_1034);
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_1028);
return x_1045;
}
else
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; uint8_t x_1053; uint8_t x_1054; uint8_t x_1055; 
x_1046 = lean_ctor_get(x_1042, 0);
lean_inc(x_1046);
x_1047 = lean_ctor_get(x_1042, 1);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1042, 2);
lean_inc(x_1048);
lean_inc(x_1039);
x_1049 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_1039, x_1028, x_1040);
x_1050 = lean_ctor_get(x_1049, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1049, 1);
lean_inc(x_1051);
lean_dec(x_1049);
x_1052 = lean_box(0);
x_1053 = lean_unbox(x_1050);
lean_dec(x_1050);
x_1054 = lean_unbox(x_1052);
x_1055 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_1053, x_1054);
if (x_1055 == 0)
{
x_1004 = x_1042;
x_1005 = x_1039;
x_1006 = x_1041;
x_1007 = x_1046;
x_1008 = x_1047;
x_1009 = x_1048;
x_1010 = x_1028;
x_1011 = x_1029;
x_1012 = x_1030;
x_1013 = x_1031;
x_1014 = x_1032;
x_1015 = x_1033;
x_1016 = x_1034;
x_1017 = x_1035;
x_1018 = x_1051;
goto block_1027;
}
else
{
lean_object* x_1056; lean_object* x_1057; 
x_1056 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_1047, x_1028, x_1051);
x_1057 = lean_ctor_get(x_1056, 1);
lean_inc(x_1057);
lean_dec(x_1056);
x_1004 = x_1042;
x_1005 = x_1039;
x_1006 = x_1041;
x_1007 = x_1046;
x_1008 = x_1047;
x_1009 = x_1048;
x_1010 = x_1028;
x_1011 = x_1029;
x_1012 = x_1030;
x_1013 = x_1031;
x_1014 = x_1032;
x_1015 = x_1033;
x_1016 = x_1034;
x_1017 = x_1035;
x_1018 = x_1057;
goto block_1027;
}
}
}
else
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; uint8_t x_1061; 
lean_dec(x_1042);
lean_dec(x_1041);
lean_dec(x_1031);
lean_dec(x_1030);
lean_dec(x_1029);
x_1058 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_1059 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1058, x_1034, x_1040);
x_1060 = lean_ctor_get(x_1059, 0);
lean_inc(x_1060);
x_1061 = lean_unbox(x_1060);
lean_dec(x_1060);
if (x_1061 == 0)
{
lean_object* x_1062; 
lean_dec(x_1039);
lean_dec(x_1035);
lean_dec(x_1034);
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_1028);
x_1062 = lean_ctor_get(x_1059, 1);
lean_inc(x_1062);
lean_dec(x_1059);
x_183 = x_1062;
goto block_186;
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; 
x_1063 = lean_ctor_get(x_1059, 1);
lean_inc(x_1063);
if (lean_is_exclusive(x_1059)) {
 lean_ctor_release(x_1059, 0);
 lean_ctor_release(x_1059, 1);
 x_1064 = x_1059;
} else {
 lean_dec_ref(x_1059);
 x_1064 = lean_box(0);
}
x_1065 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1039, x_1028, x_1063);
lean_dec(x_1028);
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1065, 1);
lean_inc(x_1067);
if (lean_is_exclusive(x_1065)) {
 lean_ctor_release(x_1065, 0);
 lean_ctor_release(x_1065, 1);
 x_1068 = x_1065;
} else {
 lean_dec_ref(x_1065);
 x_1068 = lean_box(0);
}
x_1069 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1068)) {
 x_1070 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1070 = x_1068;
 lean_ctor_set_tag(x_1070, 7);
}
lean_ctor_set(x_1070, 0, x_1069);
lean_ctor_set(x_1070, 1, x_1066);
if (lean_is_scalar(x_1064)) {
 x_1071 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1071 = x_1064;
 lean_ctor_set_tag(x_1071, 7);
}
lean_ctor_set(x_1071, 0, x_1070);
lean_ctor_set(x_1071, 1, x_1069);
x_1072 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1058, x_1071, x_1032, x_1033, x_1034, x_1035, x_1067);
lean_dec(x_1035);
lean_dec(x_1034);
lean_dec(x_1033);
lean_dec(x_1032);
x_1073 = lean_ctor_get(x_1072, 1);
lean_inc(x_1073);
lean_dec(x_1072);
x_183 = x_1073;
goto block_186;
}
}
}
else
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; uint8_t x_1077; 
lean_dec(x_1042);
lean_dec(x_1041);
x_1074 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_1075 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1074, x_1034, x_1040);
x_1076 = lean_ctor_get(x_1075, 0);
lean_inc(x_1076);
x_1077 = lean_unbox(x_1076);
lean_dec(x_1076);
if (x_1077 == 0)
{
lean_object* x_1078; 
x_1078 = lean_ctor_get(x_1075, 1);
lean_inc(x_1078);
lean_dec(x_1075);
x_164 = x_1039;
x_165 = x_1028;
x_166 = x_1029;
x_167 = x_1030;
x_168 = x_1031;
x_169 = x_1032;
x_170 = x_1033;
x_171 = x_1034;
x_172 = x_1035;
x_173 = x_1078;
goto block_182;
}
else
{
lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; 
x_1079 = lean_ctor_get(x_1075, 1);
lean_inc(x_1079);
if (lean_is_exclusive(x_1075)) {
 lean_ctor_release(x_1075, 0);
 lean_ctor_release(x_1075, 1);
 x_1080 = x_1075;
} else {
 lean_dec_ref(x_1075);
 x_1080 = lean_box(0);
}
lean_inc(x_1039);
x_1081 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1039, x_1028, x_1079);
x_1082 = lean_ctor_get(x_1081, 0);
lean_inc(x_1082);
x_1083 = lean_ctor_get(x_1081, 1);
lean_inc(x_1083);
if (lean_is_exclusive(x_1081)) {
 lean_ctor_release(x_1081, 0);
 lean_ctor_release(x_1081, 1);
 x_1084 = x_1081;
} else {
 lean_dec_ref(x_1081);
 x_1084 = lean_box(0);
}
x_1085 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1084)) {
 x_1086 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1086 = x_1084;
 lean_ctor_set_tag(x_1086, 7);
}
lean_ctor_set(x_1086, 0, x_1085);
lean_ctor_set(x_1086, 1, x_1082);
if (lean_is_scalar(x_1080)) {
 x_1087 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1087 = x_1080;
 lean_ctor_set_tag(x_1087, 7);
}
lean_ctor_set(x_1087, 0, x_1086);
lean_ctor_set(x_1087, 1, x_1085);
x_1088 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1074, x_1087, x_1032, x_1033, x_1034, x_1035, x_1083);
x_1089 = lean_ctor_get(x_1088, 1);
lean_inc(x_1089);
lean_dec(x_1088);
x_164 = x_1039;
x_165 = x_1028;
x_166 = x_1029;
x_167 = x_1030;
x_168 = x_1031;
x_169 = x_1032;
x_170 = x_1033;
x_171 = x_1034;
x_172 = x_1035;
x_173 = x_1089;
goto block_182;
}
}
}
else
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; 
lean_dec(x_1035);
lean_dec(x_1034);
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_1031);
lean_dec(x_1030);
lean_dec(x_1029);
lean_dec(x_1028);
x_1090 = lean_ctor_get(x_1038, 0);
lean_inc(x_1090);
x_1091 = lean_ctor_get(x_1038, 1);
lean_inc(x_1091);
if (lean_is_exclusive(x_1038)) {
 lean_ctor_release(x_1038, 0);
 lean_ctor_release(x_1038, 1);
 x_1092 = x_1038;
} else {
 lean_dec_ref(x_1038);
 x_1092 = lean_box(0);
}
if (lean_is_scalar(x_1092)) {
 x_1093 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1093 = x_1092;
}
lean_ctor_set(x_1093, 0, x_1090);
lean_ctor_set(x_1093, 1, x_1091);
return x_1093;
}
}
}
else
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
lean_dec(x_864);
lean_dec(x_862);
lean_dec(x_860);
lean_dec(x_859);
lean_dec(x_858);
lean_dec(x_857);
lean_dec(x_856);
lean_dec(x_855);
lean_dec(x_854);
lean_dec(x_853);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1105 = lean_ctor_get(x_866, 1);
lean_inc(x_1105);
if (lean_is_exclusive(x_866)) {
 lean_ctor_release(x_866, 0);
 lean_ctor_release(x_866, 1);
 x_1106 = x_866;
} else {
 lean_dec_ref(x_866);
 x_1106 = lean_box(0);
}
x_1107 = lean_box(0);
if (lean_is_scalar(x_1106)) {
 x_1108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1108 = x_1106;
}
lean_ctor_set(x_1108, 0, x_1107);
lean_ctor_set(x_1108, 1, x_1105);
return x_1108;
}
}
else
{
lean_object* x_1109; 
lean_dec(x_864);
lean_dec(x_862);
lean_dec(x_860);
lean_dec(x_859);
lean_dec(x_858);
lean_dec(x_857);
lean_dec(x_856);
lean_dec(x_854);
lean_dec(x_853);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1109 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_855, x_10);
return x_1109;
}
}
block_163:
{
lean_object* x_20; 
x_20 = l_Int_Linear_Poly_updateOccs___redArg(x_12, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_take(x_14, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 14);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
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
x_32 = lean_ctor_get(x_25, 7);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_11);
x_34 = l_Lean_PersistentArray_set___redArg(x_32, x_13, x_33);
lean_dec(x_13);
lean_ctor_set(x_25, 7, x_34);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
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
x_57 = lean_ctor_get(x_25, 15);
x_58 = lean_ctor_get_uint8(x_25, sizeof(void*)*21);
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
lean_inc(x_57);
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
lean_ctor_set(x_65, 0, x_11);
x_66 = l_Lean_PersistentArray_set___redArg(x_49, x_13, x_65);
lean_dec(x_13);
x_67 = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(x_67, 0, x_42);
lean_ctor_set(x_67, 1, x_43);
lean_ctor_set(x_67, 2, x_44);
lean_ctor_set(x_67, 3, x_45);
lean_ctor_set(x_67, 4, x_46);
lean_ctor_set(x_67, 5, x_47);
lean_ctor_set(x_67, 6, x_48);
lean_ctor_set(x_67, 7, x_66);
lean_ctor_set(x_67, 8, x_50);
lean_ctor_set(x_67, 9, x_51);
lean_ctor_set(x_67, 10, x_52);
lean_ctor_set(x_67, 11, x_53);
lean_ctor_set(x_67, 12, x_54);
lean_ctor_set(x_67, 13, x_55);
lean_ctor_set(x_67, 14, x_56);
lean_ctor_set(x_67, 15, x_57);
lean_ctor_set(x_67, 16, x_59);
lean_ctor_set(x_67, 17, x_60);
lean_ctor_set(x_67, 18, x_61);
lean_ctor_set(x_67, 19, x_62);
lean_ctor_set(x_67, 20, x_63);
lean_ctor_set_uint8(x_67, sizeof(void*)*21, x_58);
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
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_73 = lean_ctor_get(x_24, 0);
x_74 = lean_ctor_get(x_24, 2);
x_75 = lean_ctor_get(x_24, 3);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_24);
x_76 = lean_ctor_get(x_25, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_25, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_25, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_25, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_25, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_25, 5);
lean_inc(x_81);
x_82 = lean_ctor_get(x_25, 6);
lean_inc(x_82);
x_83 = lean_ctor_get(x_25, 7);
lean_inc(x_83);
x_84 = lean_ctor_get(x_25, 8);
lean_inc(x_84);
x_85 = lean_ctor_get(x_25, 9);
lean_inc(x_85);
x_86 = lean_ctor_get(x_25, 10);
lean_inc(x_86);
x_87 = lean_ctor_get(x_25, 11);
lean_inc(x_87);
x_88 = lean_ctor_get(x_25, 12);
lean_inc(x_88);
x_89 = lean_ctor_get(x_25, 13);
lean_inc(x_89);
x_90 = lean_ctor_get(x_25, 14);
lean_inc(x_90);
x_91 = lean_ctor_get(x_25, 15);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_25, sizeof(void*)*21);
x_93 = lean_ctor_get(x_25, 16);
lean_inc(x_93);
x_94 = lean_ctor_get(x_25, 17);
lean_inc(x_94);
x_95 = lean_ctor_get(x_25, 18);
lean_inc(x_95);
x_96 = lean_ctor_get(x_25, 19);
lean_inc(x_96);
x_97 = lean_ctor_get(x_25, 20);
lean_inc(x_97);
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
lean_ctor_set(x_100, 0, x_11);
x_101 = l_Lean_PersistentArray_set___redArg(x_83, x_13, x_100);
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
lean_ctor_set(x_102, 6, x_82);
lean_ctor_set(x_102, 7, x_101);
lean_ctor_set(x_102, 8, x_84);
lean_ctor_set(x_102, 9, x_85);
lean_ctor_set(x_102, 10, x_86);
lean_ctor_set(x_102, 11, x_87);
lean_ctor_set(x_102, 12, x_88);
lean_ctor_set(x_102, 13, x_89);
lean_ctor_set(x_102, 14, x_90);
lean_ctor_set(x_102, 15, x_91);
lean_ctor_set(x_102, 16, x_93);
lean_ctor_set(x_102, 17, x_94);
lean_ctor_set(x_102, 18, x_95);
lean_ctor_set(x_102, 19, x_96);
lean_ctor_set(x_102, 20, x_97);
lean_ctor_set_uint8(x_102, sizeof(void*)*21, x_92);
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
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
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
lean_inc(x_125);
x_126 = lean_ctor_get(x_24, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_24, 3);
lean_inc(x_127);
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
lean_inc(x_129);
x_130 = lean_ctor_get(x_25, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_25, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_25, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_25, 4);
lean_inc(x_133);
x_134 = lean_ctor_get(x_25, 5);
lean_inc(x_134);
x_135 = lean_ctor_get(x_25, 6);
lean_inc(x_135);
x_136 = lean_ctor_get(x_25, 7);
lean_inc(x_136);
x_137 = lean_ctor_get(x_25, 8);
lean_inc(x_137);
x_138 = lean_ctor_get(x_25, 9);
lean_inc(x_138);
x_139 = lean_ctor_get(x_25, 10);
lean_inc(x_139);
x_140 = lean_ctor_get(x_25, 11);
lean_inc(x_140);
x_141 = lean_ctor_get(x_25, 12);
lean_inc(x_141);
x_142 = lean_ctor_get(x_25, 13);
lean_inc(x_142);
x_143 = lean_ctor_get(x_25, 14);
lean_inc(x_143);
x_144 = lean_ctor_get(x_25, 15);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_25, sizeof(void*)*21);
x_146 = lean_ctor_get(x_25, 16);
lean_inc(x_146);
x_147 = lean_ctor_get(x_25, 17);
lean_inc(x_147);
x_148 = lean_ctor_get(x_25, 18);
lean_inc(x_148);
x_149 = lean_ctor_get(x_25, 19);
lean_inc(x_149);
x_150 = lean_ctor_get(x_25, 20);
lean_inc(x_150);
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
lean_ctor_set(x_153, 0, x_11);
x_154 = l_Lean_PersistentArray_set___redArg(x_136, x_13, x_153);
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
lean_ctor_set(x_155, 6, x_135);
lean_ctor_set(x_155, 7, x_154);
lean_ctor_set(x_155, 8, x_137);
lean_ctor_set(x_155, 9, x_138);
lean_ctor_set(x_155, 10, x_139);
lean_ctor_set(x_155, 11, x_140);
lean_ctor_set(x_155, 12, x_141);
lean_ctor_set(x_155, 13, x_142);
lean_ctor_set(x_155, 14, x_143);
lean_ctor_set(x_155, 15, x_144);
lean_ctor_set(x_155, 16, x_146);
lean_ctor_set(x_155, 17, x_147);
lean_ctor_set(x_155, 18, x_148);
lean_ctor_set(x_155, 19, x_149);
lean_ctor_set(x_155, 20, x_150);
lean_ctor_set_uint8(x_155, sizeof(void*)*21, x_145);
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
lean_dec(x_11);
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
lean_inc(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
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
lean_dec(x_13);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; uint8_t x_23; 
lean_inc(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
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
goto block_21;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
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
goto block_21;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
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
goto block_21;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
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
goto block_21;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_34 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_35 = l_Lean_Expr_isConstOf(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_dec(x_30);
lean_dec(x_27);
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
goto block_21;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_18);
x_36 = l_Lean_Meta_isInstDvdInt___redArg(x_30, x_7, x_17);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_27);
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
lean_dec(x_36);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_27);
x_46 = l_Lean_Meta_getIntValue_x3f(x_27, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_2);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_50, sizeof(void*)*6 + 11);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_11 = x_52;
goto block_14;
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_49, 1);
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
x_56 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
x_57 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_49, 7);
lean_ctor_set(x_49, 1, x_57);
lean_ctor_set(x_49, 0, x_56);
x_58 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Meta_Grind_reportIssue(x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_11 = x_61;
goto block_14;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
lean_dec(x_49);
x_63 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
x_64 = l_Lean_indentExpr(x_1);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Meta_Grind_reportIssue(x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_62);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_11 = x_69;
goto block_14;
}
}
}
else
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_46, 1);
lean_inc(x_70);
lean_dec(x_46);
x_71 = !lean_is_exclusive(x_47);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_47, 0);
lean_inc(x_1);
x_73 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_free_object(x_47);
lean_dec(x_72);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_1);
x_77 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_dec(x_27);
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
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
x_82 = lean_box(0);
lean_ctor_set(x_77, 0, x_82);
return x_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_dec(x_77);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_77, 1);
lean_inc(x_86);
lean_dec(x_77);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_87 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_91 = l_Lean_reflBoolTrue;
x_92 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_88);
x_93 = l_Lean_mkApp4(x_90, x_27, x_24, x_91, x_92);
x_94 = lean_unsigned_to_nat(0u);
x_95 = l_Lean_Meta_Grind_pushNewFact(x_93, x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_89);
return x_95;
}
else
{
uint8_t x_96; 
lean_dec(x_27);
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
x_96 = !lean_is_exclusive(x_87);
if (x_96 == 0)
{
return x_87;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_87, 0);
x_98 = lean_ctor_get(x_87, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_87);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_27);
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
x_100 = !lean_is_exclusive(x_77);
if (x_100 == 0)
{
return x_77;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_77, 0);
x_102 = lean_ctor_get(x_77, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_77);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_27);
x_104 = lean_ctor_get(x_73, 1);
lean_inc(x_104);
lean_dec(x_73);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_105 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_ctor_set_tag(x_47, 0);
lean_ctor_set(x_47, 0, x_1);
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_72);
lean_ctor_set(x_108, 1, x_106);
lean_ctor_set(x_108, 2, x_47);
x_109 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
return x_109;
}
else
{
uint8_t x_110; 
lean_free_object(x_47);
lean_dec(x_72);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_105);
if (x_110 == 0)
{
return x_105;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_105, 0);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_105);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_free_object(x_47);
lean_dec(x_72);
lean_dec(x_27);
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
x_114 = !lean_is_exclusive(x_73);
if (x_114 == 0)
{
return x_73;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_73, 0);
x_116 = lean_ctor_get(x_73, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_73);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_47, 0);
lean_inc(x_118);
lean_dec(x_47);
lean_inc(x_1);
x_119 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_70);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_118);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
lean_inc(x_1);
x_123 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_27);
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
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_127 = x_123;
} else {
 lean_dec_ref(x_123);
 x_127 = lean_box(0);
}
x_128 = lean_box(0);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_123, 1);
lean_inc(x_130);
lean_dec(x_123);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_131 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_135 = l_Lean_reflBoolTrue;
x_136 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_132);
x_137 = l_Lean_mkApp4(x_134, x_27, x_24, x_135, x_136);
x_138 = lean_unsigned_to_nat(0u);
x_139 = l_Lean_Meta_Grind_pushNewFact(x_137, x_138, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_133);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_27);
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
x_140 = lean_ctor_get(x_131, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_131, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_142 = x_131;
} else {
 lean_dec_ref(x_131);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_27);
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
x_144 = lean_ctor_get(x_123, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_123, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_146 = x_123;
} else {
 lean_dec_ref(x_123);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_27);
x_148 = lean_ctor_get(x_119, 1);
lean_inc(x_148);
lean_dec(x_119);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_149 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_1);
x_153 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_153, 0, x_118);
lean_ctor_set(x_153, 1, x_150);
lean_ctor_set(x_153, 2, x_152);
x_154 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_153, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_151);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_118);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_155 = lean_ctor_get(x_149, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_149, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_157 = x_149;
} else {
 lean_dec_ref(x_149);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_118);
lean_dec(x_27);
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
x_159 = lean_ctor_get(x_119, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_119, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_161 = x_119;
} else {
 lean_dec_ref(x_119);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_27);
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
x_163 = !lean_is_exclusive(x_46);
if (x_163 == 0)
{
return x_46;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_46, 0);
x_165 = lean_ctor_get(x_46, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_46);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
lean_inc(x_1);
x_23 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___redArg(x_2, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_22);
x_29 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_27, x_22, x_5, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_32 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_30, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_1);
x_35 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_33);
lean_dec(x_22);
lean_dec(x_21);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
lean_inc(x_1);
x_39 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_56; uint8_t x_57; 
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
lean_inc(x_1);
x_49 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_48);
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
x_56 = l_Lean_Expr_cleanupAnnotations(x_50);
x_57 = l_Lean_Expr_isApp(x_56);
if (x_57 == 0)
{
lean_dec(x_56);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_55;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
x_59 = l_Lean_Expr_appFnCleanup___redArg(x_56);
x_60 = l_Lean_Expr_isApp(x_59);
if (x_60 == 0)
{
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_55;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
x_62 = l_Lean_Expr_appFnCleanup___redArg(x_59);
x_63 = l_Lean_Expr_isApp(x_62);
if (x_63 == 0)
{
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_55;
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = l_Lean_Expr_appFnCleanup___redArg(x_62);
x_65 = l_Lean_Expr_isApp(x_64);
if (x_65 == 0)
{
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_55;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = l_Lean_Expr_appFnCleanup___redArg(x_64);
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_68 = l_Lean_Expr_isConstOf(x_66, x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_55;
}
else
{
lean_object* x_69; 
lean_dec(x_52);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_69 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_51);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_73 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_70);
x_74 = l_Lean_mkApp3(x_72, x_61, x_58, x_73);
x_75 = lean_unsigned_to_nat(0u);
x_76 = l_Lean_Meta_Grind_pushNewFact(x_74, x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_71);
return x_76;
}
else
{
uint8_t x_77; 
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_69);
if (x_77 == 0)
{
return x_69;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_69, 0);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_69);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
}
}
block_55:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_39);
if (x_81 == 0)
{
return x_39;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_39, 0);
x_83 = lean_ctor_get(x_39, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_39);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_35, 1);
lean_inc(x_85);
lean_dec(x_35);
x_86 = l_Int_Linear_Expr_norm(x_33);
lean_inc(x_21);
x_87 = lean_nat_to_int(x_21);
x_88 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_21);
lean_ctor_set(x_88, 2, x_22);
lean_ctor_set(x_88, 3, x_33);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_88);
x_90 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_85);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec(x_33);
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
x_91 = !lean_is_exclusive(x_35);
if (x_91 == 0)
{
return x_35;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_35, 0);
x_93 = lean_ctor_get(x_35, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_35);
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
x_95 = !lean_is_exclusive(x_32);
if (x_95 == 0)
{
return x_32;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_32, 0);
x_97 = lean_ctor_get(x_32, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_32);
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*6 + 20);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; uint8_t x_29; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
lean_inc(x_1);
x_21 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_20);
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
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_27;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_27;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_27;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_32);
x_35 = l_Lean_Expr_isApp(x_34);
if (x_35 == 0)
{
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_34);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_39 = l_Lean_Expr_isConstOf(x_37, x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_dec(x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_27;
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_24);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0;
x_41 = l_Lean_Expr_isConstOf(x_36, x_40);
lean_dec(x_36);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2765_(lean_object* x_1) {
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
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__8 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__8);
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
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0);
if (builtin) {res = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2765_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

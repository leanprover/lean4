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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_int_ediv(x_3, x_2);
lean_dec(x_3);
x_8 = l_Int_Linear_Poly_div(x_2, x_4);
lean_dec(x_2);
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
x_19 = lean_int_dec_eq(x_18, x_15);
lean_dec(x_15);
lean_dec(x_18);
if (x_19 == 0)
{
x_2 = x_16;
x_3 = x_12;
x_4 = x_14;
x_5 = x_13;
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
x_2 = x_16;
x_3 = x_12;
x_4 = x_14;
x_5 = x_13;
x_6 = x_19;
goto block_11;
}
else
{
lean_dec(x_16);
lean_dec(x_14);
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
x_12 = x_24;
x_13 = x_23;
x_14 = x_25;
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
x_13 = x_23;
x_14 = x_25;
x_15 = x_27;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_186; uint8_t x_190; 
x_190 = !lean_is_exclusive(x_8);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
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
x_204 = lean_nat_dec_eq(x_194, x_195);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_205 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_unbox(x_206);
lean_dec(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_605; lean_object* x_606; uint8_t x_607; 
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_dec(x_205);
x_209 = lean_unsigned_to_nat(1u);
x_210 = lean_nat_add(x_194, x_209);
lean_dec(x_194);
lean_ctor_set(x_8, 3, x_210);
x_605 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_606 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_605, x_8, x_208);
x_607 = !lean_is_exclusive(x_606);
if (x_607 == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; uint8_t x_731; 
x_608 = lean_ctor_get(x_606, 0);
x_609 = lean_ctor_get(x_606, 1);
x_610 = lean_box(0);
x_731 = lean_unbox(x_608);
lean_dec(x_608);
if (x_731 == 0)
{
lean_free_object(x_606);
x_635 = x_2;
x_636 = x_3;
x_637 = x_4;
x_638 = x_5;
x_639 = x_6;
x_640 = x_7;
x_641 = x_8;
x_642 = x_9;
x_643 = x_609;
goto block_730;
}
else
{
lean_object* x_732; uint8_t x_733; 
lean_inc(x_1);
x_732 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_609);
x_733 = !lean_is_exclusive(x_732);
if (x_733 == 0)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_734 = lean_ctor_get(x_732, 0);
x_735 = lean_ctor_get(x_732, 1);
x_736 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_732, 7);
lean_ctor_set(x_732, 1, x_734);
lean_ctor_set(x_732, 0, x_736);
lean_ctor_set_tag(x_606, 7);
lean_ctor_set(x_606, 1, x_736);
lean_ctor_set(x_606, 0, x_732);
x_737 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_605, x_606, x_6, x_7, x_8, x_9, x_735);
x_738 = lean_ctor_get(x_737, 1);
lean_inc(x_738);
lean_dec(x_737);
x_635 = x_2;
x_636 = x_3;
x_637 = x_4;
x_638 = x_5;
x_639 = x_6;
x_640 = x_7;
x_641 = x_8;
x_642 = x_9;
x_643 = x_738;
goto block_730;
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_739 = lean_ctor_get(x_732, 0);
x_740 = lean_ctor_get(x_732, 1);
lean_inc(x_740);
lean_inc(x_739);
lean_dec(x_732);
x_741 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_742 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_742, 0, x_741);
lean_ctor_set(x_742, 1, x_739);
lean_ctor_set_tag(x_606, 7);
lean_ctor_set(x_606, 1, x_741);
lean_ctor_set(x_606, 0, x_742);
x_743 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_605, x_606, x_6, x_7, x_8, x_9, x_740);
x_744 = lean_ctor_get(x_743, 1);
lean_inc(x_744);
lean_dec(x_743);
x_635 = x_2;
x_636 = x_3;
x_637 = x_4;
x_638 = x_5;
x_639 = x_6;
x_640 = x_7;
x_641 = x_8;
x_642 = x_9;
x_643 = x_744;
goto block_730;
}
}
block_634:
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; 
x_626 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_617, x_625);
x_627 = lean_ctor_get(x_626, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_627, 7);
lean_inc(x_628);
lean_dec(x_627);
x_629 = lean_ctor_get(x_626, 1);
lean_inc(x_629);
lean_dec(x_626);
x_630 = lean_ctor_get(x_628, 2);
lean_inc(x_630);
x_631 = lean_nat_dec_lt(x_611, x_630);
lean_dec(x_630);
if (x_631 == 0)
{
lean_object* x_632; 
lean_dec(x_628);
x_632 = l_outOfBounds___redArg(x_610);
x_211 = x_621;
x_212 = x_622;
x_213 = x_624;
x_214 = x_613;
x_215 = x_623;
x_216 = x_619;
x_217 = x_629;
x_218 = x_615;
x_219 = x_611;
x_220 = x_612;
x_221 = x_620;
x_222 = x_614;
x_223 = x_618;
x_224 = x_617;
x_225 = x_616;
x_226 = x_632;
goto block_604;
}
else
{
lean_object* x_633; 
x_633 = l_Lean_PersistentArray_get_x21___redArg(x_610, x_628, x_611);
x_211 = x_621;
x_212 = x_622;
x_213 = x_624;
x_214 = x_613;
x_215 = x_623;
x_216 = x_619;
x_217 = x_629;
x_218 = x_615;
x_219 = x_611;
x_220 = x_612;
x_221 = x_620;
x_222 = x_614;
x_223 = x_618;
x_224 = x_617;
x_225 = x_616;
x_226 = x_633;
goto block_604;
}
}
block_730:
{
lean_object* x_644; lean_object* x_645; 
x_644 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_641);
x_645 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_644, x_635, x_639, x_640, x_641, x_642, x_643);
if (lean_obj_tag(x_645) == 0)
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; uint8_t x_650; 
x_646 = lean_ctor_get(x_645, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_645, 1);
lean_inc(x_647);
lean_dec(x_645);
x_648 = lean_ctor_get(x_646, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_646, 1);
lean_inc(x_649);
lean_inc(x_648);
x_650 = l_Int_Linear_Poly_isUnsatDvd(x_648, x_649);
if (x_650 == 0)
{
uint8_t x_651; 
x_651 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_646);
if (x_651 == 0)
{
if (lean_obj_tag(x_649) == 0)
{
lean_object* x_652; 
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_638);
lean_dec(x_637);
lean_dec(x_636);
x_652 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_646, x_635, x_639, x_640, x_641, x_642, x_647);
lean_dec(x_642);
lean_dec(x_641);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_635);
return x_652;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; uint8_t x_659; uint8_t x_660; uint8_t x_661; 
x_653 = lean_ctor_get(x_649, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_649, 1);
lean_inc(x_654);
x_655 = lean_ctor_get(x_649, 2);
lean_inc(x_655);
lean_inc(x_646);
x_656 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_646, x_635, x_647);
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
lean_dec(x_656);
x_659 = 0;
x_660 = lean_unbox(x_657);
lean_dec(x_657);
x_661 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_660, x_659);
if (x_661 == 0)
{
x_611 = x_654;
x_612 = x_646;
x_613 = x_648;
x_614 = x_653;
x_615 = x_649;
x_616 = x_655;
x_617 = x_635;
x_618 = x_636;
x_619 = x_637;
x_620 = x_638;
x_621 = x_639;
x_622 = x_640;
x_623 = x_641;
x_624 = x_642;
x_625 = x_658;
goto block_634;
}
else
{
lean_object* x_662; lean_object* x_663; 
x_662 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_654, x_635, x_658);
x_663 = lean_ctor_get(x_662, 1);
lean_inc(x_663);
lean_dec(x_662);
x_611 = x_654;
x_612 = x_646;
x_613 = x_648;
x_614 = x_653;
x_615 = x_649;
x_616 = x_655;
x_617 = x_635;
x_618 = x_636;
x_619 = x_637;
x_620 = x_638;
x_621 = x_639;
x_622 = x_640;
x_623 = x_641;
x_624 = x_642;
x_625 = x_663;
goto block_634;
}
}
}
else
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; uint8_t x_667; 
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_638);
lean_dec(x_637);
lean_dec(x_636);
x_664 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_665 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_664, x_641, x_647);
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_unbox(x_666);
lean_dec(x_666);
if (x_667 == 0)
{
lean_object* x_668; 
lean_dec(x_646);
lean_dec(x_642);
lean_dec(x_641);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_635);
x_668 = lean_ctor_get(x_665, 1);
lean_inc(x_668);
lean_dec(x_665);
x_186 = x_668;
goto block_189;
}
else
{
uint8_t x_669; 
x_669 = !lean_is_exclusive(x_665);
if (x_669 == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; uint8_t x_673; 
x_670 = lean_ctor_get(x_665, 1);
x_671 = lean_ctor_get(x_665, 0);
lean_dec(x_671);
x_672 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_646, x_635, x_670);
lean_dec(x_635);
x_673 = !lean_is_exclusive(x_672);
if (x_673 == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_674 = lean_ctor_get(x_672, 0);
x_675 = lean_ctor_get(x_672, 1);
x_676 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_672, 7);
lean_ctor_set(x_672, 1, x_674);
lean_ctor_set(x_672, 0, x_676);
lean_ctor_set_tag(x_665, 7);
lean_ctor_set(x_665, 1, x_676);
lean_ctor_set(x_665, 0, x_672);
x_677 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_664, x_665, x_639, x_640, x_641, x_642, x_675);
lean_dec(x_642);
lean_dec(x_641);
lean_dec(x_640);
lean_dec(x_639);
x_678 = lean_ctor_get(x_677, 1);
lean_inc(x_678);
lean_dec(x_677);
x_186 = x_678;
goto block_189;
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_679 = lean_ctor_get(x_672, 0);
x_680 = lean_ctor_get(x_672, 1);
lean_inc(x_680);
lean_inc(x_679);
lean_dec(x_672);
x_681 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_682 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_682, 0, x_681);
lean_ctor_set(x_682, 1, x_679);
lean_ctor_set_tag(x_665, 7);
lean_ctor_set(x_665, 1, x_681);
lean_ctor_set(x_665, 0, x_682);
x_683 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_664, x_665, x_639, x_640, x_641, x_642, x_680);
lean_dec(x_642);
lean_dec(x_641);
lean_dec(x_640);
lean_dec(x_639);
x_684 = lean_ctor_get(x_683, 1);
lean_inc(x_684);
lean_dec(x_683);
x_186 = x_684;
goto block_189;
}
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
x_685 = lean_ctor_get(x_665, 1);
lean_inc(x_685);
lean_dec(x_665);
x_686 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_646, x_635, x_685);
lean_dec(x_635);
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_689 = x_686;
} else {
 lean_dec_ref(x_686);
 x_689 = lean_box(0);
}
x_690 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_689)) {
 x_691 = lean_alloc_ctor(7, 2, 0);
} else {
 x_691 = x_689;
 lean_ctor_set_tag(x_691, 7);
}
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_687);
x_692 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_692, 0, x_691);
lean_ctor_set(x_692, 1, x_690);
x_693 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_664, x_692, x_639, x_640, x_641, x_642, x_688);
lean_dec(x_642);
lean_dec(x_641);
lean_dec(x_640);
lean_dec(x_639);
x_694 = lean_ctor_get(x_693, 1);
lean_inc(x_694);
lean_dec(x_693);
x_186 = x_694;
goto block_189;
}
}
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; uint8_t x_698; 
lean_dec(x_649);
lean_dec(x_648);
x_695 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_696 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_695, x_641, x_647);
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_unbox(x_697);
lean_dec(x_697);
if (x_698 == 0)
{
lean_object* x_699; 
x_699 = lean_ctor_get(x_696, 1);
lean_inc(x_699);
lean_dec(x_696);
x_167 = x_646;
x_168 = x_635;
x_169 = x_636;
x_170 = x_637;
x_171 = x_638;
x_172 = x_639;
x_173 = x_640;
x_174 = x_641;
x_175 = x_642;
x_176 = x_699;
goto block_185;
}
else
{
uint8_t x_700; 
x_700 = !lean_is_exclusive(x_696);
if (x_700 == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; uint8_t x_704; 
x_701 = lean_ctor_get(x_696, 1);
x_702 = lean_ctor_get(x_696, 0);
lean_dec(x_702);
lean_inc(x_646);
x_703 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_646, x_635, x_701);
x_704 = !lean_is_exclusive(x_703);
if (x_704 == 0)
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_705 = lean_ctor_get(x_703, 0);
x_706 = lean_ctor_get(x_703, 1);
x_707 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_703, 7);
lean_ctor_set(x_703, 1, x_705);
lean_ctor_set(x_703, 0, x_707);
lean_ctor_set_tag(x_696, 7);
lean_ctor_set(x_696, 1, x_707);
lean_ctor_set(x_696, 0, x_703);
x_708 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_695, x_696, x_639, x_640, x_641, x_642, x_706);
x_709 = lean_ctor_get(x_708, 1);
lean_inc(x_709);
lean_dec(x_708);
x_167 = x_646;
x_168 = x_635;
x_169 = x_636;
x_170 = x_637;
x_171 = x_638;
x_172 = x_639;
x_173 = x_640;
x_174 = x_641;
x_175 = x_642;
x_176 = x_709;
goto block_185;
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_710 = lean_ctor_get(x_703, 0);
x_711 = lean_ctor_get(x_703, 1);
lean_inc(x_711);
lean_inc(x_710);
lean_dec(x_703);
x_712 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_713 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_713, 0, x_712);
lean_ctor_set(x_713, 1, x_710);
lean_ctor_set_tag(x_696, 7);
lean_ctor_set(x_696, 1, x_712);
lean_ctor_set(x_696, 0, x_713);
x_714 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_695, x_696, x_639, x_640, x_641, x_642, x_711);
x_715 = lean_ctor_get(x_714, 1);
lean_inc(x_715);
lean_dec(x_714);
x_167 = x_646;
x_168 = x_635;
x_169 = x_636;
x_170 = x_637;
x_171 = x_638;
x_172 = x_639;
x_173 = x_640;
x_174 = x_641;
x_175 = x_642;
x_176 = x_715;
goto block_185;
}
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_716 = lean_ctor_get(x_696, 1);
lean_inc(x_716);
lean_dec(x_696);
lean_inc(x_646);
x_717 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_646, x_635, x_716);
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 lean_ctor_release(x_717, 1);
 x_720 = x_717;
} else {
 lean_dec_ref(x_717);
 x_720 = lean_box(0);
}
x_721 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_720)) {
 x_722 = lean_alloc_ctor(7, 2, 0);
} else {
 x_722 = x_720;
 lean_ctor_set_tag(x_722, 7);
}
lean_ctor_set(x_722, 0, x_721);
lean_ctor_set(x_722, 1, x_718);
x_723 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_721);
x_724 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_695, x_723, x_639, x_640, x_641, x_642, x_719);
x_725 = lean_ctor_get(x_724, 1);
lean_inc(x_725);
lean_dec(x_724);
x_167 = x_646;
x_168 = x_635;
x_169 = x_636;
x_170 = x_637;
x_171 = x_638;
x_172 = x_639;
x_173 = x_640;
x_174 = x_641;
x_175 = x_642;
x_176 = x_725;
goto block_185;
}
}
}
}
else
{
uint8_t x_726; 
lean_dec(x_642);
lean_dec(x_641);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_638);
lean_dec(x_637);
lean_dec(x_636);
lean_dec(x_635);
x_726 = !lean_is_exclusive(x_645);
if (x_726 == 0)
{
return x_645;
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_727 = lean_ctor_get(x_645, 0);
x_728 = lean_ctor_get(x_645, 1);
lean_inc(x_728);
lean_inc(x_727);
lean_dec(x_645);
x_729 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_729, 0, x_727);
lean_ctor_set(x_729, 1, x_728);
return x_729;
}
}
}
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; uint8_t x_838; 
x_745 = lean_ctor_get(x_606, 0);
x_746 = lean_ctor_get(x_606, 1);
lean_inc(x_746);
lean_inc(x_745);
lean_dec(x_606);
x_747 = lean_box(0);
x_838 = lean_unbox(x_745);
lean_dec(x_745);
if (x_838 == 0)
{
x_772 = x_2;
x_773 = x_3;
x_774 = x_4;
x_775 = x_5;
x_776 = x_6;
x_777 = x_7;
x_778 = x_8;
x_779 = x_9;
x_780 = x_746;
goto block_837;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
lean_inc(x_1);
x_839 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_746);
x_840 = lean_ctor_get(x_839, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_839, 1);
lean_inc(x_841);
if (lean_is_exclusive(x_839)) {
 lean_ctor_release(x_839, 0);
 lean_ctor_release(x_839, 1);
 x_842 = x_839;
} else {
 lean_dec_ref(x_839);
 x_842 = lean_box(0);
}
x_843 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_842)) {
 x_844 = lean_alloc_ctor(7, 2, 0);
} else {
 x_844 = x_842;
 lean_ctor_set_tag(x_844, 7);
}
lean_ctor_set(x_844, 0, x_843);
lean_ctor_set(x_844, 1, x_840);
x_845 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_845, 0, x_844);
lean_ctor_set(x_845, 1, x_843);
x_846 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_605, x_845, x_6, x_7, x_8, x_9, x_841);
x_847 = lean_ctor_get(x_846, 1);
lean_inc(x_847);
lean_dec(x_846);
x_772 = x_2;
x_773 = x_3;
x_774 = x_4;
x_775 = x_5;
x_776 = x_6;
x_777 = x_7;
x_778 = x_8;
x_779 = x_9;
x_780 = x_847;
goto block_837;
}
block_771:
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; uint8_t x_768; 
x_763 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_754, x_762);
x_764 = lean_ctor_get(x_763, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_764, 7);
lean_inc(x_765);
lean_dec(x_764);
x_766 = lean_ctor_get(x_763, 1);
lean_inc(x_766);
lean_dec(x_763);
x_767 = lean_ctor_get(x_765, 2);
lean_inc(x_767);
x_768 = lean_nat_dec_lt(x_748, x_767);
lean_dec(x_767);
if (x_768 == 0)
{
lean_object* x_769; 
lean_dec(x_765);
x_769 = l_outOfBounds___redArg(x_747);
x_211 = x_758;
x_212 = x_759;
x_213 = x_761;
x_214 = x_750;
x_215 = x_760;
x_216 = x_756;
x_217 = x_766;
x_218 = x_752;
x_219 = x_748;
x_220 = x_749;
x_221 = x_757;
x_222 = x_751;
x_223 = x_755;
x_224 = x_754;
x_225 = x_753;
x_226 = x_769;
goto block_604;
}
else
{
lean_object* x_770; 
x_770 = l_Lean_PersistentArray_get_x21___redArg(x_747, x_765, x_748);
x_211 = x_758;
x_212 = x_759;
x_213 = x_761;
x_214 = x_750;
x_215 = x_760;
x_216 = x_756;
x_217 = x_766;
x_218 = x_752;
x_219 = x_748;
x_220 = x_749;
x_221 = x_757;
x_222 = x_751;
x_223 = x_755;
x_224 = x_754;
x_225 = x_753;
x_226 = x_770;
goto block_604;
}
}
block_837:
{
lean_object* x_781; lean_object* x_782; 
x_781 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_778);
x_782 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_781, x_772, x_776, x_777, x_778, x_779, x_780);
if (lean_obj_tag(x_782) == 0)
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; uint8_t x_787; 
x_783 = lean_ctor_get(x_782, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_782, 1);
lean_inc(x_784);
lean_dec(x_782);
x_785 = lean_ctor_get(x_783, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_783, 1);
lean_inc(x_786);
lean_inc(x_785);
x_787 = l_Int_Linear_Poly_isUnsatDvd(x_785, x_786);
if (x_787 == 0)
{
uint8_t x_788; 
x_788 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_783);
if (x_788 == 0)
{
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_789; 
lean_dec(x_786);
lean_dec(x_785);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
x_789 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_783, x_772, x_776, x_777, x_778, x_779, x_784);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_776);
lean_dec(x_772);
return x_789;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; uint8_t x_796; uint8_t x_797; uint8_t x_798; 
x_790 = lean_ctor_get(x_786, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_786, 1);
lean_inc(x_791);
x_792 = lean_ctor_get(x_786, 2);
lean_inc(x_792);
lean_inc(x_783);
x_793 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_783, x_772, x_784);
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_793, 1);
lean_inc(x_795);
lean_dec(x_793);
x_796 = 0;
x_797 = lean_unbox(x_794);
lean_dec(x_794);
x_798 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_797, x_796);
if (x_798 == 0)
{
x_748 = x_791;
x_749 = x_783;
x_750 = x_785;
x_751 = x_790;
x_752 = x_786;
x_753 = x_792;
x_754 = x_772;
x_755 = x_773;
x_756 = x_774;
x_757 = x_775;
x_758 = x_776;
x_759 = x_777;
x_760 = x_778;
x_761 = x_779;
x_762 = x_795;
goto block_771;
}
else
{
lean_object* x_799; lean_object* x_800; 
x_799 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_791, x_772, x_795);
x_800 = lean_ctor_get(x_799, 1);
lean_inc(x_800);
lean_dec(x_799);
x_748 = x_791;
x_749 = x_783;
x_750 = x_785;
x_751 = x_790;
x_752 = x_786;
x_753 = x_792;
x_754 = x_772;
x_755 = x_773;
x_756 = x_774;
x_757 = x_775;
x_758 = x_776;
x_759 = x_777;
x_760 = x_778;
x_761 = x_779;
x_762 = x_800;
goto block_771;
}
}
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; uint8_t x_804; 
lean_dec(x_786);
lean_dec(x_785);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
x_801 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_802 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_801, x_778, x_784);
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
x_804 = lean_unbox(x_803);
lean_dec(x_803);
if (x_804 == 0)
{
lean_object* x_805; 
lean_dec(x_783);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_776);
lean_dec(x_772);
x_805 = lean_ctor_get(x_802, 1);
lean_inc(x_805);
lean_dec(x_802);
x_186 = x_805;
goto block_189;
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_806 = lean_ctor_get(x_802, 1);
lean_inc(x_806);
if (lean_is_exclusive(x_802)) {
 lean_ctor_release(x_802, 0);
 lean_ctor_release(x_802, 1);
 x_807 = x_802;
} else {
 lean_dec_ref(x_802);
 x_807 = lean_box(0);
}
x_808 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_783, x_772, x_806);
lean_dec(x_772);
x_809 = lean_ctor_get(x_808, 0);
lean_inc(x_809);
x_810 = lean_ctor_get(x_808, 1);
lean_inc(x_810);
if (lean_is_exclusive(x_808)) {
 lean_ctor_release(x_808, 0);
 lean_ctor_release(x_808, 1);
 x_811 = x_808;
} else {
 lean_dec_ref(x_808);
 x_811 = lean_box(0);
}
x_812 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_811)) {
 x_813 = lean_alloc_ctor(7, 2, 0);
} else {
 x_813 = x_811;
 lean_ctor_set_tag(x_813, 7);
}
lean_ctor_set(x_813, 0, x_812);
lean_ctor_set(x_813, 1, x_809);
if (lean_is_scalar(x_807)) {
 x_814 = lean_alloc_ctor(7, 2, 0);
} else {
 x_814 = x_807;
 lean_ctor_set_tag(x_814, 7);
}
lean_ctor_set(x_814, 0, x_813);
lean_ctor_set(x_814, 1, x_812);
x_815 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_801, x_814, x_776, x_777, x_778, x_779, x_810);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_776);
x_816 = lean_ctor_get(x_815, 1);
lean_inc(x_816);
lean_dec(x_815);
x_186 = x_816;
goto block_189;
}
}
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; uint8_t x_820; 
lean_dec(x_786);
lean_dec(x_785);
x_817 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_818 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_817, x_778, x_784);
x_819 = lean_ctor_get(x_818, 0);
lean_inc(x_819);
x_820 = lean_unbox(x_819);
lean_dec(x_819);
if (x_820 == 0)
{
lean_object* x_821; 
x_821 = lean_ctor_get(x_818, 1);
lean_inc(x_821);
lean_dec(x_818);
x_167 = x_783;
x_168 = x_772;
x_169 = x_773;
x_170 = x_774;
x_171 = x_775;
x_172 = x_776;
x_173 = x_777;
x_174 = x_778;
x_175 = x_779;
x_176 = x_821;
goto block_185;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_822 = lean_ctor_get(x_818, 1);
lean_inc(x_822);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 lean_ctor_release(x_818, 1);
 x_823 = x_818;
} else {
 lean_dec_ref(x_818);
 x_823 = lean_box(0);
}
lean_inc(x_783);
x_824 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_783, x_772, x_822);
x_825 = lean_ctor_get(x_824, 0);
lean_inc(x_825);
x_826 = lean_ctor_get(x_824, 1);
lean_inc(x_826);
if (lean_is_exclusive(x_824)) {
 lean_ctor_release(x_824, 0);
 lean_ctor_release(x_824, 1);
 x_827 = x_824;
} else {
 lean_dec_ref(x_824);
 x_827 = lean_box(0);
}
x_828 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_827)) {
 x_829 = lean_alloc_ctor(7, 2, 0);
} else {
 x_829 = x_827;
 lean_ctor_set_tag(x_829, 7);
}
lean_ctor_set(x_829, 0, x_828);
lean_ctor_set(x_829, 1, x_825);
if (lean_is_scalar(x_823)) {
 x_830 = lean_alloc_ctor(7, 2, 0);
} else {
 x_830 = x_823;
 lean_ctor_set_tag(x_830, 7);
}
lean_ctor_set(x_830, 0, x_829);
lean_ctor_set(x_830, 1, x_828);
x_831 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_817, x_830, x_776, x_777, x_778, x_779, x_826);
x_832 = lean_ctor_get(x_831, 1);
lean_inc(x_832);
lean_dec(x_831);
x_167 = x_783;
x_168 = x_772;
x_169 = x_773;
x_170 = x_774;
x_171 = x_775;
x_172 = x_776;
x_173 = x_777;
x_174 = x_778;
x_175 = x_779;
x_176 = x_832;
goto block_185;
}
}
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_772);
x_833 = lean_ctor_get(x_782, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_782, 1);
lean_inc(x_834);
if (lean_is_exclusive(x_782)) {
 lean_ctor_release(x_782, 0);
 lean_ctor_release(x_782, 1);
 x_835 = x_782;
} else {
 lean_dec_ref(x_782);
 x_835 = lean_box(0);
}
if (lean_is_scalar(x_835)) {
 x_836 = lean_alloc_ctor(1, 2, 0);
} else {
 x_836 = x_835;
}
lean_ctor_set(x_836, 0, x_833);
lean_ctor_set(x_836, 1, x_834);
return x_836;
}
}
}
block_604:
{
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
lean_dec(x_225);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_216);
lean_dec(x_214);
x_227 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_228 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_227, x_215, x_217);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_unbox(x_229);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
lean_dec(x_228);
x_11 = x_219;
x_12 = x_220;
x_13 = x_218;
x_14 = x_224;
x_15 = x_211;
x_16 = x_212;
x_17 = x_215;
x_18 = x_213;
x_19 = x_231;
goto block_166;
}
else
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_228);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_233 = lean_ctor_get(x_228, 1);
x_234 = lean_ctor_get(x_228, 0);
lean_dec(x_234);
lean_inc(x_220);
x_235 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_220, x_224, x_233);
x_236 = !lean_is_exclusive(x_235);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_237 = lean_ctor_get(x_235, 0);
x_238 = lean_ctor_get(x_235, 1);
x_239 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_235, 7);
lean_ctor_set(x_235, 1, x_237);
lean_ctor_set(x_235, 0, x_239);
lean_ctor_set_tag(x_228, 7);
lean_ctor_set(x_228, 1, x_239);
lean_ctor_set(x_228, 0, x_235);
x_240 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_227, x_228, x_211, x_212, x_215, x_213, x_238);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_11 = x_219;
x_12 = x_220;
x_13 = x_218;
x_14 = x_224;
x_15 = x_211;
x_16 = x_212;
x_17 = x_215;
x_18 = x_213;
x_19 = x_241;
goto block_166;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_242 = lean_ctor_get(x_235, 0);
x_243 = lean_ctor_get(x_235, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_235);
x_244 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_245 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_242);
lean_ctor_set_tag(x_228, 7);
lean_ctor_set(x_228, 1, x_244);
lean_ctor_set(x_228, 0, x_245);
x_246 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_227, x_228, x_211, x_212, x_215, x_213, x_243);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
lean_dec(x_246);
x_11 = x_219;
x_12 = x_220;
x_13 = x_218;
x_14 = x_224;
x_15 = x_211;
x_16 = x_212;
x_17 = x_215;
x_18 = x_213;
x_19 = x_247;
goto block_166;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_248 = lean_ctor_get(x_228, 1);
lean_inc(x_248);
lean_dec(x_228);
lean_inc(x_220);
x_249 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_220, x_224, x_248);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_252 = x_249;
} else {
 lean_dec_ref(x_249);
 x_252 = lean_box(0);
}
x_253 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_252)) {
 x_254 = lean_alloc_ctor(7, 2, 0);
} else {
 x_254 = x_252;
 lean_ctor_set_tag(x_254, 7);
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_250);
x_255 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
x_256 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_227, x_255, x_211, x_212, x_215, x_213, x_251);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
lean_dec(x_256);
x_11 = x_219;
x_12 = x_220;
x_13 = x_218;
x_14 = x_224;
x_15 = x_211;
x_16 = x_212;
x_17 = x_215;
x_18 = x_213;
x_19 = x_257;
goto block_166;
}
}
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_218);
x_258 = lean_ctor_get(x_226, 0);
lean_inc(x_258);
lean_dec(x_226);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; 
lean_dec(x_259);
lean_dec(x_225);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_216);
lean_dec(x_214);
x_260 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_258, x_224, x_211, x_212, x_215, x_213, x_217);
lean_dec(x_213);
lean_dec(x_215);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_224);
return x_260;
}
else
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_258, 0);
lean_inc(x_261);
x_262 = !lean_is_exclusive(x_259);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_263 = lean_ctor_get(x_259, 0);
x_264 = lean_ctor_get(x_259, 2);
x_265 = lean_ctor_get(x_259, 1);
lean_dec(x_265);
x_266 = lean_int_mul(x_222, x_261);
x_267 = lean_int_mul(x_263, x_214);
x_268 = l_Lean_Meta_Grind_Arith_gcdExt(x_266, x_267);
lean_dec(x_267);
lean_dec(x_266);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 0);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_269, 1);
lean_inc(x_272);
lean_dec(x_269);
x_273 = lean_st_ref_take(x_224, x_217);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_274, 14);
lean_inc(x_275);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_273, 1);
lean_inc(x_277);
lean_dec(x_273);
x_278 = !lean_is_exclusive(x_274);
if (x_278 == 0)
{
lean_object* x_279; uint8_t x_280; 
x_279 = lean_ctor_get(x_274, 14);
lean_dec(x_279);
x_280 = !lean_is_exclusive(x_275);
if (x_280 == 0)
{
lean_object* x_281; uint8_t x_282; 
x_281 = lean_ctor_get(x_275, 1);
lean_dec(x_281);
x_282 = !lean_is_exclusive(x_276);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_283 = lean_ctor_get(x_276, 7);
x_284 = lean_box(0);
x_285 = l_Lean_PersistentArray_set___redArg(x_283, x_219, x_284);
lean_ctor_set(x_276, 7, x_285);
x_286 = lean_st_ref_set(x_224, x_274, x_277);
x_287 = !lean_is_exclusive(x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_288 = lean_ctor_get(x_286, 1);
x_289 = lean_ctor_get(x_286, 0);
lean_dec(x_289);
x_290 = lean_int_mul(x_271, x_261);
lean_dec(x_271);
lean_inc(x_225);
x_291 = l_Int_Linear_Poly_mul(x_225, x_290);
lean_dec(x_290);
x_292 = lean_int_mul(x_272, x_214);
lean_dec(x_272);
lean_inc(x_264);
x_293 = l_Int_Linear_Poly_mul(x_264, x_292);
lean_dec(x_292);
x_294 = lean_int_mul(x_214, x_261);
lean_dec(x_261);
lean_dec(x_214);
x_295 = l_Int_Linear_Poly_combine(x_291, x_293);
lean_inc(x_270);
lean_ctor_set(x_259, 2, x_295);
lean_ctor_set(x_259, 1, x_219);
lean_ctor_set(x_259, 0, x_270);
lean_inc(x_258);
lean_inc(x_220);
lean_ctor_set_tag(x_286, 4);
lean_ctor_set(x_286, 1, x_258);
lean_ctor_set(x_286, 0, x_220);
x_296 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_259);
lean_ctor_set(x_296, 2, x_286);
lean_inc(x_213);
lean_inc(x_215);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_221);
lean_inc(x_216);
lean_inc(x_223);
lean_inc(x_224);
x_297 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_296, x_224, x_223, x_216, x_221, x_211, x_212, x_215, x_213, x_288);
if (lean_obj_tag(x_297) == 0)
{
uint8_t x_298; 
x_298 = !lean_is_exclusive(x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_299 = lean_ctor_get(x_297, 1);
x_300 = lean_ctor_get(x_297, 0);
lean_dec(x_300);
x_301 = l_Int_Linear_Poly_mul(x_225, x_263);
lean_dec(x_263);
x_302 = lean_int_neg(x_222);
lean_dec(x_222);
x_303 = l_Int_Linear_Poly_mul(x_264, x_302);
lean_dec(x_302);
x_304 = l_Int_Linear_Poly_combine(x_301, x_303);
lean_inc(x_258);
lean_ctor_set_tag(x_297, 5);
lean_ctor_set(x_297, 1, x_258);
lean_ctor_set(x_297, 0, x_220);
x_305 = !lean_is_exclusive(x_258);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_258, 2);
lean_dec(x_306);
x_307 = lean_ctor_get(x_258, 1);
lean_dec(x_307);
x_308 = lean_ctor_get(x_258, 0);
lean_dec(x_308);
lean_ctor_set(x_258, 2, x_297);
lean_ctor_set(x_258, 1, x_304);
lean_ctor_set(x_258, 0, x_270);
x_1 = x_258;
x_2 = x_224;
x_3 = x_223;
x_4 = x_216;
x_5 = x_221;
x_6 = x_211;
x_7 = x_212;
x_8 = x_215;
x_9 = x_213;
x_10 = x_299;
goto _start;
}
else
{
lean_object* x_310; 
lean_dec(x_258);
x_310 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_310, 0, x_270);
lean_ctor_set(x_310, 1, x_304);
lean_ctor_set(x_310, 2, x_297);
x_1 = x_310;
x_2 = x_224;
x_3 = x_223;
x_4 = x_216;
x_5 = x_221;
x_6 = x_211;
x_7 = x_212;
x_8 = x_215;
x_9 = x_213;
x_10 = x_299;
goto _start;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_312 = lean_ctor_get(x_297, 1);
lean_inc(x_312);
lean_dec(x_297);
x_313 = l_Int_Linear_Poly_mul(x_225, x_263);
lean_dec(x_263);
x_314 = lean_int_neg(x_222);
lean_dec(x_222);
x_315 = l_Int_Linear_Poly_mul(x_264, x_314);
lean_dec(x_314);
x_316 = l_Int_Linear_Poly_combine(x_313, x_315);
lean_inc(x_258);
x_317 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_317, 0, x_220);
lean_ctor_set(x_317, 1, x_258);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 x_318 = x_258;
} else {
 lean_dec_ref(x_258);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(0, 3, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_270);
lean_ctor_set(x_319, 1, x_316);
lean_ctor_set(x_319, 2, x_317);
x_1 = x_319;
x_2 = x_224;
x_3 = x_223;
x_4 = x_216;
x_5 = x_221;
x_6 = x_211;
x_7 = x_212;
x_8 = x_215;
x_9 = x_213;
x_10 = x_312;
goto _start;
}
}
else
{
lean_dec(x_270);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_258);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
return x_297;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_321 = lean_ctor_get(x_286, 1);
lean_inc(x_321);
lean_dec(x_286);
x_322 = lean_int_mul(x_271, x_261);
lean_dec(x_271);
lean_inc(x_225);
x_323 = l_Int_Linear_Poly_mul(x_225, x_322);
lean_dec(x_322);
x_324 = lean_int_mul(x_272, x_214);
lean_dec(x_272);
lean_inc(x_264);
x_325 = l_Int_Linear_Poly_mul(x_264, x_324);
lean_dec(x_324);
x_326 = lean_int_mul(x_214, x_261);
lean_dec(x_261);
lean_dec(x_214);
x_327 = l_Int_Linear_Poly_combine(x_323, x_325);
lean_inc(x_270);
lean_ctor_set(x_259, 2, x_327);
lean_ctor_set(x_259, 1, x_219);
lean_ctor_set(x_259, 0, x_270);
lean_inc(x_258);
lean_inc(x_220);
x_328 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_328, 0, x_220);
lean_ctor_set(x_328, 1, x_258);
x_329 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_259);
lean_ctor_set(x_329, 2, x_328);
lean_inc(x_213);
lean_inc(x_215);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_221);
lean_inc(x_216);
lean_inc(x_223);
lean_inc(x_224);
x_330 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_329, x_224, x_223, x_216, x_221, x_211, x_212, x_215, x_213, x_321);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_332 = x_330;
} else {
 lean_dec_ref(x_330);
 x_332 = lean_box(0);
}
x_333 = l_Int_Linear_Poly_mul(x_225, x_263);
lean_dec(x_263);
x_334 = lean_int_neg(x_222);
lean_dec(x_222);
x_335 = l_Int_Linear_Poly_mul(x_264, x_334);
lean_dec(x_334);
x_336 = l_Int_Linear_Poly_combine(x_333, x_335);
lean_inc(x_258);
if (lean_is_scalar(x_332)) {
 x_337 = lean_alloc_ctor(5, 2, 0);
} else {
 x_337 = x_332;
 lean_ctor_set_tag(x_337, 5);
}
lean_ctor_set(x_337, 0, x_220);
lean_ctor_set(x_337, 1, x_258);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 x_338 = x_258;
} else {
 lean_dec_ref(x_258);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(0, 3, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_270);
lean_ctor_set(x_339, 1, x_336);
lean_ctor_set(x_339, 2, x_337);
x_1 = x_339;
x_2 = x_224;
x_3 = x_223;
x_4 = x_216;
x_5 = x_221;
x_6 = x_211;
x_7 = x_212;
x_8 = x_215;
x_9 = x_213;
x_10 = x_331;
goto _start;
}
else
{
lean_dec(x_270);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_258);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
return x_330;
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_341 = lean_ctor_get(x_276, 0);
x_342 = lean_ctor_get(x_276, 1);
x_343 = lean_ctor_get(x_276, 2);
x_344 = lean_ctor_get(x_276, 3);
x_345 = lean_ctor_get(x_276, 4);
x_346 = lean_ctor_get(x_276, 5);
x_347 = lean_ctor_get(x_276, 6);
x_348 = lean_ctor_get(x_276, 7);
x_349 = lean_ctor_get(x_276, 8);
x_350 = lean_ctor_get(x_276, 9);
x_351 = lean_ctor_get(x_276, 10);
x_352 = lean_ctor_get(x_276, 11);
x_353 = lean_ctor_get(x_276, 12);
x_354 = lean_ctor_get(x_276, 13);
x_355 = lean_ctor_get(x_276, 14);
x_356 = lean_ctor_get(x_276, 15);
x_357 = lean_ctor_get_uint8(x_276, sizeof(void*)*22);
x_358 = lean_ctor_get(x_276, 16);
x_359 = lean_ctor_get(x_276, 17);
x_360 = lean_ctor_get(x_276, 18);
x_361 = lean_ctor_get(x_276, 19);
x_362 = lean_ctor_get(x_276, 20);
x_363 = lean_ctor_get(x_276, 21);
x_364 = lean_ctor_get_uint8(x_276, sizeof(void*)*22 + 1);
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
lean_inc(x_341);
lean_dec(x_276);
x_365 = lean_box(0);
x_366 = l_Lean_PersistentArray_set___redArg(x_348, x_219, x_365);
x_367 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_367, 0, x_341);
lean_ctor_set(x_367, 1, x_342);
lean_ctor_set(x_367, 2, x_343);
lean_ctor_set(x_367, 3, x_344);
lean_ctor_set(x_367, 4, x_345);
lean_ctor_set(x_367, 5, x_346);
lean_ctor_set(x_367, 6, x_347);
lean_ctor_set(x_367, 7, x_366);
lean_ctor_set(x_367, 8, x_349);
lean_ctor_set(x_367, 9, x_350);
lean_ctor_set(x_367, 10, x_351);
lean_ctor_set(x_367, 11, x_352);
lean_ctor_set(x_367, 12, x_353);
lean_ctor_set(x_367, 13, x_354);
lean_ctor_set(x_367, 14, x_355);
lean_ctor_set(x_367, 15, x_356);
lean_ctor_set(x_367, 16, x_358);
lean_ctor_set(x_367, 17, x_359);
lean_ctor_set(x_367, 18, x_360);
lean_ctor_set(x_367, 19, x_361);
lean_ctor_set(x_367, 20, x_362);
lean_ctor_set(x_367, 21, x_363);
lean_ctor_set_uint8(x_367, sizeof(void*)*22, x_357);
lean_ctor_set_uint8(x_367, sizeof(void*)*22 + 1, x_364);
lean_ctor_set(x_275, 1, x_367);
x_368 = lean_st_ref_set(x_224, x_274, x_277);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_370 = x_368;
} else {
 lean_dec_ref(x_368);
 x_370 = lean_box(0);
}
x_371 = lean_int_mul(x_271, x_261);
lean_dec(x_271);
lean_inc(x_225);
x_372 = l_Int_Linear_Poly_mul(x_225, x_371);
lean_dec(x_371);
x_373 = lean_int_mul(x_272, x_214);
lean_dec(x_272);
lean_inc(x_264);
x_374 = l_Int_Linear_Poly_mul(x_264, x_373);
lean_dec(x_373);
x_375 = lean_int_mul(x_214, x_261);
lean_dec(x_261);
lean_dec(x_214);
x_376 = l_Int_Linear_Poly_combine(x_372, x_374);
lean_inc(x_270);
lean_ctor_set(x_259, 2, x_376);
lean_ctor_set(x_259, 1, x_219);
lean_ctor_set(x_259, 0, x_270);
lean_inc(x_258);
lean_inc(x_220);
if (lean_is_scalar(x_370)) {
 x_377 = lean_alloc_ctor(4, 2, 0);
} else {
 x_377 = x_370;
 lean_ctor_set_tag(x_377, 4);
}
lean_ctor_set(x_377, 0, x_220);
lean_ctor_set(x_377, 1, x_258);
x_378 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_378, 0, x_375);
lean_ctor_set(x_378, 1, x_259);
lean_ctor_set(x_378, 2, x_377);
lean_inc(x_213);
lean_inc(x_215);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_221);
lean_inc(x_216);
lean_inc(x_223);
lean_inc(x_224);
x_379 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_378, x_224, x_223, x_216, x_221, x_211, x_212, x_215, x_213, x_369);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_380 = lean_ctor_get(x_379, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_381 = x_379;
} else {
 lean_dec_ref(x_379);
 x_381 = lean_box(0);
}
x_382 = l_Int_Linear_Poly_mul(x_225, x_263);
lean_dec(x_263);
x_383 = lean_int_neg(x_222);
lean_dec(x_222);
x_384 = l_Int_Linear_Poly_mul(x_264, x_383);
lean_dec(x_383);
x_385 = l_Int_Linear_Poly_combine(x_382, x_384);
lean_inc(x_258);
if (lean_is_scalar(x_381)) {
 x_386 = lean_alloc_ctor(5, 2, 0);
} else {
 x_386 = x_381;
 lean_ctor_set_tag(x_386, 5);
}
lean_ctor_set(x_386, 0, x_220);
lean_ctor_set(x_386, 1, x_258);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 x_387 = x_258;
} else {
 lean_dec_ref(x_258);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(0, 3, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_270);
lean_ctor_set(x_388, 1, x_385);
lean_ctor_set(x_388, 2, x_386);
x_1 = x_388;
x_2 = x_224;
x_3 = x_223;
x_4 = x_216;
x_5 = x_221;
x_6 = x_211;
x_7 = x_212;
x_8 = x_215;
x_9 = x_213;
x_10 = x_380;
goto _start;
}
else
{
lean_dec(x_270);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_258);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
return x_379;
}
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_390 = lean_ctor_get(x_275, 0);
x_391 = lean_ctor_get(x_275, 2);
x_392 = lean_ctor_get(x_275, 3);
lean_inc(x_392);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_275);
x_393 = lean_ctor_get(x_276, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_276, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_276, 2);
lean_inc(x_395);
x_396 = lean_ctor_get(x_276, 3);
lean_inc(x_396);
x_397 = lean_ctor_get(x_276, 4);
lean_inc(x_397);
x_398 = lean_ctor_get(x_276, 5);
lean_inc(x_398);
x_399 = lean_ctor_get(x_276, 6);
lean_inc(x_399);
x_400 = lean_ctor_get(x_276, 7);
lean_inc(x_400);
x_401 = lean_ctor_get(x_276, 8);
lean_inc(x_401);
x_402 = lean_ctor_get(x_276, 9);
lean_inc(x_402);
x_403 = lean_ctor_get(x_276, 10);
lean_inc(x_403);
x_404 = lean_ctor_get(x_276, 11);
lean_inc(x_404);
x_405 = lean_ctor_get(x_276, 12);
lean_inc(x_405);
x_406 = lean_ctor_get(x_276, 13);
lean_inc(x_406);
x_407 = lean_ctor_get(x_276, 14);
lean_inc(x_407);
x_408 = lean_ctor_get(x_276, 15);
lean_inc(x_408);
x_409 = lean_ctor_get_uint8(x_276, sizeof(void*)*22);
x_410 = lean_ctor_get(x_276, 16);
lean_inc(x_410);
x_411 = lean_ctor_get(x_276, 17);
lean_inc(x_411);
x_412 = lean_ctor_get(x_276, 18);
lean_inc(x_412);
x_413 = lean_ctor_get(x_276, 19);
lean_inc(x_413);
x_414 = lean_ctor_get(x_276, 20);
lean_inc(x_414);
x_415 = lean_ctor_get(x_276, 21);
lean_inc(x_415);
x_416 = lean_ctor_get_uint8(x_276, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 lean_ctor_release(x_276, 2);
 lean_ctor_release(x_276, 3);
 lean_ctor_release(x_276, 4);
 lean_ctor_release(x_276, 5);
 lean_ctor_release(x_276, 6);
 lean_ctor_release(x_276, 7);
 lean_ctor_release(x_276, 8);
 lean_ctor_release(x_276, 9);
 lean_ctor_release(x_276, 10);
 lean_ctor_release(x_276, 11);
 lean_ctor_release(x_276, 12);
 lean_ctor_release(x_276, 13);
 lean_ctor_release(x_276, 14);
 lean_ctor_release(x_276, 15);
 lean_ctor_release(x_276, 16);
 lean_ctor_release(x_276, 17);
 lean_ctor_release(x_276, 18);
 lean_ctor_release(x_276, 19);
 lean_ctor_release(x_276, 20);
 lean_ctor_release(x_276, 21);
 x_417 = x_276;
} else {
 lean_dec_ref(x_276);
 x_417 = lean_box(0);
}
x_418 = lean_box(0);
x_419 = l_Lean_PersistentArray_set___redArg(x_400, x_219, x_418);
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
lean_ctor_set(x_420, 6, x_399);
lean_ctor_set(x_420, 7, x_419);
lean_ctor_set(x_420, 8, x_401);
lean_ctor_set(x_420, 9, x_402);
lean_ctor_set(x_420, 10, x_403);
lean_ctor_set(x_420, 11, x_404);
lean_ctor_set(x_420, 12, x_405);
lean_ctor_set(x_420, 13, x_406);
lean_ctor_set(x_420, 14, x_407);
lean_ctor_set(x_420, 15, x_408);
lean_ctor_set(x_420, 16, x_410);
lean_ctor_set(x_420, 17, x_411);
lean_ctor_set(x_420, 18, x_412);
lean_ctor_set(x_420, 19, x_413);
lean_ctor_set(x_420, 20, x_414);
lean_ctor_set(x_420, 21, x_415);
lean_ctor_set_uint8(x_420, sizeof(void*)*22, x_409);
lean_ctor_set_uint8(x_420, sizeof(void*)*22 + 1, x_416);
x_421 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_421, 0, x_390);
lean_ctor_set(x_421, 1, x_420);
lean_ctor_set(x_421, 2, x_391);
lean_ctor_set(x_421, 3, x_392);
lean_ctor_set(x_274, 14, x_421);
x_422 = lean_st_ref_set(x_224, x_274, x_277);
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
x_425 = lean_int_mul(x_271, x_261);
lean_dec(x_271);
lean_inc(x_225);
x_426 = l_Int_Linear_Poly_mul(x_225, x_425);
lean_dec(x_425);
x_427 = lean_int_mul(x_272, x_214);
lean_dec(x_272);
lean_inc(x_264);
x_428 = l_Int_Linear_Poly_mul(x_264, x_427);
lean_dec(x_427);
x_429 = lean_int_mul(x_214, x_261);
lean_dec(x_261);
lean_dec(x_214);
x_430 = l_Int_Linear_Poly_combine(x_426, x_428);
lean_inc(x_270);
lean_ctor_set(x_259, 2, x_430);
lean_ctor_set(x_259, 1, x_219);
lean_ctor_set(x_259, 0, x_270);
lean_inc(x_258);
lean_inc(x_220);
if (lean_is_scalar(x_424)) {
 x_431 = lean_alloc_ctor(4, 2, 0);
} else {
 x_431 = x_424;
 lean_ctor_set_tag(x_431, 4);
}
lean_ctor_set(x_431, 0, x_220);
lean_ctor_set(x_431, 1, x_258);
x_432 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_432, 0, x_429);
lean_ctor_set(x_432, 1, x_259);
lean_ctor_set(x_432, 2, x_431);
lean_inc(x_213);
lean_inc(x_215);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_221);
lean_inc(x_216);
lean_inc(x_223);
lean_inc(x_224);
x_433 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_432, x_224, x_223, x_216, x_221, x_211, x_212, x_215, x_213, x_423);
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
x_436 = l_Int_Linear_Poly_mul(x_225, x_263);
lean_dec(x_263);
x_437 = lean_int_neg(x_222);
lean_dec(x_222);
x_438 = l_Int_Linear_Poly_mul(x_264, x_437);
lean_dec(x_437);
x_439 = l_Int_Linear_Poly_combine(x_436, x_438);
lean_inc(x_258);
if (lean_is_scalar(x_435)) {
 x_440 = lean_alloc_ctor(5, 2, 0);
} else {
 x_440 = x_435;
 lean_ctor_set_tag(x_440, 5);
}
lean_ctor_set(x_440, 0, x_220);
lean_ctor_set(x_440, 1, x_258);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 x_441 = x_258;
} else {
 lean_dec_ref(x_258);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(0, 3, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_270);
lean_ctor_set(x_442, 1, x_439);
lean_ctor_set(x_442, 2, x_440);
x_1 = x_442;
x_2 = x_224;
x_3 = x_223;
x_4 = x_216;
x_5 = x_221;
x_6 = x_211;
x_7 = x_212;
x_8 = x_215;
x_9 = x_213;
x_10 = x_434;
goto _start;
}
else
{
lean_dec(x_270);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_258);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
return x_433;
}
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_444 = lean_ctor_get(x_274, 0);
x_445 = lean_ctor_get(x_274, 1);
x_446 = lean_ctor_get(x_274, 2);
x_447 = lean_ctor_get(x_274, 3);
x_448 = lean_ctor_get(x_274, 4);
x_449 = lean_ctor_get(x_274, 5);
x_450 = lean_ctor_get(x_274, 6);
x_451 = lean_ctor_get(x_274, 7);
x_452 = lean_ctor_get_uint8(x_274, sizeof(void*)*16);
x_453 = lean_ctor_get(x_274, 8);
x_454 = lean_ctor_get(x_274, 9);
x_455 = lean_ctor_get(x_274, 10);
x_456 = lean_ctor_get(x_274, 11);
x_457 = lean_ctor_get(x_274, 12);
x_458 = lean_ctor_get(x_274, 13);
x_459 = lean_ctor_get(x_274, 15);
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
lean_dec(x_274);
x_460 = lean_ctor_get(x_275, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_275, 2);
lean_inc(x_461);
x_462 = lean_ctor_get(x_275, 3);
lean_inc(x_462);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 lean_ctor_release(x_275, 2);
 lean_ctor_release(x_275, 3);
 x_463 = x_275;
} else {
 lean_dec_ref(x_275);
 x_463 = lean_box(0);
}
x_464 = lean_ctor_get(x_276, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_276, 1);
lean_inc(x_465);
x_466 = lean_ctor_get(x_276, 2);
lean_inc(x_466);
x_467 = lean_ctor_get(x_276, 3);
lean_inc(x_467);
x_468 = lean_ctor_get(x_276, 4);
lean_inc(x_468);
x_469 = lean_ctor_get(x_276, 5);
lean_inc(x_469);
x_470 = lean_ctor_get(x_276, 6);
lean_inc(x_470);
x_471 = lean_ctor_get(x_276, 7);
lean_inc(x_471);
x_472 = lean_ctor_get(x_276, 8);
lean_inc(x_472);
x_473 = lean_ctor_get(x_276, 9);
lean_inc(x_473);
x_474 = lean_ctor_get(x_276, 10);
lean_inc(x_474);
x_475 = lean_ctor_get(x_276, 11);
lean_inc(x_475);
x_476 = lean_ctor_get(x_276, 12);
lean_inc(x_476);
x_477 = lean_ctor_get(x_276, 13);
lean_inc(x_477);
x_478 = lean_ctor_get(x_276, 14);
lean_inc(x_478);
x_479 = lean_ctor_get(x_276, 15);
lean_inc(x_479);
x_480 = lean_ctor_get_uint8(x_276, sizeof(void*)*22);
x_481 = lean_ctor_get(x_276, 16);
lean_inc(x_481);
x_482 = lean_ctor_get(x_276, 17);
lean_inc(x_482);
x_483 = lean_ctor_get(x_276, 18);
lean_inc(x_483);
x_484 = lean_ctor_get(x_276, 19);
lean_inc(x_484);
x_485 = lean_ctor_get(x_276, 20);
lean_inc(x_485);
x_486 = lean_ctor_get(x_276, 21);
lean_inc(x_486);
x_487 = lean_ctor_get_uint8(x_276, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 lean_ctor_release(x_276, 2);
 lean_ctor_release(x_276, 3);
 lean_ctor_release(x_276, 4);
 lean_ctor_release(x_276, 5);
 lean_ctor_release(x_276, 6);
 lean_ctor_release(x_276, 7);
 lean_ctor_release(x_276, 8);
 lean_ctor_release(x_276, 9);
 lean_ctor_release(x_276, 10);
 lean_ctor_release(x_276, 11);
 lean_ctor_release(x_276, 12);
 lean_ctor_release(x_276, 13);
 lean_ctor_release(x_276, 14);
 lean_ctor_release(x_276, 15);
 lean_ctor_release(x_276, 16);
 lean_ctor_release(x_276, 17);
 lean_ctor_release(x_276, 18);
 lean_ctor_release(x_276, 19);
 lean_ctor_release(x_276, 20);
 lean_ctor_release(x_276, 21);
 x_488 = x_276;
} else {
 lean_dec_ref(x_276);
 x_488 = lean_box(0);
}
x_489 = lean_box(0);
x_490 = l_Lean_PersistentArray_set___redArg(x_471, x_219, x_489);
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
lean_ctor_set(x_491, 6, x_470);
lean_ctor_set(x_491, 7, x_490);
lean_ctor_set(x_491, 8, x_472);
lean_ctor_set(x_491, 9, x_473);
lean_ctor_set(x_491, 10, x_474);
lean_ctor_set(x_491, 11, x_475);
lean_ctor_set(x_491, 12, x_476);
lean_ctor_set(x_491, 13, x_477);
lean_ctor_set(x_491, 14, x_478);
lean_ctor_set(x_491, 15, x_479);
lean_ctor_set(x_491, 16, x_481);
lean_ctor_set(x_491, 17, x_482);
lean_ctor_set(x_491, 18, x_483);
lean_ctor_set(x_491, 19, x_484);
lean_ctor_set(x_491, 20, x_485);
lean_ctor_set(x_491, 21, x_486);
lean_ctor_set_uint8(x_491, sizeof(void*)*22, x_480);
lean_ctor_set_uint8(x_491, sizeof(void*)*22 + 1, x_487);
if (lean_is_scalar(x_463)) {
 x_492 = lean_alloc_ctor(0, 4, 0);
} else {
 x_492 = x_463;
}
lean_ctor_set(x_492, 0, x_460);
lean_ctor_set(x_492, 1, x_491);
lean_ctor_set(x_492, 2, x_461);
lean_ctor_set(x_492, 3, x_462);
x_493 = lean_alloc_ctor(0, 16, 1);
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
lean_ctor_set_uint8(x_493, sizeof(void*)*16, x_452);
x_494 = lean_st_ref_set(x_224, x_493, x_277);
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
x_497 = lean_int_mul(x_271, x_261);
lean_dec(x_271);
lean_inc(x_225);
x_498 = l_Int_Linear_Poly_mul(x_225, x_497);
lean_dec(x_497);
x_499 = lean_int_mul(x_272, x_214);
lean_dec(x_272);
lean_inc(x_264);
x_500 = l_Int_Linear_Poly_mul(x_264, x_499);
lean_dec(x_499);
x_501 = lean_int_mul(x_214, x_261);
lean_dec(x_261);
lean_dec(x_214);
x_502 = l_Int_Linear_Poly_combine(x_498, x_500);
lean_inc(x_270);
lean_ctor_set(x_259, 2, x_502);
lean_ctor_set(x_259, 1, x_219);
lean_ctor_set(x_259, 0, x_270);
lean_inc(x_258);
lean_inc(x_220);
if (lean_is_scalar(x_496)) {
 x_503 = lean_alloc_ctor(4, 2, 0);
} else {
 x_503 = x_496;
 lean_ctor_set_tag(x_503, 4);
}
lean_ctor_set(x_503, 0, x_220);
lean_ctor_set(x_503, 1, x_258);
x_504 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_259);
lean_ctor_set(x_504, 2, x_503);
lean_inc(x_213);
lean_inc(x_215);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_221);
lean_inc(x_216);
lean_inc(x_223);
lean_inc(x_224);
x_505 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_504, x_224, x_223, x_216, x_221, x_211, x_212, x_215, x_213, x_495);
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
x_508 = l_Int_Linear_Poly_mul(x_225, x_263);
lean_dec(x_263);
x_509 = lean_int_neg(x_222);
lean_dec(x_222);
x_510 = l_Int_Linear_Poly_mul(x_264, x_509);
lean_dec(x_509);
x_511 = l_Int_Linear_Poly_combine(x_508, x_510);
lean_inc(x_258);
if (lean_is_scalar(x_507)) {
 x_512 = lean_alloc_ctor(5, 2, 0);
} else {
 x_512 = x_507;
 lean_ctor_set_tag(x_512, 5);
}
lean_ctor_set(x_512, 0, x_220);
lean_ctor_set(x_512, 1, x_258);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 x_513 = x_258;
} else {
 lean_dec_ref(x_258);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(0, 3, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_270);
lean_ctor_set(x_514, 1, x_511);
lean_ctor_set(x_514, 2, x_512);
x_1 = x_514;
x_2 = x_224;
x_3 = x_223;
x_4 = x_216;
x_5 = x_221;
x_6 = x_211;
x_7 = x_212;
x_8 = x_215;
x_9 = x_213;
x_10 = x_506;
goto _start;
}
else
{
lean_dec(x_270);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_258);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
return x_505;
}
}
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; uint8_t x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; uint8_t x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_516 = lean_ctor_get(x_259, 0);
x_517 = lean_ctor_get(x_259, 2);
lean_inc(x_517);
lean_inc(x_516);
lean_dec(x_259);
x_518 = lean_int_mul(x_222, x_261);
x_519 = lean_int_mul(x_516, x_214);
x_520 = l_Lean_Meta_Grind_Arith_gcdExt(x_518, x_519);
lean_dec(x_519);
lean_dec(x_518);
x_521 = lean_ctor_get(x_520, 1);
lean_inc(x_521);
x_522 = lean_ctor_get(x_520, 0);
lean_inc(x_522);
lean_dec(x_520);
x_523 = lean_ctor_get(x_521, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_521, 1);
lean_inc(x_524);
lean_dec(x_521);
x_525 = lean_st_ref_take(x_224, x_217);
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_526, 14);
lean_inc(x_527);
x_528 = lean_ctor_get(x_527, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_525, 1);
lean_inc(x_529);
lean_dec(x_525);
x_530 = lean_ctor_get(x_526, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_526, 1);
lean_inc(x_531);
x_532 = lean_ctor_get(x_526, 2);
lean_inc(x_532);
x_533 = lean_ctor_get(x_526, 3);
lean_inc(x_533);
x_534 = lean_ctor_get(x_526, 4);
lean_inc(x_534);
x_535 = lean_ctor_get(x_526, 5);
lean_inc(x_535);
x_536 = lean_ctor_get(x_526, 6);
lean_inc(x_536);
x_537 = lean_ctor_get(x_526, 7);
lean_inc(x_537);
x_538 = lean_ctor_get_uint8(x_526, sizeof(void*)*16);
x_539 = lean_ctor_get(x_526, 8);
lean_inc(x_539);
x_540 = lean_ctor_get(x_526, 9);
lean_inc(x_540);
x_541 = lean_ctor_get(x_526, 10);
lean_inc(x_541);
x_542 = lean_ctor_get(x_526, 11);
lean_inc(x_542);
x_543 = lean_ctor_get(x_526, 12);
lean_inc(x_543);
x_544 = lean_ctor_get(x_526, 13);
lean_inc(x_544);
x_545 = lean_ctor_get(x_526, 15);
lean_inc(x_545);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 lean_ctor_release(x_526, 2);
 lean_ctor_release(x_526, 3);
 lean_ctor_release(x_526, 4);
 lean_ctor_release(x_526, 5);
 lean_ctor_release(x_526, 6);
 lean_ctor_release(x_526, 7);
 lean_ctor_release(x_526, 8);
 lean_ctor_release(x_526, 9);
 lean_ctor_release(x_526, 10);
 lean_ctor_release(x_526, 11);
 lean_ctor_release(x_526, 12);
 lean_ctor_release(x_526, 13);
 lean_ctor_release(x_526, 14);
 lean_ctor_release(x_526, 15);
 x_546 = x_526;
} else {
 lean_dec_ref(x_526);
 x_546 = lean_box(0);
}
x_547 = lean_ctor_get(x_527, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_527, 2);
lean_inc(x_548);
x_549 = lean_ctor_get(x_527, 3);
lean_inc(x_549);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 lean_ctor_release(x_527, 2);
 lean_ctor_release(x_527, 3);
 x_550 = x_527;
} else {
 lean_dec_ref(x_527);
 x_550 = lean_box(0);
}
x_551 = lean_ctor_get(x_528, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_528, 1);
lean_inc(x_552);
x_553 = lean_ctor_get(x_528, 2);
lean_inc(x_553);
x_554 = lean_ctor_get(x_528, 3);
lean_inc(x_554);
x_555 = lean_ctor_get(x_528, 4);
lean_inc(x_555);
x_556 = lean_ctor_get(x_528, 5);
lean_inc(x_556);
x_557 = lean_ctor_get(x_528, 6);
lean_inc(x_557);
x_558 = lean_ctor_get(x_528, 7);
lean_inc(x_558);
x_559 = lean_ctor_get(x_528, 8);
lean_inc(x_559);
x_560 = lean_ctor_get(x_528, 9);
lean_inc(x_560);
x_561 = lean_ctor_get(x_528, 10);
lean_inc(x_561);
x_562 = lean_ctor_get(x_528, 11);
lean_inc(x_562);
x_563 = lean_ctor_get(x_528, 12);
lean_inc(x_563);
x_564 = lean_ctor_get(x_528, 13);
lean_inc(x_564);
x_565 = lean_ctor_get(x_528, 14);
lean_inc(x_565);
x_566 = lean_ctor_get(x_528, 15);
lean_inc(x_566);
x_567 = lean_ctor_get_uint8(x_528, sizeof(void*)*22);
x_568 = lean_ctor_get(x_528, 16);
lean_inc(x_568);
x_569 = lean_ctor_get(x_528, 17);
lean_inc(x_569);
x_570 = lean_ctor_get(x_528, 18);
lean_inc(x_570);
x_571 = lean_ctor_get(x_528, 19);
lean_inc(x_571);
x_572 = lean_ctor_get(x_528, 20);
lean_inc(x_572);
x_573 = lean_ctor_get(x_528, 21);
lean_inc(x_573);
x_574 = lean_ctor_get_uint8(x_528, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 lean_ctor_release(x_528, 2);
 lean_ctor_release(x_528, 3);
 lean_ctor_release(x_528, 4);
 lean_ctor_release(x_528, 5);
 lean_ctor_release(x_528, 6);
 lean_ctor_release(x_528, 7);
 lean_ctor_release(x_528, 8);
 lean_ctor_release(x_528, 9);
 lean_ctor_release(x_528, 10);
 lean_ctor_release(x_528, 11);
 lean_ctor_release(x_528, 12);
 lean_ctor_release(x_528, 13);
 lean_ctor_release(x_528, 14);
 lean_ctor_release(x_528, 15);
 lean_ctor_release(x_528, 16);
 lean_ctor_release(x_528, 17);
 lean_ctor_release(x_528, 18);
 lean_ctor_release(x_528, 19);
 lean_ctor_release(x_528, 20);
 lean_ctor_release(x_528, 21);
 x_575 = x_528;
} else {
 lean_dec_ref(x_528);
 x_575 = lean_box(0);
}
x_576 = lean_box(0);
x_577 = l_Lean_PersistentArray_set___redArg(x_558, x_219, x_576);
if (lean_is_scalar(x_575)) {
 x_578 = lean_alloc_ctor(0, 22, 2);
} else {
 x_578 = x_575;
}
lean_ctor_set(x_578, 0, x_551);
lean_ctor_set(x_578, 1, x_552);
lean_ctor_set(x_578, 2, x_553);
lean_ctor_set(x_578, 3, x_554);
lean_ctor_set(x_578, 4, x_555);
lean_ctor_set(x_578, 5, x_556);
lean_ctor_set(x_578, 6, x_557);
lean_ctor_set(x_578, 7, x_577);
lean_ctor_set(x_578, 8, x_559);
lean_ctor_set(x_578, 9, x_560);
lean_ctor_set(x_578, 10, x_561);
lean_ctor_set(x_578, 11, x_562);
lean_ctor_set(x_578, 12, x_563);
lean_ctor_set(x_578, 13, x_564);
lean_ctor_set(x_578, 14, x_565);
lean_ctor_set(x_578, 15, x_566);
lean_ctor_set(x_578, 16, x_568);
lean_ctor_set(x_578, 17, x_569);
lean_ctor_set(x_578, 18, x_570);
lean_ctor_set(x_578, 19, x_571);
lean_ctor_set(x_578, 20, x_572);
lean_ctor_set(x_578, 21, x_573);
lean_ctor_set_uint8(x_578, sizeof(void*)*22, x_567);
lean_ctor_set_uint8(x_578, sizeof(void*)*22 + 1, x_574);
if (lean_is_scalar(x_550)) {
 x_579 = lean_alloc_ctor(0, 4, 0);
} else {
 x_579 = x_550;
}
lean_ctor_set(x_579, 0, x_547);
lean_ctor_set(x_579, 1, x_578);
lean_ctor_set(x_579, 2, x_548);
lean_ctor_set(x_579, 3, x_549);
if (lean_is_scalar(x_546)) {
 x_580 = lean_alloc_ctor(0, 16, 1);
} else {
 x_580 = x_546;
}
lean_ctor_set(x_580, 0, x_530);
lean_ctor_set(x_580, 1, x_531);
lean_ctor_set(x_580, 2, x_532);
lean_ctor_set(x_580, 3, x_533);
lean_ctor_set(x_580, 4, x_534);
lean_ctor_set(x_580, 5, x_535);
lean_ctor_set(x_580, 6, x_536);
lean_ctor_set(x_580, 7, x_537);
lean_ctor_set(x_580, 8, x_539);
lean_ctor_set(x_580, 9, x_540);
lean_ctor_set(x_580, 10, x_541);
lean_ctor_set(x_580, 11, x_542);
lean_ctor_set(x_580, 12, x_543);
lean_ctor_set(x_580, 13, x_544);
lean_ctor_set(x_580, 14, x_579);
lean_ctor_set(x_580, 15, x_545);
lean_ctor_set_uint8(x_580, sizeof(void*)*16, x_538);
x_581 = lean_st_ref_set(x_224, x_580, x_529);
x_582 = lean_ctor_get(x_581, 1);
lean_inc(x_582);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 lean_ctor_release(x_581, 1);
 x_583 = x_581;
} else {
 lean_dec_ref(x_581);
 x_583 = lean_box(0);
}
x_584 = lean_int_mul(x_523, x_261);
lean_dec(x_523);
lean_inc(x_225);
x_585 = l_Int_Linear_Poly_mul(x_225, x_584);
lean_dec(x_584);
x_586 = lean_int_mul(x_524, x_214);
lean_dec(x_524);
lean_inc(x_517);
x_587 = l_Int_Linear_Poly_mul(x_517, x_586);
lean_dec(x_586);
x_588 = lean_int_mul(x_214, x_261);
lean_dec(x_261);
lean_dec(x_214);
x_589 = l_Int_Linear_Poly_combine(x_585, x_587);
lean_inc(x_522);
x_590 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_590, 0, x_522);
lean_ctor_set(x_590, 1, x_219);
lean_ctor_set(x_590, 2, x_589);
lean_inc(x_258);
lean_inc(x_220);
if (lean_is_scalar(x_583)) {
 x_591 = lean_alloc_ctor(4, 2, 0);
} else {
 x_591 = x_583;
 lean_ctor_set_tag(x_591, 4);
}
lean_ctor_set(x_591, 0, x_220);
lean_ctor_set(x_591, 1, x_258);
x_592 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_592, 0, x_588);
lean_ctor_set(x_592, 1, x_590);
lean_ctor_set(x_592, 2, x_591);
lean_inc(x_213);
lean_inc(x_215);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_221);
lean_inc(x_216);
lean_inc(x_223);
lean_inc(x_224);
x_593 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_592, x_224, x_223, x_216, x_221, x_211, x_212, x_215, x_213, x_582);
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_594 = lean_ctor_get(x_593, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_595 = x_593;
} else {
 lean_dec_ref(x_593);
 x_595 = lean_box(0);
}
x_596 = l_Int_Linear_Poly_mul(x_225, x_516);
lean_dec(x_516);
x_597 = lean_int_neg(x_222);
lean_dec(x_222);
x_598 = l_Int_Linear_Poly_mul(x_517, x_597);
lean_dec(x_597);
x_599 = l_Int_Linear_Poly_combine(x_596, x_598);
lean_inc(x_258);
if (lean_is_scalar(x_595)) {
 x_600 = lean_alloc_ctor(5, 2, 0);
} else {
 x_600 = x_595;
 lean_ctor_set_tag(x_600, 5);
}
lean_ctor_set(x_600, 0, x_220);
lean_ctor_set(x_600, 1, x_258);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 x_601 = x_258;
} else {
 lean_dec_ref(x_258);
 x_601 = lean_box(0);
}
if (lean_is_scalar(x_601)) {
 x_602 = lean_alloc_ctor(0, 3, 0);
} else {
 x_602 = x_601;
}
lean_ctor_set(x_602, 0, x_522);
lean_ctor_set(x_602, 1, x_599);
lean_ctor_set(x_602, 2, x_600);
x_1 = x_602;
x_2 = x_224;
x_3 = x_223;
x_4 = x_216;
x_5 = x_221;
x_6 = x_211;
x_7 = x_212;
x_8 = x_215;
x_9 = x_213;
x_10 = x_594;
goto _start;
}
else
{
lean_dec(x_522);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_258);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
return x_593;
}
}
}
}
}
}
else
{
uint8_t x_848; 
lean_free_object(x_8);
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
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_848 = !lean_is_exclusive(x_205);
if (x_848 == 0)
{
lean_object* x_849; lean_object* x_850; 
x_849 = lean_ctor_get(x_205, 0);
lean_dec(x_849);
x_850 = lean_box(0);
lean_ctor_set(x_205, 0, x_850);
return x_205;
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; 
x_851 = lean_ctor_get(x_205, 1);
lean_inc(x_851);
lean_dec(x_205);
x_852 = lean_box(0);
x_853 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_853, 0, x_852);
lean_ctor_set(x_853, 1, x_851);
return x_853;
}
}
}
else
{
lean_object* x_854; 
lean_free_object(x_8);
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
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_854 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_196, x_10);
return x_854;
}
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; uint8_t x_866; lean_object* x_867; uint8_t x_868; lean_object* x_869; uint8_t x_870; 
x_855 = lean_ctor_get(x_8, 0);
x_856 = lean_ctor_get(x_8, 1);
x_857 = lean_ctor_get(x_8, 2);
x_858 = lean_ctor_get(x_8, 3);
x_859 = lean_ctor_get(x_8, 4);
x_860 = lean_ctor_get(x_8, 5);
x_861 = lean_ctor_get(x_8, 6);
x_862 = lean_ctor_get(x_8, 7);
x_863 = lean_ctor_get(x_8, 8);
x_864 = lean_ctor_get(x_8, 9);
x_865 = lean_ctor_get(x_8, 10);
x_866 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_867 = lean_ctor_get(x_8, 11);
x_868 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_869 = lean_ctor_get(x_8, 12);
lean_inc(x_869);
lean_inc(x_867);
lean_inc(x_865);
lean_inc(x_864);
lean_inc(x_863);
lean_inc(x_862);
lean_inc(x_861);
lean_inc(x_860);
lean_inc(x_859);
lean_inc(x_858);
lean_inc(x_857);
lean_inc(x_856);
lean_inc(x_855);
lean_dec(x_8);
x_870 = lean_nat_dec_eq(x_858, x_859);
if (x_870 == 0)
{
lean_object* x_871; lean_object* x_872; uint8_t x_873; 
x_871 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_872 = lean_ctor_get(x_871, 0);
lean_inc(x_872);
x_873 = lean_unbox(x_872);
lean_dec(x_872);
if (x_873 == 0)
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; uint8_t x_1100; 
x_874 = lean_ctor_get(x_871, 1);
lean_inc(x_874);
lean_dec(x_871);
x_875 = lean_unsigned_to_nat(1u);
x_876 = lean_nat_add(x_858, x_875);
lean_dec(x_858);
x_877 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_877, 0, x_855);
lean_ctor_set(x_877, 1, x_856);
lean_ctor_set(x_877, 2, x_857);
lean_ctor_set(x_877, 3, x_876);
lean_ctor_set(x_877, 4, x_859);
lean_ctor_set(x_877, 5, x_860);
lean_ctor_set(x_877, 6, x_861);
lean_ctor_set(x_877, 7, x_862);
lean_ctor_set(x_877, 8, x_863);
lean_ctor_set(x_877, 9, x_864);
lean_ctor_set(x_877, 10, x_865);
lean_ctor_set(x_877, 11, x_867);
lean_ctor_set(x_877, 12, x_869);
lean_ctor_set_uint8(x_877, sizeof(void*)*13, x_866);
lean_ctor_set_uint8(x_877, sizeof(void*)*13 + 1, x_868);
x_1004 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_1005 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1004, x_877, x_874);
x_1006 = lean_ctor_get(x_1005, 0);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_1005, 1);
lean_inc(x_1007);
if (lean_is_exclusive(x_1005)) {
 lean_ctor_release(x_1005, 0);
 lean_ctor_release(x_1005, 1);
 x_1008 = x_1005;
} else {
 lean_dec_ref(x_1005);
 x_1008 = lean_box(0);
}
x_1009 = lean_box(0);
x_1100 = lean_unbox(x_1006);
lean_dec(x_1006);
if (x_1100 == 0)
{
lean_dec(x_1008);
x_1034 = x_2;
x_1035 = x_3;
x_1036 = x_4;
x_1037 = x_5;
x_1038 = x_6;
x_1039 = x_7;
x_1040 = x_877;
x_1041 = x_9;
x_1042 = x_1007;
goto block_1099;
}
else
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
lean_inc(x_1);
x_1101 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_1007);
x_1102 = lean_ctor_get(x_1101, 0);
lean_inc(x_1102);
x_1103 = lean_ctor_get(x_1101, 1);
lean_inc(x_1103);
if (lean_is_exclusive(x_1101)) {
 lean_ctor_release(x_1101, 0);
 lean_ctor_release(x_1101, 1);
 x_1104 = x_1101;
} else {
 lean_dec_ref(x_1101);
 x_1104 = lean_box(0);
}
x_1105 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1104)) {
 x_1106 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1106 = x_1104;
 lean_ctor_set_tag(x_1106, 7);
}
lean_ctor_set(x_1106, 0, x_1105);
lean_ctor_set(x_1106, 1, x_1102);
if (lean_is_scalar(x_1008)) {
 x_1107 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1107 = x_1008;
 lean_ctor_set_tag(x_1107, 7);
}
lean_ctor_set(x_1107, 0, x_1106);
lean_ctor_set(x_1107, 1, x_1105);
x_1108 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1004, x_1107, x_6, x_7, x_877, x_9, x_1103);
x_1109 = lean_ctor_get(x_1108, 1);
lean_inc(x_1109);
lean_dec(x_1108);
x_1034 = x_2;
x_1035 = x_3;
x_1036 = x_4;
x_1037 = x_5;
x_1038 = x_6;
x_1039 = x_7;
x_1040 = x_877;
x_1041 = x_9;
x_1042 = x_1109;
goto block_1099;
}
block_1003:
{
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; uint8_t x_897; 
lean_dec(x_892);
lean_dec(x_890);
lean_dec(x_889);
lean_dec(x_888);
lean_dec(x_883);
lean_dec(x_881);
x_894 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_895 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_894, x_882, x_884);
x_896 = lean_ctor_get(x_895, 0);
lean_inc(x_896);
x_897 = lean_unbox(x_896);
lean_dec(x_896);
if (x_897 == 0)
{
lean_object* x_898; 
x_898 = lean_ctor_get(x_895, 1);
lean_inc(x_898);
lean_dec(x_895);
x_11 = x_886;
x_12 = x_887;
x_13 = x_885;
x_14 = x_891;
x_15 = x_878;
x_16 = x_879;
x_17 = x_882;
x_18 = x_880;
x_19 = x_898;
goto block_166;
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_899 = lean_ctor_get(x_895, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_895)) {
 lean_ctor_release(x_895, 0);
 lean_ctor_release(x_895, 1);
 x_900 = x_895;
} else {
 lean_dec_ref(x_895);
 x_900 = lean_box(0);
}
lean_inc(x_887);
x_901 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_887, x_891, x_899);
x_902 = lean_ctor_get(x_901, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_901, 1);
lean_inc(x_903);
if (lean_is_exclusive(x_901)) {
 lean_ctor_release(x_901, 0);
 lean_ctor_release(x_901, 1);
 x_904 = x_901;
} else {
 lean_dec_ref(x_901);
 x_904 = lean_box(0);
}
x_905 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_904)) {
 x_906 = lean_alloc_ctor(7, 2, 0);
} else {
 x_906 = x_904;
 lean_ctor_set_tag(x_906, 7);
}
lean_ctor_set(x_906, 0, x_905);
lean_ctor_set(x_906, 1, x_902);
if (lean_is_scalar(x_900)) {
 x_907 = lean_alloc_ctor(7, 2, 0);
} else {
 x_907 = x_900;
 lean_ctor_set_tag(x_907, 7);
}
lean_ctor_set(x_907, 0, x_906);
lean_ctor_set(x_907, 1, x_905);
x_908 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_894, x_907, x_878, x_879, x_882, x_880, x_903);
x_909 = lean_ctor_get(x_908, 1);
lean_inc(x_909);
lean_dec(x_908);
x_11 = x_886;
x_12 = x_887;
x_13 = x_885;
x_14 = x_891;
x_15 = x_878;
x_16 = x_879;
x_17 = x_882;
x_18 = x_880;
x_19 = x_909;
goto block_166;
}
}
else
{
lean_object* x_910; lean_object* x_911; 
lean_dec(x_885);
x_910 = lean_ctor_get(x_893, 0);
lean_inc(x_910);
lean_dec(x_893);
x_911 = lean_ctor_get(x_910, 1);
lean_inc(x_911);
if (lean_obj_tag(x_911) == 0)
{
lean_object* x_912; 
lean_dec(x_911);
lean_dec(x_892);
lean_dec(x_890);
lean_dec(x_889);
lean_dec(x_888);
lean_dec(x_887);
lean_dec(x_886);
lean_dec(x_883);
lean_dec(x_881);
x_912 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_910, x_891, x_878, x_879, x_882, x_880, x_884);
lean_dec(x_880);
lean_dec(x_882);
lean_dec(x_879);
lean_dec(x_878);
lean_dec(x_891);
return x_912;
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; uint8_t x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; uint8_t x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; uint8_t x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_913 = lean_ctor_get(x_910, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_911, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_911, 2);
lean_inc(x_915);
if (lean_is_exclusive(x_911)) {
 lean_ctor_release(x_911, 0);
 lean_ctor_release(x_911, 1);
 lean_ctor_release(x_911, 2);
 x_916 = x_911;
} else {
 lean_dec_ref(x_911);
 x_916 = lean_box(0);
}
x_917 = lean_int_mul(x_889, x_913);
x_918 = lean_int_mul(x_914, x_881);
x_919 = l_Lean_Meta_Grind_Arith_gcdExt(x_917, x_918);
lean_dec(x_918);
lean_dec(x_917);
x_920 = lean_ctor_get(x_919, 1);
lean_inc(x_920);
x_921 = lean_ctor_get(x_919, 0);
lean_inc(x_921);
lean_dec(x_919);
x_922 = lean_ctor_get(x_920, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_920, 1);
lean_inc(x_923);
lean_dec(x_920);
x_924 = lean_st_ref_take(x_891, x_884);
x_925 = lean_ctor_get(x_924, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_925, 14);
lean_inc(x_926);
x_927 = lean_ctor_get(x_926, 1);
lean_inc(x_927);
x_928 = lean_ctor_get(x_924, 1);
lean_inc(x_928);
lean_dec(x_924);
x_929 = lean_ctor_get(x_925, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_925, 1);
lean_inc(x_930);
x_931 = lean_ctor_get(x_925, 2);
lean_inc(x_931);
x_932 = lean_ctor_get(x_925, 3);
lean_inc(x_932);
x_933 = lean_ctor_get(x_925, 4);
lean_inc(x_933);
x_934 = lean_ctor_get(x_925, 5);
lean_inc(x_934);
x_935 = lean_ctor_get(x_925, 6);
lean_inc(x_935);
x_936 = lean_ctor_get(x_925, 7);
lean_inc(x_936);
x_937 = lean_ctor_get_uint8(x_925, sizeof(void*)*16);
x_938 = lean_ctor_get(x_925, 8);
lean_inc(x_938);
x_939 = lean_ctor_get(x_925, 9);
lean_inc(x_939);
x_940 = lean_ctor_get(x_925, 10);
lean_inc(x_940);
x_941 = lean_ctor_get(x_925, 11);
lean_inc(x_941);
x_942 = lean_ctor_get(x_925, 12);
lean_inc(x_942);
x_943 = lean_ctor_get(x_925, 13);
lean_inc(x_943);
x_944 = lean_ctor_get(x_925, 15);
lean_inc(x_944);
if (lean_is_exclusive(x_925)) {
 lean_ctor_release(x_925, 0);
 lean_ctor_release(x_925, 1);
 lean_ctor_release(x_925, 2);
 lean_ctor_release(x_925, 3);
 lean_ctor_release(x_925, 4);
 lean_ctor_release(x_925, 5);
 lean_ctor_release(x_925, 6);
 lean_ctor_release(x_925, 7);
 lean_ctor_release(x_925, 8);
 lean_ctor_release(x_925, 9);
 lean_ctor_release(x_925, 10);
 lean_ctor_release(x_925, 11);
 lean_ctor_release(x_925, 12);
 lean_ctor_release(x_925, 13);
 lean_ctor_release(x_925, 14);
 lean_ctor_release(x_925, 15);
 x_945 = x_925;
} else {
 lean_dec_ref(x_925);
 x_945 = lean_box(0);
}
x_946 = lean_ctor_get(x_926, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_926, 2);
lean_inc(x_947);
x_948 = lean_ctor_get(x_926, 3);
lean_inc(x_948);
if (lean_is_exclusive(x_926)) {
 lean_ctor_release(x_926, 0);
 lean_ctor_release(x_926, 1);
 lean_ctor_release(x_926, 2);
 lean_ctor_release(x_926, 3);
 x_949 = x_926;
} else {
 lean_dec_ref(x_926);
 x_949 = lean_box(0);
}
x_950 = lean_ctor_get(x_927, 0);
lean_inc(x_950);
x_951 = lean_ctor_get(x_927, 1);
lean_inc(x_951);
x_952 = lean_ctor_get(x_927, 2);
lean_inc(x_952);
x_953 = lean_ctor_get(x_927, 3);
lean_inc(x_953);
x_954 = lean_ctor_get(x_927, 4);
lean_inc(x_954);
x_955 = lean_ctor_get(x_927, 5);
lean_inc(x_955);
x_956 = lean_ctor_get(x_927, 6);
lean_inc(x_956);
x_957 = lean_ctor_get(x_927, 7);
lean_inc(x_957);
x_958 = lean_ctor_get(x_927, 8);
lean_inc(x_958);
x_959 = lean_ctor_get(x_927, 9);
lean_inc(x_959);
x_960 = lean_ctor_get(x_927, 10);
lean_inc(x_960);
x_961 = lean_ctor_get(x_927, 11);
lean_inc(x_961);
x_962 = lean_ctor_get(x_927, 12);
lean_inc(x_962);
x_963 = lean_ctor_get(x_927, 13);
lean_inc(x_963);
x_964 = lean_ctor_get(x_927, 14);
lean_inc(x_964);
x_965 = lean_ctor_get(x_927, 15);
lean_inc(x_965);
x_966 = lean_ctor_get_uint8(x_927, sizeof(void*)*22);
x_967 = lean_ctor_get(x_927, 16);
lean_inc(x_967);
x_968 = lean_ctor_get(x_927, 17);
lean_inc(x_968);
x_969 = lean_ctor_get(x_927, 18);
lean_inc(x_969);
x_970 = lean_ctor_get(x_927, 19);
lean_inc(x_970);
x_971 = lean_ctor_get(x_927, 20);
lean_inc(x_971);
x_972 = lean_ctor_get(x_927, 21);
lean_inc(x_972);
x_973 = lean_ctor_get_uint8(x_927, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_927)) {
 lean_ctor_release(x_927, 0);
 lean_ctor_release(x_927, 1);
 lean_ctor_release(x_927, 2);
 lean_ctor_release(x_927, 3);
 lean_ctor_release(x_927, 4);
 lean_ctor_release(x_927, 5);
 lean_ctor_release(x_927, 6);
 lean_ctor_release(x_927, 7);
 lean_ctor_release(x_927, 8);
 lean_ctor_release(x_927, 9);
 lean_ctor_release(x_927, 10);
 lean_ctor_release(x_927, 11);
 lean_ctor_release(x_927, 12);
 lean_ctor_release(x_927, 13);
 lean_ctor_release(x_927, 14);
 lean_ctor_release(x_927, 15);
 lean_ctor_release(x_927, 16);
 lean_ctor_release(x_927, 17);
 lean_ctor_release(x_927, 18);
 lean_ctor_release(x_927, 19);
 lean_ctor_release(x_927, 20);
 lean_ctor_release(x_927, 21);
 x_974 = x_927;
} else {
 lean_dec_ref(x_927);
 x_974 = lean_box(0);
}
x_975 = lean_box(0);
x_976 = l_Lean_PersistentArray_set___redArg(x_957, x_886, x_975);
if (lean_is_scalar(x_974)) {
 x_977 = lean_alloc_ctor(0, 22, 2);
} else {
 x_977 = x_974;
}
lean_ctor_set(x_977, 0, x_950);
lean_ctor_set(x_977, 1, x_951);
lean_ctor_set(x_977, 2, x_952);
lean_ctor_set(x_977, 3, x_953);
lean_ctor_set(x_977, 4, x_954);
lean_ctor_set(x_977, 5, x_955);
lean_ctor_set(x_977, 6, x_956);
lean_ctor_set(x_977, 7, x_976);
lean_ctor_set(x_977, 8, x_958);
lean_ctor_set(x_977, 9, x_959);
lean_ctor_set(x_977, 10, x_960);
lean_ctor_set(x_977, 11, x_961);
lean_ctor_set(x_977, 12, x_962);
lean_ctor_set(x_977, 13, x_963);
lean_ctor_set(x_977, 14, x_964);
lean_ctor_set(x_977, 15, x_965);
lean_ctor_set(x_977, 16, x_967);
lean_ctor_set(x_977, 17, x_968);
lean_ctor_set(x_977, 18, x_969);
lean_ctor_set(x_977, 19, x_970);
lean_ctor_set(x_977, 20, x_971);
lean_ctor_set(x_977, 21, x_972);
lean_ctor_set_uint8(x_977, sizeof(void*)*22, x_966);
lean_ctor_set_uint8(x_977, sizeof(void*)*22 + 1, x_973);
if (lean_is_scalar(x_949)) {
 x_978 = lean_alloc_ctor(0, 4, 0);
} else {
 x_978 = x_949;
}
lean_ctor_set(x_978, 0, x_946);
lean_ctor_set(x_978, 1, x_977);
lean_ctor_set(x_978, 2, x_947);
lean_ctor_set(x_978, 3, x_948);
if (lean_is_scalar(x_945)) {
 x_979 = lean_alloc_ctor(0, 16, 1);
} else {
 x_979 = x_945;
}
lean_ctor_set(x_979, 0, x_929);
lean_ctor_set(x_979, 1, x_930);
lean_ctor_set(x_979, 2, x_931);
lean_ctor_set(x_979, 3, x_932);
lean_ctor_set(x_979, 4, x_933);
lean_ctor_set(x_979, 5, x_934);
lean_ctor_set(x_979, 6, x_935);
lean_ctor_set(x_979, 7, x_936);
lean_ctor_set(x_979, 8, x_938);
lean_ctor_set(x_979, 9, x_939);
lean_ctor_set(x_979, 10, x_940);
lean_ctor_set(x_979, 11, x_941);
lean_ctor_set(x_979, 12, x_942);
lean_ctor_set(x_979, 13, x_943);
lean_ctor_set(x_979, 14, x_978);
lean_ctor_set(x_979, 15, x_944);
lean_ctor_set_uint8(x_979, sizeof(void*)*16, x_937);
x_980 = lean_st_ref_set(x_891, x_979, x_928);
x_981 = lean_ctor_get(x_980, 1);
lean_inc(x_981);
if (lean_is_exclusive(x_980)) {
 lean_ctor_release(x_980, 0);
 lean_ctor_release(x_980, 1);
 x_982 = x_980;
} else {
 lean_dec_ref(x_980);
 x_982 = lean_box(0);
}
x_983 = lean_int_mul(x_922, x_913);
lean_dec(x_922);
lean_inc(x_892);
x_984 = l_Int_Linear_Poly_mul(x_892, x_983);
lean_dec(x_983);
x_985 = lean_int_mul(x_923, x_881);
lean_dec(x_923);
lean_inc(x_915);
x_986 = l_Int_Linear_Poly_mul(x_915, x_985);
lean_dec(x_985);
x_987 = lean_int_mul(x_881, x_913);
lean_dec(x_913);
lean_dec(x_881);
x_988 = l_Int_Linear_Poly_combine(x_984, x_986);
lean_inc(x_921);
if (lean_is_scalar(x_916)) {
 x_989 = lean_alloc_ctor(1, 3, 0);
} else {
 x_989 = x_916;
}
lean_ctor_set(x_989, 0, x_921);
lean_ctor_set(x_989, 1, x_886);
lean_ctor_set(x_989, 2, x_988);
lean_inc(x_910);
lean_inc(x_887);
if (lean_is_scalar(x_982)) {
 x_990 = lean_alloc_ctor(4, 2, 0);
} else {
 x_990 = x_982;
 lean_ctor_set_tag(x_990, 4);
}
lean_ctor_set(x_990, 0, x_887);
lean_ctor_set(x_990, 1, x_910);
x_991 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_991, 0, x_987);
lean_ctor_set(x_991, 1, x_989);
lean_ctor_set(x_991, 2, x_990);
lean_inc(x_880);
lean_inc(x_882);
lean_inc(x_879);
lean_inc(x_878);
lean_inc(x_888);
lean_inc(x_883);
lean_inc(x_890);
lean_inc(x_891);
x_992 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_991, x_891, x_890, x_883, x_888, x_878, x_879, x_882, x_880, x_981);
if (lean_obj_tag(x_992) == 0)
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
x_993 = lean_ctor_get(x_992, 1);
lean_inc(x_993);
if (lean_is_exclusive(x_992)) {
 lean_ctor_release(x_992, 0);
 lean_ctor_release(x_992, 1);
 x_994 = x_992;
} else {
 lean_dec_ref(x_992);
 x_994 = lean_box(0);
}
x_995 = l_Int_Linear_Poly_mul(x_892, x_914);
lean_dec(x_914);
x_996 = lean_int_neg(x_889);
lean_dec(x_889);
x_997 = l_Int_Linear_Poly_mul(x_915, x_996);
lean_dec(x_996);
x_998 = l_Int_Linear_Poly_combine(x_995, x_997);
lean_inc(x_910);
if (lean_is_scalar(x_994)) {
 x_999 = lean_alloc_ctor(5, 2, 0);
} else {
 x_999 = x_994;
 lean_ctor_set_tag(x_999, 5);
}
lean_ctor_set(x_999, 0, x_887);
lean_ctor_set(x_999, 1, x_910);
if (lean_is_exclusive(x_910)) {
 lean_ctor_release(x_910, 0);
 lean_ctor_release(x_910, 1);
 lean_ctor_release(x_910, 2);
 x_1000 = x_910;
} else {
 lean_dec_ref(x_910);
 x_1000 = lean_box(0);
}
if (lean_is_scalar(x_1000)) {
 x_1001 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1001 = x_1000;
}
lean_ctor_set(x_1001, 0, x_921);
lean_ctor_set(x_1001, 1, x_998);
lean_ctor_set(x_1001, 2, x_999);
x_1 = x_1001;
x_2 = x_891;
x_3 = x_890;
x_4 = x_883;
x_5 = x_888;
x_6 = x_878;
x_7 = x_879;
x_8 = x_882;
x_9 = x_880;
x_10 = x_993;
goto _start;
}
else
{
lean_dec(x_921);
lean_dec(x_915);
lean_dec(x_914);
lean_dec(x_910);
lean_dec(x_892);
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_889);
lean_dec(x_888);
lean_dec(x_887);
lean_dec(x_883);
lean_dec(x_882);
lean_dec(x_880);
lean_dec(x_879);
lean_dec(x_878);
return x_992;
}
}
}
}
block_1033:
{
lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; uint8_t x_1030; 
x_1025 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_1016, x_1024);
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1026, 7);
lean_inc(x_1027);
lean_dec(x_1026);
x_1028 = lean_ctor_get(x_1025, 1);
lean_inc(x_1028);
lean_dec(x_1025);
x_1029 = lean_ctor_get(x_1027, 2);
lean_inc(x_1029);
x_1030 = lean_nat_dec_lt(x_1010, x_1029);
lean_dec(x_1029);
if (x_1030 == 0)
{
lean_object* x_1031; 
lean_dec(x_1027);
x_1031 = l_outOfBounds___redArg(x_1009);
x_878 = x_1020;
x_879 = x_1021;
x_880 = x_1023;
x_881 = x_1012;
x_882 = x_1022;
x_883 = x_1018;
x_884 = x_1028;
x_885 = x_1014;
x_886 = x_1010;
x_887 = x_1011;
x_888 = x_1019;
x_889 = x_1013;
x_890 = x_1017;
x_891 = x_1016;
x_892 = x_1015;
x_893 = x_1031;
goto block_1003;
}
else
{
lean_object* x_1032; 
x_1032 = l_Lean_PersistentArray_get_x21___redArg(x_1009, x_1027, x_1010);
x_878 = x_1020;
x_879 = x_1021;
x_880 = x_1023;
x_881 = x_1012;
x_882 = x_1022;
x_883 = x_1018;
x_884 = x_1028;
x_885 = x_1014;
x_886 = x_1010;
x_887 = x_1011;
x_888 = x_1019;
x_889 = x_1013;
x_890 = x_1017;
x_891 = x_1016;
x_892 = x_1015;
x_893 = x_1032;
goto block_1003;
}
}
block_1099:
{
lean_object* x_1043; lean_object* x_1044; 
x_1043 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_1040);
x_1044 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_1043, x_1034, x_1038, x_1039, x_1040, x_1041, x_1042);
if (lean_obj_tag(x_1044) == 0)
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; uint8_t x_1049; 
x_1045 = lean_ctor_get(x_1044, 0);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1044, 1);
lean_inc(x_1046);
lean_dec(x_1044);
x_1047 = lean_ctor_get(x_1045, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1045, 1);
lean_inc(x_1048);
lean_inc(x_1047);
x_1049 = l_Int_Linear_Poly_isUnsatDvd(x_1047, x_1048);
if (x_1049 == 0)
{
uint8_t x_1050; 
x_1050 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_1045);
if (x_1050 == 0)
{
if (lean_obj_tag(x_1048) == 0)
{
lean_object* x_1051; 
lean_dec(x_1048);
lean_dec(x_1047);
lean_dec(x_1037);
lean_dec(x_1036);
lean_dec(x_1035);
x_1051 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_1045, x_1034, x_1038, x_1039, x_1040, x_1041, x_1046);
lean_dec(x_1041);
lean_dec(x_1040);
lean_dec(x_1039);
lean_dec(x_1038);
lean_dec(x_1034);
return x_1051;
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; uint8_t x_1058; uint8_t x_1059; uint8_t x_1060; 
x_1052 = lean_ctor_get(x_1048, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1048, 1);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_1048, 2);
lean_inc(x_1054);
lean_inc(x_1045);
x_1055 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_1045, x_1034, x_1046);
x_1056 = lean_ctor_get(x_1055, 0);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1055, 1);
lean_inc(x_1057);
lean_dec(x_1055);
x_1058 = 0;
x_1059 = lean_unbox(x_1056);
lean_dec(x_1056);
x_1060 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_1059, x_1058);
if (x_1060 == 0)
{
x_1010 = x_1053;
x_1011 = x_1045;
x_1012 = x_1047;
x_1013 = x_1052;
x_1014 = x_1048;
x_1015 = x_1054;
x_1016 = x_1034;
x_1017 = x_1035;
x_1018 = x_1036;
x_1019 = x_1037;
x_1020 = x_1038;
x_1021 = x_1039;
x_1022 = x_1040;
x_1023 = x_1041;
x_1024 = x_1057;
goto block_1033;
}
else
{
lean_object* x_1061; lean_object* x_1062; 
x_1061 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_1053, x_1034, x_1057);
x_1062 = lean_ctor_get(x_1061, 1);
lean_inc(x_1062);
lean_dec(x_1061);
x_1010 = x_1053;
x_1011 = x_1045;
x_1012 = x_1047;
x_1013 = x_1052;
x_1014 = x_1048;
x_1015 = x_1054;
x_1016 = x_1034;
x_1017 = x_1035;
x_1018 = x_1036;
x_1019 = x_1037;
x_1020 = x_1038;
x_1021 = x_1039;
x_1022 = x_1040;
x_1023 = x_1041;
x_1024 = x_1062;
goto block_1033;
}
}
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; uint8_t x_1066; 
lean_dec(x_1048);
lean_dec(x_1047);
lean_dec(x_1037);
lean_dec(x_1036);
lean_dec(x_1035);
x_1063 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_1064 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1063, x_1040, x_1046);
x_1065 = lean_ctor_get(x_1064, 0);
lean_inc(x_1065);
x_1066 = lean_unbox(x_1065);
lean_dec(x_1065);
if (x_1066 == 0)
{
lean_object* x_1067; 
lean_dec(x_1045);
lean_dec(x_1041);
lean_dec(x_1040);
lean_dec(x_1039);
lean_dec(x_1038);
lean_dec(x_1034);
x_1067 = lean_ctor_get(x_1064, 1);
lean_inc(x_1067);
lean_dec(x_1064);
x_186 = x_1067;
goto block_189;
}
else
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; 
x_1068 = lean_ctor_get(x_1064, 1);
lean_inc(x_1068);
if (lean_is_exclusive(x_1064)) {
 lean_ctor_release(x_1064, 0);
 lean_ctor_release(x_1064, 1);
 x_1069 = x_1064;
} else {
 lean_dec_ref(x_1064);
 x_1069 = lean_box(0);
}
x_1070 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1045, x_1034, x_1068);
lean_dec(x_1034);
x_1071 = lean_ctor_get(x_1070, 0);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1070, 1);
lean_inc(x_1072);
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 lean_ctor_release(x_1070, 1);
 x_1073 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1073 = lean_box(0);
}
x_1074 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1073)) {
 x_1075 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1075 = x_1073;
 lean_ctor_set_tag(x_1075, 7);
}
lean_ctor_set(x_1075, 0, x_1074);
lean_ctor_set(x_1075, 1, x_1071);
if (lean_is_scalar(x_1069)) {
 x_1076 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1076 = x_1069;
 lean_ctor_set_tag(x_1076, 7);
}
lean_ctor_set(x_1076, 0, x_1075);
lean_ctor_set(x_1076, 1, x_1074);
x_1077 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1063, x_1076, x_1038, x_1039, x_1040, x_1041, x_1072);
lean_dec(x_1041);
lean_dec(x_1040);
lean_dec(x_1039);
lean_dec(x_1038);
x_1078 = lean_ctor_get(x_1077, 1);
lean_inc(x_1078);
lean_dec(x_1077);
x_186 = x_1078;
goto block_189;
}
}
}
else
{
lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; uint8_t x_1082; 
lean_dec(x_1048);
lean_dec(x_1047);
x_1079 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_1080 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1079, x_1040, x_1046);
x_1081 = lean_ctor_get(x_1080, 0);
lean_inc(x_1081);
x_1082 = lean_unbox(x_1081);
lean_dec(x_1081);
if (x_1082 == 0)
{
lean_object* x_1083; 
x_1083 = lean_ctor_get(x_1080, 1);
lean_inc(x_1083);
lean_dec(x_1080);
x_167 = x_1045;
x_168 = x_1034;
x_169 = x_1035;
x_170 = x_1036;
x_171 = x_1037;
x_172 = x_1038;
x_173 = x_1039;
x_174 = x_1040;
x_175 = x_1041;
x_176 = x_1083;
goto block_185;
}
else
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; 
x_1084 = lean_ctor_get(x_1080, 1);
lean_inc(x_1084);
if (lean_is_exclusive(x_1080)) {
 lean_ctor_release(x_1080, 0);
 lean_ctor_release(x_1080, 1);
 x_1085 = x_1080;
} else {
 lean_dec_ref(x_1080);
 x_1085 = lean_box(0);
}
lean_inc(x_1045);
x_1086 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1045, x_1034, x_1084);
x_1087 = lean_ctor_get(x_1086, 0);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_1086, 1);
lean_inc(x_1088);
if (lean_is_exclusive(x_1086)) {
 lean_ctor_release(x_1086, 0);
 lean_ctor_release(x_1086, 1);
 x_1089 = x_1086;
} else {
 lean_dec_ref(x_1086);
 x_1089 = lean_box(0);
}
x_1090 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1089)) {
 x_1091 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1091 = x_1089;
 lean_ctor_set_tag(x_1091, 7);
}
lean_ctor_set(x_1091, 0, x_1090);
lean_ctor_set(x_1091, 1, x_1087);
if (lean_is_scalar(x_1085)) {
 x_1092 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1092 = x_1085;
 lean_ctor_set_tag(x_1092, 7);
}
lean_ctor_set(x_1092, 0, x_1091);
lean_ctor_set(x_1092, 1, x_1090);
x_1093 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1079, x_1092, x_1038, x_1039, x_1040, x_1041, x_1088);
x_1094 = lean_ctor_get(x_1093, 1);
lean_inc(x_1094);
lean_dec(x_1093);
x_167 = x_1045;
x_168 = x_1034;
x_169 = x_1035;
x_170 = x_1036;
x_171 = x_1037;
x_172 = x_1038;
x_173 = x_1039;
x_174 = x_1040;
x_175 = x_1041;
x_176 = x_1094;
goto block_185;
}
}
}
else
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
lean_dec(x_1041);
lean_dec(x_1040);
lean_dec(x_1039);
lean_dec(x_1038);
lean_dec(x_1037);
lean_dec(x_1036);
lean_dec(x_1035);
lean_dec(x_1034);
x_1095 = lean_ctor_get(x_1044, 0);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_1044, 1);
lean_inc(x_1096);
if (lean_is_exclusive(x_1044)) {
 lean_ctor_release(x_1044, 0);
 lean_ctor_release(x_1044, 1);
 x_1097 = x_1044;
} else {
 lean_dec_ref(x_1044);
 x_1097 = lean_box(0);
}
if (lean_is_scalar(x_1097)) {
 x_1098 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1098 = x_1097;
}
lean_ctor_set(x_1098, 0, x_1095);
lean_ctor_set(x_1098, 1, x_1096);
return x_1098;
}
}
}
else
{
lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; 
lean_dec(x_869);
lean_dec(x_867);
lean_dec(x_865);
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_862);
lean_dec(x_861);
lean_dec(x_860);
lean_dec(x_859);
lean_dec(x_858);
lean_dec(x_857);
lean_dec(x_856);
lean_dec(x_855);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1110 = lean_ctor_get(x_871, 1);
lean_inc(x_1110);
if (lean_is_exclusive(x_871)) {
 lean_ctor_release(x_871, 0);
 lean_ctor_release(x_871, 1);
 x_1111 = x_871;
} else {
 lean_dec_ref(x_871);
 x_1111 = lean_box(0);
}
x_1112 = lean_box(0);
if (lean_is_scalar(x_1111)) {
 x_1113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1113 = x_1111;
}
lean_ctor_set(x_1113, 0, x_1112);
lean_ctor_set(x_1113, 1, x_1110);
return x_1113;
}
}
else
{
lean_object* x_1114; 
lean_dec(x_869);
lean_dec(x_867);
lean_dec(x_865);
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_862);
lean_dec(x_861);
lean_dec(x_859);
lean_dec(x_858);
lean_dec(x_857);
lean_dec(x_856);
lean_dec(x_855);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1114 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_860, x_10);
return x_1114;
}
}
block_166:
{
lean_object* x_20; 
x_20 = l_Int_Linear_Poly_updateOccs___redArg(x_13, x_14, x_15, x_16, x_17, x_18, x_19);
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
lean_ctor_set(x_33, 0, x_12);
x_34 = l_Lean_PersistentArray_set___redArg(x_32, x_11, x_33);
lean_dec(x_11);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
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
x_58 = lean_ctor_get_uint8(x_25, sizeof(void*)*22);
x_59 = lean_ctor_get(x_25, 16);
x_60 = lean_ctor_get(x_25, 17);
x_61 = lean_ctor_get(x_25, 18);
x_62 = lean_ctor_get(x_25, 19);
x_63 = lean_ctor_get(x_25, 20);
x_64 = lean_ctor_get(x_25, 21);
x_65 = lean_ctor_get_uint8(x_25, sizeof(void*)*22 + 1);
lean_inc(x_64);
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
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_12);
x_67 = l_Lean_PersistentArray_set___redArg(x_49, x_11, x_66);
lean_dec(x_11);
x_68 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_68, 0, x_42);
lean_ctor_set(x_68, 1, x_43);
lean_ctor_set(x_68, 2, x_44);
lean_ctor_set(x_68, 3, x_45);
lean_ctor_set(x_68, 4, x_46);
lean_ctor_set(x_68, 5, x_47);
lean_ctor_set(x_68, 6, x_48);
lean_ctor_set(x_68, 7, x_67);
lean_ctor_set(x_68, 8, x_50);
lean_ctor_set(x_68, 9, x_51);
lean_ctor_set(x_68, 10, x_52);
lean_ctor_set(x_68, 11, x_53);
lean_ctor_set(x_68, 12, x_54);
lean_ctor_set(x_68, 13, x_55);
lean_ctor_set(x_68, 14, x_56);
lean_ctor_set(x_68, 15, x_57);
lean_ctor_set(x_68, 16, x_59);
lean_ctor_set(x_68, 17, x_60);
lean_ctor_set(x_68, 18, x_61);
lean_ctor_set(x_68, 19, x_62);
lean_ctor_set(x_68, 20, x_63);
lean_ctor_set(x_68, 21, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*22, x_58);
lean_ctor_set_uint8(x_68, sizeof(void*)*22 + 1, x_65);
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
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_74 = lean_ctor_get(x_24, 0);
x_75 = lean_ctor_get(x_24, 2);
x_76 = lean_ctor_get(x_24, 3);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_24);
x_77 = lean_ctor_get(x_25, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_25, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_25, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_25, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_25, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_25, 5);
lean_inc(x_82);
x_83 = lean_ctor_get(x_25, 6);
lean_inc(x_83);
x_84 = lean_ctor_get(x_25, 7);
lean_inc(x_84);
x_85 = lean_ctor_get(x_25, 8);
lean_inc(x_85);
x_86 = lean_ctor_get(x_25, 9);
lean_inc(x_86);
x_87 = lean_ctor_get(x_25, 10);
lean_inc(x_87);
x_88 = lean_ctor_get(x_25, 11);
lean_inc(x_88);
x_89 = lean_ctor_get(x_25, 12);
lean_inc(x_89);
x_90 = lean_ctor_get(x_25, 13);
lean_inc(x_90);
x_91 = lean_ctor_get(x_25, 14);
lean_inc(x_91);
x_92 = lean_ctor_get(x_25, 15);
lean_inc(x_92);
x_93 = lean_ctor_get_uint8(x_25, sizeof(void*)*22);
x_94 = lean_ctor_get(x_25, 16);
lean_inc(x_94);
x_95 = lean_ctor_get(x_25, 17);
lean_inc(x_95);
x_96 = lean_ctor_get(x_25, 18);
lean_inc(x_96);
x_97 = lean_ctor_get(x_25, 19);
lean_inc(x_97);
x_98 = lean_ctor_get(x_25, 20);
lean_inc(x_98);
x_99 = lean_ctor_get(x_25, 21);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_25, sizeof(void*)*22 + 1);
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
x_103 = l_Lean_PersistentArray_set___redArg(x_84, x_11, x_102);
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
lean_ctor_set(x_104, 6, x_83);
lean_ctor_set(x_104, 7, x_103);
lean_ctor_set(x_104, 8, x_85);
lean_ctor_set(x_104, 9, x_86);
lean_ctor_set(x_104, 10, x_87);
lean_ctor_set(x_104, 11, x_88);
lean_ctor_set(x_104, 12, x_89);
lean_ctor_set(x_104, 13, x_90);
lean_ctor_set(x_104, 14, x_91);
lean_ctor_set(x_104, 15, x_92);
lean_ctor_set(x_104, 16, x_94);
lean_ctor_set(x_104, 17, x_95);
lean_ctor_set(x_104, 18, x_96);
lean_ctor_set(x_104, 19, x_97);
lean_ctor_set(x_104, 20, x_98);
lean_ctor_set(x_104, 21, x_99);
lean_ctor_set_uint8(x_104, sizeof(void*)*22, x_93);
lean_ctor_set_uint8(x_104, sizeof(void*)*22 + 1, x_100);
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
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
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
lean_inc(x_127);
x_128 = lean_ctor_get(x_24, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_24, 3);
lean_inc(x_129);
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
lean_inc(x_131);
x_132 = lean_ctor_get(x_25, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_25, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_25, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_25, 4);
lean_inc(x_135);
x_136 = lean_ctor_get(x_25, 5);
lean_inc(x_136);
x_137 = lean_ctor_get(x_25, 6);
lean_inc(x_137);
x_138 = lean_ctor_get(x_25, 7);
lean_inc(x_138);
x_139 = lean_ctor_get(x_25, 8);
lean_inc(x_139);
x_140 = lean_ctor_get(x_25, 9);
lean_inc(x_140);
x_141 = lean_ctor_get(x_25, 10);
lean_inc(x_141);
x_142 = lean_ctor_get(x_25, 11);
lean_inc(x_142);
x_143 = lean_ctor_get(x_25, 12);
lean_inc(x_143);
x_144 = lean_ctor_get(x_25, 13);
lean_inc(x_144);
x_145 = lean_ctor_get(x_25, 14);
lean_inc(x_145);
x_146 = lean_ctor_get(x_25, 15);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_25, sizeof(void*)*22);
x_148 = lean_ctor_get(x_25, 16);
lean_inc(x_148);
x_149 = lean_ctor_get(x_25, 17);
lean_inc(x_149);
x_150 = lean_ctor_get(x_25, 18);
lean_inc(x_150);
x_151 = lean_ctor_get(x_25, 19);
lean_inc(x_151);
x_152 = lean_ctor_get(x_25, 20);
lean_inc(x_152);
x_153 = lean_ctor_get(x_25, 21);
lean_inc(x_153);
x_154 = lean_ctor_get_uint8(x_25, sizeof(void*)*22 + 1);
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
lean_ctor_set(x_156, 0, x_12);
x_157 = l_Lean_PersistentArray_set___redArg(x_138, x_11, x_156);
lean_dec(x_11);
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
lean_ctor_set(x_158, 6, x_137);
lean_ctor_set(x_158, 7, x_157);
lean_ctor_set(x_158, 8, x_139);
lean_ctor_set(x_158, 9, x_140);
lean_ctor_set(x_158, 10, x_141);
lean_ctor_set(x_158, 11, x_142);
lean_ctor_set(x_158, 12, x_143);
lean_ctor_set(x_158, 13, x_144);
lean_ctor_set(x_158, 14, x_145);
lean_ctor_set(x_158, 15, x_146);
lean_ctor_set(x_158, 16, x_148);
lean_ctor_set(x_158, 17, x_149);
lean_ctor_set(x_158, 18, x_150);
lean_ctor_set(x_158, 19, x_151);
lean_ctor_set(x_158, 20, x_152);
lean_ctor_set(x_158, 21, x_153);
lean_ctor_set_uint8(x_158, sizeof(void*)*22, x_147);
lean_ctor_set_uint8(x_158, sizeof(void*)*22 + 1, x_154);
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
lean_dec(x_11);
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

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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2668_(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_180; uint8_t x_184; 
x_184 = !lean_is_exclusive(x_8);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_185 = lean_ctor_get(x_8, 0);
x_186 = lean_ctor_get(x_8, 1);
x_187 = lean_ctor_get(x_8, 2);
x_188 = lean_ctor_get(x_8, 3);
x_189 = lean_ctor_get(x_8, 4);
x_190 = lean_ctor_get(x_8, 5);
x_191 = lean_ctor_get(x_8, 6);
x_192 = lean_ctor_get(x_8, 7);
x_193 = lean_ctor_get(x_8, 8);
x_194 = lean_ctor_get(x_8, 9);
x_195 = lean_ctor_get(x_8, 10);
x_196 = lean_ctor_get(x_8, 11);
x_197 = lean_ctor_get(x_8, 12);
x_198 = lean_nat_dec_eq(x_188, x_189);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_199 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_unbox(x_200);
lean_dec(x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_591; lean_object* x_592; uint8_t x_593; 
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
lean_dec(x_199);
x_203 = lean_unsigned_to_nat(1u);
x_204 = lean_nat_add(x_188, x_203);
lean_dec(x_188);
lean_ctor_set(x_8, 3, x_204);
x_591 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_592 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_591, x_8, x_202);
x_593 = !lean_is_exclusive(x_592);
if (x_593 == 0)
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_718; 
x_594 = lean_ctor_get(x_592, 0);
x_595 = lean_ctor_get(x_592, 1);
x_596 = lean_box(0);
x_718 = lean_unbox(x_594);
lean_dec(x_594);
if (x_718 == 0)
{
lean_free_object(x_592);
x_621 = x_2;
x_622 = x_3;
x_623 = x_4;
x_624 = x_5;
x_625 = x_6;
x_626 = x_7;
x_627 = x_8;
x_628 = x_9;
x_629 = x_595;
goto block_717;
}
else
{
lean_object* x_719; uint8_t x_720; 
lean_inc(x_1);
x_719 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_595);
x_720 = !lean_is_exclusive(x_719);
if (x_720 == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_721 = lean_ctor_get(x_719, 0);
x_722 = lean_ctor_get(x_719, 1);
x_723 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_719, 7);
lean_ctor_set(x_719, 1, x_721);
lean_ctor_set(x_719, 0, x_723);
lean_ctor_set_tag(x_592, 7);
lean_ctor_set(x_592, 1, x_723);
lean_ctor_set(x_592, 0, x_719);
x_724 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_591, x_592, x_6, x_7, x_8, x_9, x_722);
x_725 = lean_ctor_get(x_724, 1);
lean_inc(x_725);
lean_dec(x_724);
x_621 = x_2;
x_622 = x_3;
x_623 = x_4;
x_624 = x_5;
x_625 = x_6;
x_626 = x_7;
x_627 = x_8;
x_628 = x_9;
x_629 = x_725;
goto block_717;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_726 = lean_ctor_get(x_719, 0);
x_727 = lean_ctor_get(x_719, 1);
lean_inc(x_727);
lean_inc(x_726);
lean_dec(x_719);
x_728 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_729 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_729, 0, x_728);
lean_ctor_set(x_729, 1, x_726);
lean_ctor_set_tag(x_592, 7);
lean_ctor_set(x_592, 1, x_728);
lean_ctor_set(x_592, 0, x_729);
x_730 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_591, x_592, x_6, x_7, x_8, x_9, x_727);
x_731 = lean_ctor_get(x_730, 1);
lean_inc(x_731);
lean_dec(x_730);
x_621 = x_2;
x_622 = x_3;
x_623 = x_4;
x_624 = x_5;
x_625 = x_6;
x_626 = x_7;
x_627 = x_8;
x_628 = x_9;
x_629 = x_731;
goto block_717;
}
}
block_620:
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; uint8_t x_617; 
x_612 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_603, x_611);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_613, 7);
lean_inc(x_614);
lean_dec(x_613);
x_615 = lean_ctor_get(x_612, 1);
lean_inc(x_615);
lean_dec(x_612);
x_616 = lean_ctor_get(x_614, 2);
lean_inc(x_616);
x_617 = lean_nat_dec_lt(x_601, x_616);
lean_dec(x_616);
if (x_617 == 0)
{
lean_object* x_618; 
lean_dec(x_614);
x_618 = l_outOfBounds___redArg(x_596);
x_205 = x_603;
x_206 = x_610;
x_207 = x_609;
x_208 = x_601;
x_209 = x_600;
x_210 = x_607;
x_211 = x_605;
x_212 = x_604;
x_213 = x_602;
x_214 = x_597;
x_215 = x_608;
x_216 = x_598;
x_217 = x_599;
x_218 = x_606;
x_219 = x_615;
x_220 = x_618;
goto block_590;
}
else
{
lean_object* x_619; 
x_619 = l_Lean_PersistentArray_get_x21___redArg(x_596, x_614, x_601);
x_205 = x_603;
x_206 = x_610;
x_207 = x_609;
x_208 = x_601;
x_209 = x_600;
x_210 = x_607;
x_211 = x_605;
x_212 = x_604;
x_213 = x_602;
x_214 = x_597;
x_215 = x_608;
x_216 = x_598;
x_217 = x_599;
x_218 = x_606;
x_219 = x_615;
x_220 = x_619;
goto block_590;
}
}
block_717:
{
lean_object* x_630; lean_object* x_631; 
x_630 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_627);
x_631 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_630, x_621, x_625, x_626, x_627, x_628, x_629);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; uint8_t x_636; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
lean_dec(x_631);
x_634 = lean_ctor_get(x_632, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_632, 1);
lean_inc(x_635);
lean_inc(x_634);
x_636 = l_Int_Linear_Poly_isUnsatDvd(x_634, x_635);
if (x_636 == 0)
{
uint8_t x_637; 
x_637 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_632);
if (x_637 == 0)
{
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_638; 
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_622);
x_638 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_632, x_621, x_625, x_626, x_627, x_628, x_633);
lean_dec(x_628);
lean_dec(x_627);
lean_dec(x_626);
lean_dec(x_625);
lean_dec(x_621);
return x_638;
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; uint8_t x_647; uint8_t x_648; 
x_639 = lean_ctor_get(x_635, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_635, 1);
lean_inc(x_640);
x_641 = lean_ctor_get(x_635, 2);
lean_inc(x_641);
lean_inc(x_632);
x_642 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_632, x_621, x_633);
x_643 = lean_ctor_get(x_642, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_642, 1);
lean_inc(x_644);
lean_dec(x_642);
x_645 = lean_box(0);
x_646 = lean_unbox(x_643);
lean_dec(x_643);
x_647 = lean_unbox(x_645);
x_648 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_646, x_647);
if (x_648 == 0)
{
x_597 = x_635;
x_598 = x_639;
x_599 = x_641;
x_600 = x_634;
x_601 = x_640;
x_602 = x_632;
x_603 = x_621;
x_604 = x_622;
x_605 = x_623;
x_606 = x_624;
x_607 = x_625;
x_608 = x_626;
x_609 = x_627;
x_610 = x_628;
x_611 = x_644;
goto block_620;
}
else
{
lean_object* x_649; lean_object* x_650; 
x_649 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_640, x_621, x_644);
x_650 = lean_ctor_get(x_649, 1);
lean_inc(x_650);
lean_dec(x_649);
x_597 = x_635;
x_598 = x_639;
x_599 = x_641;
x_600 = x_634;
x_601 = x_640;
x_602 = x_632;
x_603 = x_621;
x_604 = x_622;
x_605 = x_623;
x_606 = x_624;
x_607 = x_625;
x_608 = x_626;
x_609 = x_627;
x_610 = x_628;
x_611 = x_650;
goto block_620;
}
}
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; uint8_t x_654; 
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_622);
x_651 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_652 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_651, x_627, x_633);
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_unbox(x_653);
lean_dec(x_653);
if (x_654 == 0)
{
lean_object* x_655; 
lean_dec(x_632);
lean_dec(x_628);
lean_dec(x_627);
lean_dec(x_626);
lean_dec(x_625);
lean_dec(x_621);
x_655 = lean_ctor_get(x_652, 1);
lean_inc(x_655);
lean_dec(x_652);
x_180 = x_655;
goto block_183;
}
else
{
uint8_t x_656; 
x_656 = !lean_is_exclusive(x_652);
if (x_656 == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; uint8_t x_660; 
x_657 = lean_ctor_get(x_652, 1);
x_658 = lean_ctor_get(x_652, 0);
lean_dec(x_658);
x_659 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_632, x_621, x_657);
lean_dec(x_621);
x_660 = !lean_is_exclusive(x_659);
if (x_660 == 0)
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_661 = lean_ctor_get(x_659, 0);
x_662 = lean_ctor_get(x_659, 1);
x_663 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_659, 7);
lean_ctor_set(x_659, 1, x_661);
lean_ctor_set(x_659, 0, x_663);
lean_ctor_set_tag(x_652, 7);
lean_ctor_set(x_652, 1, x_663);
lean_ctor_set(x_652, 0, x_659);
x_664 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_651, x_652, x_625, x_626, x_627, x_628, x_662);
lean_dec(x_628);
lean_dec(x_627);
lean_dec(x_626);
lean_dec(x_625);
x_665 = lean_ctor_get(x_664, 1);
lean_inc(x_665);
lean_dec(x_664);
x_180 = x_665;
goto block_183;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_666 = lean_ctor_get(x_659, 0);
x_667 = lean_ctor_get(x_659, 1);
lean_inc(x_667);
lean_inc(x_666);
lean_dec(x_659);
x_668 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_669 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_666);
lean_ctor_set_tag(x_652, 7);
lean_ctor_set(x_652, 1, x_668);
lean_ctor_set(x_652, 0, x_669);
x_670 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_651, x_652, x_625, x_626, x_627, x_628, x_667);
lean_dec(x_628);
lean_dec(x_627);
lean_dec(x_626);
lean_dec(x_625);
x_671 = lean_ctor_get(x_670, 1);
lean_inc(x_671);
lean_dec(x_670);
x_180 = x_671;
goto block_183;
}
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_672 = lean_ctor_get(x_652, 1);
lean_inc(x_672);
lean_dec(x_652);
x_673 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_632, x_621, x_672);
lean_dec(x_621);
x_674 = lean_ctor_get(x_673, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 x_676 = x_673;
} else {
 lean_dec_ref(x_673);
 x_676 = lean_box(0);
}
x_677 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_676)) {
 x_678 = lean_alloc_ctor(7, 2, 0);
} else {
 x_678 = x_676;
 lean_ctor_set_tag(x_678, 7);
}
lean_ctor_set(x_678, 0, x_677);
lean_ctor_set(x_678, 1, x_674);
x_679 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_679, 0, x_678);
lean_ctor_set(x_679, 1, x_677);
x_680 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_651, x_679, x_625, x_626, x_627, x_628, x_675);
lean_dec(x_628);
lean_dec(x_627);
lean_dec(x_626);
lean_dec(x_625);
x_681 = lean_ctor_get(x_680, 1);
lean_inc(x_681);
lean_dec(x_680);
x_180 = x_681;
goto block_183;
}
}
}
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; uint8_t x_685; 
lean_dec(x_635);
lean_dec(x_634);
x_682 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_683 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_682, x_627, x_633);
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
x_685 = lean_unbox(x_684);
lean_dec(x_684);
if (x_685 == 0)
{
lean_object* x_686; 
x_686 = lean_ctor_get(x_683, 1);
lean_inc(x_686);
lean_dec(x_683);
x_161 = x_632;
x_162 = x_621;
x_163 = x_622;
x_164 = x_623;
x_165 = x_624;
x_166 = x_625;
x_167 = x_626;
x_168 = x_627;
x_169 = x_628;
x_170 = x_686;
goto block_179;
}
else
{
uint8_t x_687; 
x_687 = !lean_is_exclusive(x_683);
if (x_687 == 0)
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; uint8_t x_691; 
x_688 = lean_ctor_get(x_683, 1);
x_689 = lean_ctor_get(x_683, 0);
lean_dec(x_689);
lean_inc(x_632);
x_690 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_632, x_621, x_688);
x_691 = !lean_is_exclusive(x_690);
if (x_691 == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_692 = lean_ctor_get(x_690, 0);
x_693 = lean_ctor_get(x_690, 1);
x_694 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_690, 7);
lean_ctor_set(x_690, 1, x_692);
lean_ctor_set(x_690, 0, x_694);
lean_ctor_set_tag(x_683, 7);
lean_ctor_set(x_683, 1, x_694);
lean_ctor_set(x_683, 0, x_690);
x_695 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_682, x_683, x_625, x_626, x_627, x_628, x_693);
x_696 = lean_ctor_get(x_695, 1);
lean_inc(x_696);
lean_dec(x_695);
x_161 = x_632;
x_162 = x_621;
x_163 = x_622;
x_164 = x_623;
x_165 = x_624;
x_166 = x_625;
x_167 = x_626;
x_168 = x_627;
x_169 = x_628;
x_170 = x_696;
goto block_179;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_697 = lean_ctor_get(x_690, 0);
x_698 = lean_ctor_get(x_690, 1);
lean_inc(x_698);
lean_inc(x_697);
lean_dec(x_690);
x_699 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_700 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_697);
lean_ctor_set_tag(x_683, 7);
lean_ctor_set(x_683, 1, x_699);
lean_ctor_set(x_683, 0, x_700);
x_701 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_682, x_683, x_625, x_626, x_627, x_628, x_698);
x_702 = lean_ctor_get(x_701, 1);
lean_inc(x_702);
lean_dec(x_701);
x_161 = x_632;
x_162 = x_621;
x_163 = x_622;
x_164 = x_623;
x_165 = x_624;
x_166 = x_625;
x_167 = x_626;
x_168 = x_627;
x_169 = x_628;
x_170 = x_702;
goto block_179;
}
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_703 = lean_ctor_get(x_683, 1);
lean_inc(x_703);
lean_dec(x_683);
lean_inc(x_632);
x_704 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_632, x_621, x_703);
x_705 = lean_ctor_get(x_704, 0);
lean_inc(x_705);
x_706 = lean_ctor_get(x_704, 1);
lean_inc(x_706);
if (lean_is_exclusive(x_704)) {
 lean_ctor_release(x_704, 0);
 lean_ctor_release(x_704, 1);
 x_707 = x_704;
} else {
 lean_dec_ref(x_704);
 x_707 = lean_box(0);
}
x_708 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_707)) {
 x_709 = lean_alloc_ctor(7, 2, 0);
} else {
 x_709 = x_707;
 lean_ctor_set_tag(x_709, 7);
}
lean_ctor_set(x_709, 0, x_708);
lean_ctor_set(x_709, 1, x_705);
x_710 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_710, 0, x_709);
lean_ctor_set(x_710, 1, x_708);
x_711 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_682, x_710, x_625, x_626, x_627, x_628, x_706);
x_712 = lean_ctor_get(x_711, 1);
lean_inc(x_712);
lean_dec(x_711);
x_161 = x_632;
x_162 = x_621;
x_163 = x_622;
x_164 = x_623;
x_165 = x_624;
x_166 = x_625;
x_167 = x_626;
x_168 = x_627;
x_169 = x_628;
x_170 = x_712;
goto block_179;
}
}
}
}
else
{
uint8_t x_713; 
lean_dec(x_628);
lean_dec(x_627);
lean_dec(x_626);
lean_dec(x_625);
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_621);
x_713 = !lean_is_exclusive(x_631);
if (x_713 == 0)
{
return x_631;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_714 = lean_ctor_get(x_631, 0);
x_715 = lean_ctor_get(x_631, 1);
lean_inc(x_715);
lean_inc(x_714);
lean_dec(x_631);
x_716 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_716, 0, x_714);
lean_ctor_set(x_716, 1, x_715);
return x_716;
}
}
}
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; uint8_t x_826; 
x_732 = lean_ctor_get(x_592, 0);
x_733 = lean_ctor_get(x_592, 1);
lean_inc(x_733);
lean_inc(x_732);
lean_dec(x_592);
x_734 = lean_box(0);
x_826 = lean_unbox(x_732);
lean_dec(x_732);
if (x_826 == 0)
{
x_759 = x_2;
x_760 = x_3;
x_761 = x_4;
x_762 = x_5;
x_763 = x_6;
x_764 = x_7;
x_765 = x_8;
x_766 = x_9;
x_767 = x_733;
goto block_825;
}
else
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
lean_inc(x_1);
x_827 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_733);
x_828 = lean_ctor_get(x_827, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_827, 1);
lean_inc(x_829);
if (lean_is_exclusive(x_827)) {
 lean_ctor_release(x_827, 0);
 lean_ctor_release(x_827, 1);
 x_830 = x_827;
} else {
 lean_dec_ref(x_827);
 x_830 = lean_box(0);
}
x_831 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_830)) {
 x_832 = lean_alloc_ctor(7, 2, 0);
} else {
 x_832 = x_830;
 lean_ctor_set_tag(x_832, 7);
}
lean_ctor_set(x_832, 0, x_831);
lean_ctor_set(x_832, 1, x_828);
x_833 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_833, 0, x_832);
lean_ctor_set(x_833, 1, x_831);
x_834 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_591, x_833, x_6, x_7, x_8, x_9, x_829);
x_835 = lean_ctor_get(x_834, 1);
lean_inc(x_835);
lean_dec(x_834);
x_759 = x_2;
x_760 = x_3;
x_761 = x_4;
x_762 = x_5;
x_763 = x_6;
x_764 = x_7;
x_765 = x_8;
x_766 = x_9;
x_767 = x_835;
goto block_825;
}
block_758:
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; uint8_t x_755; 
x_750 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_741, x_749);
x_751 = lean_ctor_get(x_750, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_751, 7);
lean_inc(x_752);
lean_dec(x_751);
x_753 = lean_ctor_get(x_750, 1);
lean_inc(x_753);
lean_dec(x_750);
x_754 = lean_ctor_get(x_752, 2);
lean_inc(x_754);
x_755 = lean_nat_dec_lt(x_739, x_754);
lean_dec(x_754);
if (x_755 == 0)
{
lean_object* x_756; 
lean_dec(x_752);
x_756 = l_outOfBounds___redArg(x_734);
x_205 = x_741;
x_206 = x_748;
x_207 = x_747;
x_208 = x_739;
x_209 = x_738;
x_210 = x_745;
x_211 = x_743;
x_212 = x_742;
x_213 = x_740;
x_214 = x_735;
x_215 = x_746;
x_216 = x_736;
x_217 = x_737;
x_218 = x_744;
x_219 = x_753;
x_220 = x_756;
goto block_590;
}
else
{
lean_object* x_757; 
x_757 = l_Lean_PersistentArray_get_x21___redArg(x_734, x_752, x_739);
x_205 = x_741;
x_206 = x_748;
x_207 = x_747;
x_208 = x_739;
x_209 = x_738;
x_210 = x_745;
x_211 = x_743;
x_212 = x_742;
x_213 = x_740;
x_214 = x_735;
x_215 = x_746;
x_216 = x_736;
x_217 = x_737;
x_218 = x_744;
x_219 = x_753;
x_220 = x_757;
goto block_590;
}
}
block_825:
{
lean_object* x_768; lean_object* x_769; 
x_768 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_765);
x_769 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_768, x_759, x_763, x_764, x_765, x_766, x_767);
if (lean_obj_tag(x_769) == 0)
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; uint8_t x_774; 
x_770 = lean_ctor_get(x_769, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_769, 1);
lean_inc(x_771);
lean_dec(x_769);
x_772 = lean_ctor_get(x_770, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_770, 1);
lean_inc(x_773);
lean_inc(x_772);
x_774 = l_Int_Linear_Poly_isUnsatDvd(x_772, x_773);
if (x_774 == 0)
{
uint8_t x_775; 
x_775 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_770);
if (x_775 == 0)
{
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_776; 
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
x_776 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_770, x_759, x_763, x_764, x_765, x_766, x_771);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_759);
return x_776;
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; uint8_t x_784; uint8_t x_785; uint8_t x_786; 
x_777 = lean_ctor_get(x_773, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_773, 1);
lean_inc(x_778);
x_779 = lean_ctor_get(x_773, 2);
lean_inc(x_779);
lean_inc(x_770);
x_780 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_770, x_759, x_771);
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
lean_dec(x_780);
x_783 = lean_box(0);
x_784 = lean_unbox(x_781);
lean_dec(x_781);
x_785 = lean_unbox(x_783);
x_786 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_784, x_785);
if (x_786 == 0)
{
x_735 = x_773;
x_736 = x_777;
x_737 = x_779;
x_738 = x_772;
x_739 = x_778;
x_740 = x_770;
x_741 = x_759;
x_742 = x_760;
x_743 = x_761;
x_744 = x_762;
x_745 = x_763;
x_746 = x_764;
x_747 = x_765;
x_748 = x_766;
x_749 = x_782;
goto block_758;
}
else
{
lean_object* x_787; lean_object* x_788; 
x_787 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_778, x_759, x_782);
x_788 = lean_ctor_get(x_787, 1);
lean_inc(x_788);
lean_dec(x_787);
x_735 = x_773;
x_736 = x_777;
x_737 = x_779;
x_738 = x_772;
x_739 = x_778;
x_740 = x_770;
x_741 = x_759;
x_742 = x_760;
x_743 = x_761;
x_744 = x_762;
x_745 = x_763;
x_746 = x_764;
x_747 = x_765;
x_748 = x_766;
x_749 = x_788;
goto block_758;
}
}
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; uint8_t x_792; 
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
x_789 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_790 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_789, x_765, x_771);
x_791 = lean_ctor_get(x_790, 0);
lean_inc(x_791);
x_792 = lean_unbox(x_791);
lean_dec(x_791);
if (x_792 == 0)
{
lean_object* x_793; 
lean_dec(x_770);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_759);
x_793 = lean_ctor_get(x_790, 1);
lean_inc(x_793);
lean_dec(x_790);
x_180 = x_793;
goto block_183;
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_794 = lean_ctor_get(x_790, 1);
lean_inc(x_794);
if (lean_is_exclusive(x_790)) {
 lean_ctor_release(x_790, 0);
 lean_ctor_release(x_790, 1);
 x_795 = x_790;
} else {
 lean_dec_ref(x_790);
 x_795 = lean_box(0);
}
x_796 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_770, x_759, x_794);
lean_dec(x_759);
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_796, 1);
lean_inc(x_798);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 x_799 = x_796;
} else {
 lean_dec_ref(x_796);
 x_799 = lean_box(0);
}
x_800 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_799)) {
 x_801 = lean_alloc_ctor(7, 2, 0);
} else {
 x_801 = x_799;
 lean_ctor_set_tag(x_801, 7);
}
lean_ctor_set(x_801, 0, x_800);
lean_ctor_set(x_801, 1, x_797);
if (lean_is_scalar(x_795)) {
 x_802 = lean_alloc_ctor(7, 2, 0);
} else {
 x_802 = x_795;
 lean_ctor_set_tag(x_802, 7);
}
lean_ctor_set(x_802, 0, x_801);
lean_ctor_set(x_802, 1, x_800);
x_803 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_789, x_802, x_763, x_764, x_765, x_766, x_798);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
x_804 = lean_ctor_get(x_803, 1);
lean_inc(x_804);
lean_dec(x_803);
x_180 = x_804;
goto block_183;
}
}
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; uint8_t x_808; 
lean_dec(x_773);
lean_dec(x_772);
x_805 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_806 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_805, x_765, x_771);
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
x_808 = lean_unbox(x_807);
lean_dec(x_807);
if (x_808 == 0)
{
lean_object* x_809; 
x_809 = lean_ctor_get(x_806, 1);
lean_inc(x_809);
lean_dec(x_806);
x_161 = x_770;
x_162 = x_759;
x_163 = x_760;
x_164 = x_761;
x_165 = x_762;
x_166 = x_763;
x_167 = x_764;
x_168 = x_765;
x_169 = x_766;
x_170 = x_809;
goto block_179;
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_810 = lean_ctor_get(x_806, 1);
lean_inc(x_810);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 lean_ctor_release(x_806, 1);
 x_811 = x_806;
} else {
 lean_dec_ref(x_806);
 x_811 = lean_box(0);
}
lean_inc(x_770);
x_812 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_770, x_759, x_810);
x_813 = lean_ctor_get(x_812, 0);
lean_inc(x_813);
x_814 = lean_ctor_get(x_812, 1);
lean_inc(x_814);
if (lean_is_exclusive(x_812)) {
 lean_ctor_release(x_812, 0);
 lean_ctor_release(x_812, 1);
 x_815 = x_812;
} else {
 lean_dec_ref(x_812);
 x_815 = lean_box(0);
}
x_816 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_815)) {
 x_817 = lean_alloc_ctor(7, 2, 0);
} else {
 x_817 = x_815;
 lean_ctor_set_tag(x_817, 7);
}
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_813);
if (lean_is_scalar(x_811)) {
 x_818 = lean_alloc_ctor(7, 2, 0);
} else {
 x_818 = x_811;
 lean_ctor_set_tag(x_818, 7);
}
lean_ctor_set(x_818, 0, x_817);
lean_ctor_set(x_818, 1, x_816);
x_819 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_805, x_818, x_763, x_764, x_765, x_766, x_814);
x_820 = lean_ctor_get(x_819, 1);
lean_inc(x_820);
lean_dec(x_819);
x_161 = x_770;
x_162 = x_759;
x_163 = x_760;
x_164 = x_761;
x_165 = x_762;
x_166 = x_763;
x_167 = x_764;
x_168 = x_765;
x_169 = x_766;
x_170 = x_820;
goto block_179;
}
}
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_759);
x_821 = lean_ctor_get(x_769, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_769, 1);
lean_inc(x_822);
if (lean_is_exclusive(x_769)) {
 lean_ctor_release(x_769, 0);
 lean_ctor_release(x_769, 1);
 x_823 = x_769;
} else {
 lean_dec_ref(x_769);
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
block_590:
{
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_209);
x_221 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_222 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_221, x_207, x_219);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_unbox(x_223);
lean_dec(x_223);
if (x_224 == 0)
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
x_11 = x_214;
x_12 = x_208;
x_13 = x_213;
x_14 = x_205;
x_15 = x_210;
x_16 = x_215;
x_17 = x_207;
x_18 = x_206;
x_19 = x_225;
goto block_160;
}
else
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_222);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_227 = lean_ctor_get(x_222, 1);
x_228 = lean_ctor_get(x_222, 0);
lean_dec(x_228);
lean_inc(x_213);
x_229 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_213, x_205, x_227);
x_230 = !lean_is_exclusive(x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_231 = lean_ctor_get(x_229, 0);
x_232 = lean_ctor_get(x_229, 1);
x_233 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_229, 7);
lean_ctor_set(x_229, 1, x_231);
lean_ctor_set(x_229, 0, x_233);
lean_ctor_set_tag(x_222, 7);
lean_ctor_set(x_222, 1, x_233);
lean_ctor_set(x_222, 0, x_229);
x_234 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_221, x_222, x_210, x_215, x_207, x_206, x_232);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
lean_dec(x_234);
x_11 = x_214;
x_12 = x_208;
x_13 = x_213;
x_14 = x_205;
x_15 = x_210;
x_16 = x_215;
x_17 = x_207;
x_18 = x_206;
x_19 = x_235;
goto block_160;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_ctor_get(x_229, 0);
x_237 = lean_ctor_get(x_229, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_229);
x_238 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_239 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_236);
lean_ctor_set_tag(x_222, 7);
lean_ctor_set(x_222, 1, x_238);
lean_ctor_set(x_222, 0, x_239);
x_240 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_221, x_222, x_210, x_215, x_207, x_206, x_237);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_11 = x_214;
x_12 = x_208;
x_13 = x_213;
x_14 = x_205;
x_15 = x_210;
x_16 = x_215;
x_17 = x_207;
x_18 = x_206;
x_19 = x_241;
goto block_160;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_242 = lean_ctor_get(x_222, 1);
lean_inc(x_242);
lean_dec(x_222);
lean_inc(x_213);
x_243 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_213, x_205, x_242);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_246 = x_243;
} else {
 lean_dec_ref(x_243);
 x_246 = lean_box(0);
}
x_247 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_246)) {
 x_248 = lean_alloc_ctor(7, 2, 0);
} else {
 x_248 = x_246;
 lean_ctor_set_tag(x_248, 7);
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_244);
x_249 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_221, x_249, x_210, x_215, x_207, x_206, x_245);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec(x_250);
x_11 = x_214;
x_12 = x_208;
x_13 = x_213;
x_14 = x_205;
x_15 = x_210;
x_16 = x_215;
x_17 = x_207;
x_18 = x_206;
x_19 = x_251;
goto block_160;
}
}
}
else
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_214);
x_252 = lean_ctor_get(x_220, 0);
lean_inc(x_252);
lean_dec(x_220);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; 
lean_dec(x_253);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_208);
x_254 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_252, x_205, x_210, x_215, x_207, x_206, x_219);
lean_dec(x_206);
lean_dec(x_207);
lean_dec(x_215);
lean_dec(x_210);
lean_dec(x_205);
return x_254;
}
else
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_ctor_get(x_252, 0);
lean_inc(x_255);
x_256 = !lean_is_exclusive(x_253);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_257 = lean_ctor_get(x_253, 0);
x_258 = lean_ctor_get(x_253, 2);
x_259 = lean_ctor_get(x_253, 1);
lean_dec(x_259);
x_260 = lean_int_mul(x_216, x_255);
x_261 = lean_int_mul(x_257, x_209);
x_262 = l_Lean_Meta_Grind_Arith_gcdExt(x_260, x_261);
lean_dec(x_261);
lean_dec(x_260);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 0);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_ctor_get(x_263, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_263, 1);
lean_inc(x_266);
lean_dec(x_263);
x_267 = lean_st_ref_take(x_205, x_219);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_268, 14);
lean_inc(x_269);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_267, 1);
lean_inc(x_271);
lean_dec(x_267);
x_272 = !lean_is_exclusive(x_268);
if (x_272 == 0)
{
lean_object* x_273; uint8_t x_274; 
x_273 = lean_ctor_get(x_268, 14);
lean_dec(x_273);
x_274 = !lean_is_exclusive(x_269);
if (x_274 == 0)
{
lean_object* x_275; uint8_t x_276; 
x_275 = lean_ctor_get(x_269, 1);
lean_dec(x_275);
x_276 = !lean_is_exclusive(x_270);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_277 = lean_ctor_get(x_270, 7);
x_278 = lean_box(0);
x_279 = l_Lean_PersistentArray_set___redArg(x_277, x_208, x_278);
lean_ctor_set(x_270, 7, x_279);
x_280 = lean_st_ref_set(x_205, x_268, x_271);
x_281 = !lean_is_exclusive(x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_282 = lean_ctor_get(x_280, 1);
x_283 = lean_ctor_get(x_280, 0);
lean_dec(x_283);
x_284 = lean_int_mul(x_265, x_255);
lean_dec(x_265);
lean_inc(x_217);
x_285 = l_Int_Linear_Poly_mul(x_217, x_284);
lean_dec(x_284);
x_286 = lean_int_mul(x_266, x_209);
lean_dec(x_266);
lean_inc(x_258);
x_287 = l_Int_Linear_Poly_mul(x_258, x_286);
lean_dec(x_286);
x_288 = lean_int_mul(x_209, x_255);
lean_dec(x_255);
lean_dec(x_209);
x_289 = l_Int_Linear_Poly_combine(x_285, x_287);
lean_inc(x_264);
lean_ctor_set(x_253, 2, x_289);
lean_ctor_set(x_253, 1, x_208);
lean_ctor_set(x_253, 0, x_264);
lean_inc(x_252);
lean_inc(x_213);
lean_ctor_set_tag(x_280, 4);
lean_ctor_set(x_280, 1, x_252);
lean_ctor_set(x_280, 0, x_213);
x_290 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_253);
lean_ctor_set(x_290, 2, x_280);
lean_inc(x_206);
lean_inc(x_207);
lean_inc(x_215);
lean_inc(x_210);
lean_inc(x_218);
lean_inc(x_211);
lean_inc(x_212);
lean_inc(x_205);
x_291 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_290, x_205, x_212, x_211, x_218, x_210, x_215, x_207, x_206, x_282);
if (lean_obj_tag(x_291) == 0)
{
uint8_t x_292; 
x_292 = !lean_is_exclusive(x_291);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_293 = lean_ctor_get(x_291, 1);
x_294 = lean_ctor_get(x_291, 0);
lean_dec(x_294);
x_295 = l_Int_Linear_Poly_mul(x_217, x_257);
lean_dec(x_257);
x_296 = lean_int_neg(x_216);
lean_dec(x_216);
x_297 = l_Int_Linear_Poly_mul(x_258, x_296);
lean_dec(x_296);
x_298 = l_Int_Linear_Poly_combine(x_295, x_297);
lean_inc(x_252);
lean_ctor_set_tag(x_291, 5);
lean_ctor_set(x_291, 1, x_252);
lean_ctor_set(x_291, 0, x_213);
x_299 = !lean_is_exclusive(x_252);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_252, 2);
lean_dec(x_300);
x_301 = lean_ctor_get(x_252, 1);
lean_dec(x_301);
x_302 = lean_ctor_get(x_252, 0);
lean_dec(x_302);
lean_ctor_set(x_252, 2, x_291);
lean_ctor_set(x_252, 1, x_298);
lean_ctor_set(x_252, 0, x_264);
x_1 = x_252;
x_2 = x_205;
x_3 = x_212;
x_4 = x_211;
x_5 = x_218;
x_6 = x_210;
x_7 = x_215;
x_8 = x_207;
x_9 = x_206;
x_10 = x_293;
goto _start;
}
else
{
lean_object* x_304; 
lean_dec(x_252);
x_304 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_304, 0, x_264);
lean_ctor_set(x_304, 1, x_298);
lean_ctor_set(x_304, 2, x_291);
x_1 = x_304;
x_2 = x_205;
x_3 = x_212;
x_4 = x_211;
x_5 = x_218;
x_6 = x_210;
x_7 = x_215;
x_8 = x_207;
x_9 = x_206;
x_10 = x_293;
goto _start;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_306 = lean_ctor_get(x_291, 1);
lean_inc(x_306);
lean_dec(x_291);
x_307 = l_Int_Linear_Poly_mul(x_217, x_257);
lean_dec(x_257);
x_308 = lean_int_neg(x_216);
lean_dec(x_216);
x_309 = l_Int_Linear_Poly_mul(x_258, x_308);
lean_dec(x_308);
x_310 = l_Int_Linear_Poly_combine(x_307, x_309);
lean_inc(x_252);
x_311 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_311, 0, x_213);
lean_ctor_set(x_311, 1, x_252);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 lean_ctor_release(x_252, 2);
 x_312 = x_252;
} else {
 lean_dec_ref(x_252);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(0, 3, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_264);
lean_ctor_set(x_313, 1, x_310);
lean_ctor_set(x_313, 2, x_311);
x_1 = x_313;
x_2 = x_205;
x_3 = x_212;
x_4 = x_211;
x_5 = x_218;
x_6 = x_210;
x_7 = x_215;
x_8 = x_207;
x_9 = x_206;
x_10 = x_306;
goto _start;
}
}
else
{
lean_dec(x_264);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_252);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
return x_291;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_315 = lean_ctor_get(x_280, 1);
lean_inc(x_315);
lean_dec(x_280);
x_316 = lean_int_mul(x_265, x_255);
lean_dec(x_265);
lean_inc(x_217);
x_317 = l_Int_Linear_Poly_mul(x_217, x_316);
lean_dec(x_316);
x_318 = lean_int_mul(x_266, x_209);
lean_dec(x_266);
lean_inc(x_258);
x_319 = l_Int_Linear_Poly_mul(x_258, x_318);
lean_dec(x_318);
x_320 = lean_int_mul(x_209, x_255);
lean_dec(x_255);
lean_dec(x_209);
x_321 = l_Int_Linear_Poly_combine(x_317, x_319);
lean_inc(x_264);
lean_ctor_set(x_253, 2, x_321);
lean_ctor_set(x_253, 1, x_208);
lean_ctor_set(x_253, 0, x_264);
lean_inc(x_252);
lean_inc(x_213);
x_322 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_322, 0, x_213);
lean_ctor_set(x_322, 1, x_252);
x_323 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_253);
lean_ctor_set(x_323, 2, x_322);
lean_inc(x_206);
lean_inc(x_207);
lean_inc(x_215);
lean_inc(x_210);
lean_inc(x_218);
lean_inc(x_211);
lean_inc(x_212);
lean_inc(x_205);
x_324 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_323, x_205, x_212, x_211, x_218, x_210, x_215, x_207, x_206, x_315);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_325 = lean_ctor_get(x_324, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_326 = x_324;
} else {
 lean_dec_ref(x_324);
 x_326 = lean_box(0);
}
x_327 = l_Int_Linear_Poly_mul(x_217, x_257);
lean_dec(x_257);
x_328 = lean_int_neg(x_216);
lean_dec(x_216);
x_329 = l_Int_Linear_Poly_mul(x_258, x_328);
lean_dec(x_328);
x_330 = l_Int_Linear_Poly_combine(x_327, x_329);
lean_inc(x_252);
if (lean_is_scalar(x_326)) {
 x_331 = lean_alloc_ctor(5, 2, 0);
} else {
 x_331 = x_326;
 lean_ctor_set_tag(x_331, 5);
}
lean_ctor_set(x_331, 0, x_213);
lean_ctor_set(x_331, 1, x_252);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 lean_ctor_release(x_252, 2);
 x_332 = x_252;
} else {
 lean_dec_ref(x_252);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(0, 3, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_264);
lean_ctor_set(x_333, 1, x_330);
lean_ctor_set(x_333, 2, x_331);
x_1 = x_333;
x_2 = x_205;
x_3 = x_212;
x_4 = x_211;
x_5 = x_218;
x_6 = x_210;
x_7 = x_215;
x_8 = x_207;
x_9 = x_206;
x_10 = x_325;
goto _start;
}
else
{
lean_dec(x_264);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_252);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
return x_324;
}
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_335 = lean_ctor_get(x_270, 0);
x_336 = lean_ctor_get(x_270, 1);
x_337 = lean_ctor_get(x_270, 2);
x_338 = lean_ctor_get(x_270, 3);
x_339 = lean_ctor_get(x_270, 4);
x_340 = lean_ctor_get(x_270, 5);
x_341 = lean_ctor_get(x_270, 6);
x_342 = lean_ctor_get(x_270, 7);
x_343 = lean_ctor_get(x_270, 8);
x_344 = lean_ctor_get(x_270, 9);
x_345 = lean_ctor_get(x_270, 10);
x_346 = lean_ctor_get(x_270, 11);
x_347 = lean_ctor_get(x_270, 12);
x_348 = lean_ctor_get(x_270, 13);
x_349 = lean_ctor_get(x_270, 14);
x_350 = lean_ctor_get(x_270, 15);
x_351 = lean_ctor_get_uint8(x_270, sizeof(void*)*21);
x_352 = lean_ctor_get(x_270, 16);
x_353 = lean_ctor_get(x_270, 17);
x_354 = lean_ctor_get(x_270, 18);
x_355 = lean_ctor_get(x_270, 19);
x_356 = lean_ctor_get(x_270, 20);
lean_inc(x_356);
lean_inc(x_355);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_352);
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
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_270);
x_357 = lean_box(0);
x_358 = l_Lean_PersistentArray_set___redArg(x_342, x_208, x_357);
x_359 = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(x_359, 0, x_335);
lean_ctor_set(x_359, 1, x_336);
lean_ctor_set(x_359, 2, x_337);
lean_ctor_set(x_359, 3, x_338);
lean_ctor_set(x_359, 4, x_339);
lean_ctor_set(x_359, 5, x_340);
lean_ctor_set(x_359, 6, x_341);
lean_ctor_set(x_359, 7, x_358);
lean_ctor_set(x_359, 8, x_343);
lean_ctor_set(x_359, 9, x_344);
lean_ctor_set(x_359, 10, x_345);
lean_ctor_set(x_359, 11, x_346);
lean_ctor_set(x_359, 12, x_347);
lean_ctor_set(x_359, 13, x_348);
lean_ctor_set(x_359, 14, x_349);
lean_ctor_set(x_359, 15, x_350);
lean_ctor_set(x_359, 16, x_352);
lean_ctor_set(x_359, 17, x_353);
lean_ctor_set(x_359, 18, x_354);
lean_ctor_set(x_359, 19, x_355);
lean_ctor_set(x_359, 20, x_356);
lean_ctor_set_uint8(x_359, sizeof(void*)*21, x_351);
lean_ctor_set(x_269, 1, x_359);
x_360 = lean_st_ref_set(x_205, x_268, x_271);
x_361 = lean_ctor_get(x_360, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_362 = x_360;
} else {
 lean_dec_ref(x_360);
 x_362 = lean_box(0);
}
x_363 = lean_int_mul(x_265, x_255);
lean_dec(x_265);
lean_inc(x_217);
x_364 = l_Int_Linear_Poly_mul(x_217, x_363);
lean_dec(x_363);
x_365 = lean_int_mul(x_266, x_209);
lean_dec(x_266);
lean_inc(x_258);
x_366 = l_Int_Linear_Poly_mul(x_258, x_365);
lean_dec(x_365);
x_367 = lean_int_mul(x_209, x_255);
lean_dec(x_255);
lean_dec(x_209);
x_368 = l_Int_Linear_Poly_combine(x_364, x_366);
lean_inc(x_264);
lean_ctor_set(x_253, 2, x_368);
lean_ctor_set(x_253, 1, x_208);
lean_ctor_set(x_253, 0, x_264);
lean_inc(x_252);
lean_inc(x_213);
if (lean_is_scalar(x_362)) {
 x_369 = lean_alloc_ctor(4, 2, 0);
} else {
 x_369 = x_362;
 lean_ctor_set_tag(x_369, 4);
}
lean_ctor_set(x_369, 0, x_213);
lean_ctor_set(x_369, 1, x_252);
x_370 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_253);
lean_ctor_set(x_370, 2, x_369);
lean_inc(x_206);
lean_inc(x_207);
lean_inc(x_215);
lean_inc(x_210);
lean_inc(x_218);
lean_inc(x_211);
lean_inc(x_212);
lean_inc(x_205);
x_371 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_370, x_205, x_212, x_211, x_218, x_210, x_215, x_207, x_206, x_361);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
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
x_374 = l_Int_Linear_Poly_mul(x_217, x_257);
lean_dec(x_257);
x_375 = lean_int_neg(x_216);
lean_dec(x_216);
x_376 = l_Int_Linear_Poly_mul(x_258, x_375);
lean_dec(x_375);
x_377 = l_Int_Linear_Poly_combine(x_374, x_376);
lean_inc(x_252);
if (lean_is_scalar(x_373)) {
 x_378 = lean_alloc_ctor(5, 2, 0);
} else {
 x_378 = x_373;
 lean_ctor_set_tag(x_378, 5);
}
lean_ctor_set(x_378, 0, x_213);
lean_ctor_set(x_378, 1, x_252);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 lean_ctor_release(x_252, 2);
 x_379 = x_252;
} else {
 lean_dec_ref(x_252);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(0, 3, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_264);
lean_ctor_set(x_380, 1, x_377);
lean_ctor_set(x_380, 2, x_378);
x_1 = x_380;
x_2 = x_205;
x_3 = x_212;
x_4 = x_211;
x_5 = x_218;
x_6 = x_210;
x_7 = x_215;
x_8 = x_207;
x_9 = x_206;
x_10 = x_372;
goto _start;
}
else
{
lean_dec(x_264);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_252);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
return x_371;
}
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_382 = lean_ctor_get(x_269, 0);
x_383 = lean_ctor_get(x_269, 2);
x_384 = lean_ctor_get(x_269, 3);
lean_inc(x_384);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_269);
x_385 = lean_ctor_get(x_270, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_270, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_270, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_270, 3);
lean_inc(x_388);
x_389 = lean_ctor_get(x_270, 4);
lean_inc(x_389);
x_390 = lean_ctor_get(x_270, 5);
lean_inc(x_390);
x_391 = lean_ctor_get(x_270, 6);
lean_inc(x_391);
x_392 = lean_ctor_get(x_270, 7);
lean_inc(x_392);
x_393 = lean_ctor_get(x_270, 8);
lean_inc(x_393);
x_394 = lean_ctor_get(x_270, 9);
lean_inc(x_394);
x_395 = lean_ctor_get(x_270, 10);
lean_inc(x_395);
x_396 = lean_ctor_get(x_270, 11);
lean_inc(x_396);
x_397 = lean_ctor_get(x_270, 12);
lean_inc(x_397);
x_398 = lean_ctor_get(x_270, 13);
lean_inc(x_398);
x_399 = lean_ctor_get(x_270, 14);
lean_inc(x_399);
x_400 = lean_ctor_get(x_270, 15);
lean_inc(x_400);
x_401 = lean_ctor_get_uint8(x_270, sizeof(void*)*21);
x_402 = lean_ctor_get(x_270, 16);
lean_inc(x_402);
x_403 = lean_ctor_get(x_270, 17);
lean_inc(x_403);
x_404 = lean_ctor_get(x_270, 18);
lean_inc(x_404);
x_405 = lean_ctor_get(x_270, 19);
lean_inc(x_405);
x_406 = lean_ctor_get(x_270, 20);
lean_inc(x_406);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 lean_ctor_release(x_270, 2);
 lean_ctor_release(x_270, 3);
 lean_ctor_release(x_270, 4);
 lean_ctor_release(x_270, 5);
 lean_ctor_release(x_270, 6);
 lean_ctor_release(x_270, 7);
 lean_ctor_release(x_270, 8);
 lean_ctor_release(x_270, 9);
 lean_ctor_release(x_270, 10);
 lean_ctor_release(x_270, 11);
 lean_ctor_release(x_270, 12);
 lean_ctor_release(x_270, 13);
 lean_ctor_release(x_270, 14);
 lean_ctor_release(x_270, 15);
 lean_ctor_release(x_270, 16);
 lean_ctor_release(x_270, 17);
 lean_ctor_release(x_270, 18);
 lean_ctor_release(x_270, 19);
 lean_ctor_release(x_270, 20);
 x_407 = x_270;
} else {
 lean_dec_ref(x_270);
 x_407 = lean_box(0);
}
x_408 = lean_box(0);
x_409 = l_Lean_PersistentArray_set___redArg(x_392, x_208, x_408);
if (lean_is_scalar(x_407)) {
 x_410 = lean_alloc_ctor(0, 21, 1);
} else {
 x_410 = x_407;
}
lean_ctor_set(x_410, 0, x_385);
lean_ctor_set(x_410, 1, x_386);
lean_ctor_set(x_410, 2, x_387);
lean_ctor_set(x_410, 3, x_388);
lean_ctor_set(x_410, 4, x_389);
lean_ctor_set(x_410, 5, x_390);
lean_ctor_set(x_410, 6, x_391);
lean_ctor_set(x_410, 7, x_409);
lean_ctor_set(x_410, 8, x_393);
lean_ctor_set(x_410, 9, x_394);
lean_ctor_set(x_410, 10, x_395);
lean_ctor_set(x_410, 11, x_396);
lean_ctor_set(x_410, 12, x_397);
lean_ctor_set(x_410, 13, x_398);
lean_ctor_set(x_410, 14, x_399);
lean_ctor_set(x_410, 15, x_400);
lean_ctor_set(x_410, 16, x_402);
lean_ctor_set(x_410, 17, x_403);
lean_ctor_set(x_410, 18, x_404);
lean_ctor_set(x_410, 19, x_405);
lean_ctor_set(x_410, 20, x_406);
lean_ctor_set_uint8(x_410, sizeof(void*)*21, x_401);
x_411 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_411, 0, x_382);
lean_ctor_set(x_411, 1, x_410);
lean_ctor_set(x_411, 2, x_383);
lean_ctor_set(x_411, 3, x_384);
lean_ctor_set(x_268, 14, x_411);
x_412 = lean_st_ref_set(x_205, x_268, x_271);
x_413 = lean_ctor_get(x_412, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_414 = x_412;
} else {
 lean_dec_ref(x_412);
 x_414 = lean_box(0);
}
x_415 = lean_int_mul(x_265, x_255);
lean_dec(x_265);
lean_inc(x_217);
x_416 = l_Int_Linear_Poly_mul(x_217, x_415);
lean_dec(x_415);
x_417 = lean_int_mul(x_266, x_209);
lean_dec(x_266);
lean_inc(x_258);
x_418 = l_Int_Linear_Poly_mul(x_258, x_417);
lean_dec(x_417);
x_419 = lean_int_mul(x_209, x_255);
lean_dec(x_255);
lean_dec(x_209);
x_420 = l_Int_Linear_Poly_combine(x_416, x_418);
lean_inc(x_264);
lean_ctor_set(x_253, 2, x_420);
lean_ctor_set(x_253, 1, x_208);
lean_ctor_set(x_253, 0, x_264);
lean_inc(x_252);
lean_inc(x_213);
if (lean_is_scalar(x_414)) {
 x_421 = lean_alloc_ctor(4, 2, 0);
} else {
 x_421 = x_414;
 lean_ctor_set_tag(x_421, 4);
}
lean_ctor_set(x_421, 0, x_213);
lean_ctor_set(x_421, 1, x_252);
x_422 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_253);
lean_ctor_set(x_422, 2, x_421);
lean_inc(x_206);
lean_inc(x_207);
lean_inc(x_215);
lean_inc(x_210);
lean_inc(x_218);
lean_inc(x_211);
lean_inc(x_212);
lean_inc(x_205);
x_423 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_422, x_205, x_212, x_211, x_218, x_210, x_215, x_207, x_206, x_413);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_425 = x_423;
} else {
 lean_dec_ref(x_423);
 x_425 = lean_box(0);
}
x_426 = l_Int_Linear_Poly_mul(x_217, x_257);
lean_dec(x_257);
x_427 = lean_int_neg(x_216);
lean_dec(x_216);
x_428 = l_Int_Linear_Poly_mul(x_258, x_427);
lean_dec(x_427);
x_429 = l_Int_Linear_Poly_combine(x_426, x_428);
lean_inc(x_252);
if (lean_is_scalar(x_425)) {
 x_430 = lean_alloc_ctor(5, 2, 0);
} else {
 x_430 = x_425;
 lean_ctor_set_tag(x_430, 5);
}
lean_ctor_set(x_430, 0, x_213);
lean_ctor_set(x_430, 1, x_252);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 lean_ctor_release(x_252, 2);
 x_431 = x_252;
} else {
 lean_dec_ref(x_252);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(0, 3, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_264);
lean_ctor_set(x_432, 1, x_429);
lean_ctor_set(x_432, 2, x_430);
x_1 = x_432;
x_2 = x_205;
x_3 = x_212;
x_4 = x_211;
x_5 = x_218;
x_6 = x_210;
x_7 = x_215;
x_8 = x_207;
x_9 = x_206;
x_10 = x_424;
goto _start;
}
else
{
lean_dec(x_264);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_252);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
return x_423;
}
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_434 = lean_ctor_get(x_268, 0);
x_435 = lean_ctor_get(x_268, 1);
x_436 = lean_ctor_get(x_268, 2);
x_437 = lean_ctor_get(x_268, 3);
x_438 = lean_ctor_get(x_268, 4);
x_439 = lean_ctor_get(x_268, 5);
x_440 = lean_ctor_get(x_268, 6);
x_441 = lean_ctor_get(x_268, 7);
x_442 = lean_ctor_get_uint8(x_268, sizeof(void*)*16);
x_443 = lean_ctor_get(x_268, 8);
x_444 = lean_ctor_get(x_268, 9);
x_445 = lean_ctor_get(x_268, 10);
x_446 = lean_ctor_get(x_268, 11);
x_447 = lean_ctor_get(x_268, 12);
x_448 = lean_ctor_get(x_268, 13);
x_449 = lean_ctor_get(x_268, 15);
lean_inc(x_449);
lean_inc(x_448);
lean_inc(x_447);
lean_inc(x_446);
lean_inc(x_445);
lean_inc(x_444);
lean_inc(x_443);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
lean_inc(x_437);
lean_inc(x_436);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_268);
x_450 = lean_ctor_get(x_269, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_269, 2);
lean_inc(x_451);
x_452 = lean_ctor_get(x_269, 3);
lean_inc(x_452);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 lean_ctor_release(x_269, 2);
 lean_ctor_release(x_269, 3);
 x_453 = x_269;
} else {
 lean_dec_ref(x_269);
 x_453 = lean_box(0);
}
x_454 = lean_ctor_get(x_270, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_270, 1);
lean_inc(x_455);
x_456 = lean_ctor_get(x_270, 2);
lean_inc(x_456);
x_457 = lean_ctor_get(x_270, 3);
lean_inc(x_457);
x_458 = lean_ctor_get(x_270, 4);
lean_inc(x_458);
x_459 = lean_ctor_get(x_270, 5);
lean_inc(x_459);
x_460 = lean_ctor_get(x_270, 6);
lean_inc(x_460);
x_461 = lean_ctor_get(x_270, 7);
lean_inc(x_461);
x_462 = lean_ctor_get(x_270, 8);
lean_inc(x_462);
x_463 = lean_ctor_get(x_270, 9);
lean_inc(x_463);
x_464 = lean_ctor_get(x_270, 10);
lean_inc(x_464);
x_465 = lean_ctor_get(x_270, 11);
lean_inc(x_465);
x_466 = lean_ctor_get(x_270, 12);
lean_inc(x_466);
x_467 = lean_ctor_get(x_270, 13);
lean_inc(x_467);
x_468 = lean_ctor_get(x_270, 14);
lean_inc(x_468);
x_469 = lean_ctor_get(x_270, 15);
lean_inc(x_469);
x_470 = lean_ctor_get_uint8(x_270, sizeof(void*)*21);
x_471 = lean_ctor_get(x_270, 16);
lean_inc(x_471);
x_472 = lean_ctor_get(x_270, 17);
lean_inc(x_472);
x_473 = lean_ctor_get(x_270, 18);
lean_inc(x_473);
x_474 = lean_ctor_get(x_270, 19);
lean_inc(x_474);
x_475 = lean_ctor_get(x_270, 20);
lean_inc(x_475);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 lean_ctor_release(x_270, 2);
 lean_ctor_release(x_270, 3);
 lean_ctor_release(x_270, 4);
 lean_ctor_release(x_270, 5);
 lean_ctor_release(x_270, 6);
 lean_ctor_release(x_270, 7);
 lean_ctor_release(x_270, 8);
 lean_ctor_release(x_270, 9);
 lean_ctor_release(x_270, 10);
 lean_ctor_release(x_270, 11);
 lean_ctor_release(x_270, 12);
 lean_ctor_release(x_270, 13);
 lean_ctor_release(x_270, 14);
 lean_ctor_release(x_270, 15);
 lean_ctor_release(x_270, 16);
 lean_ctor_release(x_270, 17);
 lean_ctor_release(x_270, 18);
 lean_ctor_release(x_270, 19);
 lean_ctor_release(x_270, 20);
 x_476 = x_270;
} else {
 lean_dec_ref(x_270);
 x_476 = lean_box(0);
}
x_477 = lean_box(0);
x_478 = l_Lean_PersistentArray_set___redArg(x_461, x_208, x_477);
if (lean_is_scalar(x_476)) {
 x_479 = lean_alloc_ctor(0, 21, 1);
} else {
 x_479 = x_476;
}
lean_ctor_set(x_479, 0, x_454);
lean_ctor_set(x_479, 1, x_455);
lean_ctor_set(x_479, 2, x_456);
lean_ctor_set(x_479, 3, x_457);
lean_ctor_set(x_479, 4, x_458);
lean_ctor_set(x_479, 5, x_459);
lean_ctor_set(x_479, 6, x_460);
lean_ctor_set(x_479, 7, x_478);
lean_ctor_set(x_479, 8, x_462);
lean_ctor_set(x_479, 9, x_463);
lean_ctor_set(x_479, 10, x_464);
lean_ctor_set(x_479, 11, x_465);
lean_ctor_set(x_479, 12, x_466);
lean_ctor_set(x_479, 13, x_467);
lean_ctor_set(x_479, 14, x_468);
lean_ctor_set(x_479, 15, x_469);
lean_ctor_set(x_479, 16, x_471);
lean_ctor_set(x_479, 17, x_472);
lean_ctor_set(x_479, 18, x_473);
lean_ctor_set(x_479, 19, x_474);
lean_ctor_set(x_479, 20, x_475);
lean_ctor_set_uint8(x_479, sizeof(void*)*21, x_470);
if (lean_is_scalar(x_453)) {
 x_480 = lean_alloc_ctor(0, 4, 0);
} else {
 x_480 = x_453;
}
lean_ctor_set(x_480, 0, x_450);
lean_ctor_set(x_480, 1, x_479);
lean_ctor_set(x_480, 2, x_451);
lean_ctor_set(x_480, 3, x_452);
x_481 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_481, 0, x_434);
lean_ctor_set(x_481, 1, x_435);
lean_ctor_set(x_481, 2, x_436);
lean_ctor_set(x_481, 3, x_437);
lean_ctor_set(x_481, 4, x_438);
lean_ctor_set(x_481, 5, x_439);
lean_ctor_set(x_481, 6, x_440);
lean_ctor_set(x_481, 7, x_441);
lean_ctor_set(x_481, 8, x_443);
lean_ctor_set(x_481, 9, x_444);
lean_ctor_set(x_481, 10, x_445);
lean_ctor_set(x_481, 11, x_446);
lean_ctor_set(x_481, 12, x_447);
lean_ctor_set(x_481, 13, x_448);
lean_ctor_set(x_481, 14, x_480);
lean_ctor_set(x_481, 15, x_449);
lean_ctor_set_uint8(x_481, sizeof(void*)*16, x_442);
x_482 = lean_st_ref_set(x_205, x_481, x_271);
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_484 = x_482;
} else {
 lean_dec_ref(x_482);
 x_484 = lean_box(0);
}
x_485 = lean_int_mul(x_265, x_255);
lean_dec(x_265);
lean_inc(x_217);
x_486 = l_Int_Linear_Poly_mul(x_217, x_485);
lean_dec(x_485);
x_487 = lean_int_mul(x_266, x_209);
lean_dec(x_266);
lean_inc(x_258);
x_488 = l_Int_Linear_Poly_mul(x_258, x_487);
lean_dec(x_487);
x_489 = lean_int_mul(x_209, x_255);
lean_dec(x_255);
lean_dec(x_209);
x_490 = l_Int_Linear_Poly_combine(x_486, x_488);
lean_inc(x_264);
lean_ctor_set(x_253, 2, x_490);
lean_ctor_set(x_253, 1, x_208);
lean_ctor_set(x_253, 0, x_264);
lean_inc(x_252);
lean_inc(x_213);
if (lean_is_scalar(x_484)) {
 x_491 = lean_alloc_ctor(4, 2, 0);
} else {
 x_491 = x_484;
 lean_ctor_set_tag(x_491, 4);
}
lean_ctor_set(x_491, 0, x_213);
lean_ctor_set(x_491, 1, x_252);
x_492 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_253);
lean_ctor_set(x_492, 2, x_491);
lean_inc(x_206);
lean_inc(x_207);
lean_inc(x_215);
lean_inc(x_210);
lean_inc(x_218);
lean_inc(x_211);
lean_inc(x_212);
lean_inc(x_205);
x_493 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_492, x_205, x_212, x_211, x_218, x_210, x_215, x_207, x_206, x_483);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_494 = lean_ctor_get(x_493, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_495 = x_493;
} else {
 lean_dec_ref(x_493);
 x_495 = lean_box(0);
}
x_496 = l_Int_Linear_Poly_mul(x_217, x_257);
lean_dec(x_257);
x_497 = lean_int_neg(x_216);
lean_dec(x_216);
x_498 = l_Int_Linear_Poly_mul(x_258, x_497);
lean_dec(x_497);
x_499 = l_Int_Linear_Poly_combine(x_496, x_498);
lean_inc(x_252);
if (lean_is_scalar(x_495)) {
 x_500 = lean_alloc_ctor(5, 2, 0);
} else {
 x_500 = x_495;
 lean_ctor_set_tag(x_500, 5);
}
lean_ctor_set(x_500, 0, x_213);
lean_ctor_set(x_500, 1, x_252);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 lean_ctor_release(x_252, 2);
 x_501 = x_252;
} else {
 lean_dec_ref(x_252);
 x_501 = lean_box(0);
}
if (lean_is_scalar(x_501)) {
 x_502 = lean_alloc_ctor(0, 3, 0);
} else {
 x_502 = x_501;
}
lean_ctor_set(x_502, 0, x_264);
lean_ctor_set(x_502, 1, x_499);
lean_ctor_set(x_502, 2, x_500);
x_1 = x_502;
x_2 = x_205;
x_3 = x_212;
x_4 = x_211;
x_5 = x_218;
x_6 = x_210;
x_7 = x_215;
x_8 = x_207;
x_9 = x_206;
x_10 = x_494;
goto _start;
}
else
{
lean_dec(x_264);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_252);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
return x_493;
}
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; uint8_t x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_504 = lean_ctor_get(x_253, 0);
x_505 = lean_ctor_get(x_253, 2);
lean_inc(x_505);
lean_inc(x_504);
lean_dec(x_253);
x_506 = lean_int_mul(x_216, x_255);
x_507 = lean_int_mul(x_504, x_209);
x_508 = l_Lean_Meta_Grind_Arith_gcdExt(x_506, x_507);
lean_dec(x_507);
lean_dec(x_506);
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 0);
lean_inc(x_510);
lean_dec(x_508);
x_511 = lean_ctor_get(x_509, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_509, 1);
lean_inc(x_512);
lean_dec(x_509);
x_513 = lean_st_ref_take(x_205, x_219);
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_514, 14);
lean_inc(x_515);
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
x_517 = lean_ctor_get(x_513, 1);
lean_inc(x_517);
lean_dec(x_513);
x_518 = lean_ctor_get(x_514, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_514, 1);
lean_inc(x_519);
x_520 = lean_ctor_get(x_514, 2);
lean_inc(x_520);
x_521 = lean_ctor_get(x_514, 3);
lean_inc(x_521);
x_522 = lean_ctor_get(x_514, 4);
lean_inc(x_522);
x_523 = lean_ctor_get(x_514, 5);
lean_inc(x_523);
x_524 = lean_ctor_get(x_514, 6);
lean_inc(x_524);
x_525 = lean_ctor_get(x_514, 7);
lean_inc(x_525);
x_526 = lean_ctor_get_uint8(x_514, sizeof(void*)*16);
x_527 = lean_ctor_get(x_514, 8);
lean_inc(x_527);
x_528 = lean_ctor_get(x_514, 9);
lean_inc(x_528);
x_529 = lean_ctor_get(x_514, 10);
lean_inc(x_529);
x_530 = lean_ctor_get(x_514, 11);
lean_inc(x_530);
x_531 = lean_ctor_get(x_514, 12);
lean_inc(x_531);
x_532 = lean_ctor_get(x_514, 13);
lean_inc(x_532);
x_533 = lean_ctor_get(x_514, 15);
lean_inc(x_533);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 lean_ctor_release(x_514, 1);
 lean_ctor_release(x_514, 2);
 lean_ctor_release(x_514, 3);
 lean_ctor_release(x_514, 4);
 lean_ctor_release(x_514, 5);
 lean_ctor_release(x_514, 6);
 lean_ctor_release(x_514, 7);
 lean_ctor_release(x_514, 8);
 lean_ctor_release(x_514, 9);
 lean_ctor_release(x_514, 10);
 lean_ctor_release(x_514, 11);
 lean_ctor_release(x_514, 12);
 lean_ctor_release(x_514, 13);
 lean_ctor_release(x_514, 14);
 lean_ctor_release(x_514, 15);
 x_534 = x_514;
} else {
 lean_dec_ref(x_514);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_515, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_515, 2);
lean_inc(x_536);
x_537 = lean_ctor_get(x_515, 3);
lean_inc(x_537);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 lean_ctor_release(x_515, 1);
 lean_ctor_release(x_515, 2);
 lean_ctor_release(x_515, 3);
 x_538 = x_515;
} else {
 lean_dec_ref(x_515);
 x_538 = lean_box(0);
}
x_539 = lean_ctor_get(x_516, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_516, 1);
lean_inc(x_540);
x_541 = lean_ctor_get(x_516, 2);
lean_inc(x_541);
x_542 = lean_ctor_get(x_516, 3);
lean_inc(x_542);
x_543 = lean_ctor_get(x_516, 4);
lean_inc(x_543);
x_544 = lean_ctor_get(x_516, 5);
lean_inc(x_544);
x_545 = lean_ctor_get(x_516, 6);
lean_inc(x_545);
x_546 = lean_ctor_get(x_516, 7);
lean_inc(x_546);
x_547 = lean_ctor_get(x_516, 8);
lean_inc(x_547);
x_548 = lean_ctor_get(x_516, 9);
lean_inc(x_548);
x_549 = lean_ctor_get(x_516, 10);
lean_inc(x_549);
x_550 = lean_ctor_get(x_516, 11);
lean_inc(x_550);
x_551 = lean_ctor_get(x_516, 12);
lean_inc(x_551);
x_552 = lean_ctor_get(x_516, 13);
lean_inc(x_552);
x_553 = lean_ctor_get(x_516, 14);
lean_inc(x_553);
x_554 = lean_ctor_get(x_516, 15);
lean_inc(x_554);
x_555 = lean_ctor_get_uint8(x_516, sizeof(void*)*21);
x_556 = lean_ctor_get(x_516, 16);
lean_inc(x_556);
x_557 = lean_ctor_get(x_516, 17);
lean_inc(x_557);
x_558 = lean_ctor_get(x_516, 18);
lean_inc(x_558);
x_559 = lean_ctor_get(x_516, 19);
lean_inc(x_559);
x_560 = lean_ctor_get(x_516, 20);
lean_inc(x_560);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 lean_ctor_release(x_516, 2);
 lean_ctor_release(x_516, 3);
 lean_ctor_release(x_516, 4);
 lean_ctor_release(x_516, 5);
 lean_ctor_release(x_516, 6);
 lean_ctor_release(x_516, 7);
 lean_ctor_release(x_516, 8);
 lean_ctor_release(x_516, 9);
 lean_ctor_release(x_516, 10);
 lean_ctor_release(x_516, 11);
 lean_ctor_release(x_516, 12);
 lean_ctor_release(x_516, 13);
 lean_ctor_release(x_516, 14);
 lean_ctor_release(x_516, 15);
 lean_ctor_release(x_516, 16);
 lean_ctor_release(x_516, 17);
 lean_ctor_release(x_516, 18);
 lean_ctor_release(x_516, 19);
 lean_ctor_release(x_516, 20);
 x_561 = x_516;
} else {
 lean_dec_ref(x_516);
 x_561 = lean_box(0);
}
x_562 = lean_box(0);
x_563 = l_Lean_PersistentArray_set___redArg(x_546, x_208, x_562);
if (lean_is_scalar(x_561)) {
 x_564 = lean_alloc_ctor(0, 21, 1);
} else {
 x_564 = x_561;
}
lean_ctor_set(x_564, 0, x_539);
lean_ctor_set(x_564, 1, x_540);
lean_ctor_set(x_564, 2, x_541);
lean_ctor_set(x_564, 3, x_542);
lean_ctor_set(x_564, 4, x_543);
lean_ctor_set(x_564, 5, x_544);
lean_ctor_set(x_564, 6, x_545);
lean_ctor_set(x_564, 7, x_563);
lean_ctor_set(x_564, 8, x_547);
lean_ctor_set(x_564, 9, x_548);
lean_ctor_set(x_564, 10, x_549);
lean_ctor_set(x_564, 11, x_550);
lean_ctor_set(x_564, 12, x_551);
lean_ctor_set(x_564, 13, x_552);
lean_ctor_set(x_564, 14, x_553);
lean_ctor_set(x_564, 15, x_554);
lean_ctor_set(x_564, 16, x_556);
lean_ctor_set(x_564, 17, x_557);
lean_ctor_set(x_564, 18, x_558);
lean_ctor_set(x_564, 19, x_559);
lean_ctor_set(x_564, 20, x_560);
lean_ctor_set_uint8(x_564, sizeof(void*)*21, x_555);
if (lean_is_scalar(x_538)) {
 x_565 = lean_alloc_ctor(0, 4, 0);
} else {
 x_565 = x_538;
}
lean_ctor_set(x_565, 0, x_535);
lean_ctor_set(x_565, 1, x_564);
lean_ctor_set(x_565, 2, x_536);
lean_ctor_set(x_565, 3, x_537);
if (lean_is_scalar(x_534)) {
 x_566 = lean_alloc_ctor(0, 16, 1);
} else {
 x_566 = x_534;
}
lean_ctor_set(x_566, 0, x_518);
lean_ctor_set(x_566, 1, x_519);
lean_ctor_set(x_566, 2, x_520);
lean_ctor_set(x_566, 3, x_521);
lean_ctor_set(x_566, 4, x_522);
lean_ctor_set(x_566, 5, x_523);
lean_ctor_set(x_566, 6, x_524);
lean_ctor_set(x_566, 7, x_525);
lean_ctor_set(x_566, 8, x_527);
lean_ctor_set(x_566, 9, x_528);
lean_ctor_set(x_566, 10, x_529);
lean_ctor_set(x_566, 11, x_530);
lean_ctor_set(x_566, 12, x_531);
lean_ctor_set(x_566, 13, x_532);
lean_ctor_set(x_566, 14, x_565);
lean_ctor_set(x_566, 15, x_533);
lean_ctor_set_uint8(x_566, sizeof(void*)*16, x_526);
x_567 = lean_st_ref_set(x_205, x_566, x_517);
x_568 = lean_ctor_get(x_567, 1);
lean_inc(x_568);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 x_569 = x_567;
} else {
 lean_dec_ref(x_567);
 x_569 = lean_box(0);
}
x_570 = lean_int_mul(x_511, x_255);
lean_dec(x_511);
lean_inc(x_217);
x_571 = l_Int_Linear_Poly_mul(x_217, x_570);
lean_dec(x_570);
x_572 = lean_int_mul(x_512, x_209);
lean_dec(x_512);
lean_inc(x_505);
x_573 = l_Int_Linear_Poly_mul(x_505, x_572);
lean_dec(x_572);
x_574 = lean_int_mul(x_209, x_255);
lean_dec(x_255);
lean_dec(x_209);
x_575 = l_Int_Linear_Poly_combine(x_571, x_573);
lean_inc(x_510);
x_576 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_576, 0, x_510);
lean_ctor_set(x_576, 1, x_208);
lean_ctor_set(x_576, 2, x_575);
lean_inc(x_252);
lean_inc(x_213);
if (lean_is_scalar(x_569)) {
 x_577 = lean_alloc_ctor(4, 2, 0);
} else {
 x_577 = x_569;
 lean_ctor_set_tag(x_577, 4);
}
lean_ctor_set(x_577, 0, x_213);
lean_ctor_set(x_577, 1, x_252);
x_578 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_578, 0, x_574);
lean_ctor_set(x_578, 1, x_576);
lean_ctor_set(x_578, 2, x_577);
lean_inc(x_206);
lean_inc(x_207);
lean_inc(x_215);
lean_inc(x_210);
lean_inc(x_218);
lean_inc(x_211);
lean_inc(x_212);
lean_inc(x_205);
x_579 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_578, x_205, x_212, x_211, x_218, x_210, x_215, x_207, x_206, x_568);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_580 = lean_ctor_get(x_579, 1);
lean_inc(x_580);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 lean_ctor_release(x_579, 1);
 x_581 = x_579;
} else {
 lean_dec_ref(x_579);
 x_581 = lean_box(0);
}
x_582 = l_Int_Linear_Poly_mul(x_217, x_504);
lean_dec(x_504);
x_583 = lean_int_neg(x_216);
lean_dec(x_216);
x_584 = l_Int_Linear_Poly_mul(x_505, x_583);
lean_dec(x_583);
x_585 = l_Int_Linear_Poly_combine(x_582, x_584);
lean_inc(x_252);
if (lean_is_scalar(x_581)) {
 x_586 = lean_alloc_ctor(5, 2, 0);
} else {
 x_586 = x_581;
 lean_ctor_set_tag(x_586, 5);
}
lean_ctor_set(x_586, 0, x_213);
lean_ctor_set(x_586, 1, x_252);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 lean_ctor_release(x_252, 2);
 x_587 = x_252;
} else {
 lean_dec_ref(x_252);
 x_587 = lean_box(0);
}
if (lean_is_scalar(x_587)) {
 x_588 = lean_alloc_ctor(0, 3, 0);
} else {
 x_588 = x_587;
}
lean_ctor_set(x_588, 0, x_510);
lean_ctor_set(x_588, 1, x_585);
lean_ctor_set(x_588, 2, x_586);
x_1 = x_588;
x_2 = x_205;
x_3 = x_212;
x_4 = x_211;
x_5 = x_218;
x_6 = x_210;
x_7 = x_215;
x_8 = x_207;
x_9 = x_206;
x_10 = x_580;
goto _start;
}
else
{
lean_dec(x_510);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_252);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
return x_579;
}
}
}
}
}
}
else
{
uint8_t x_836; 
lean_free_object(x_8);
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
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_836 = !lean_is_exclusive(x_199);
if (x_836 == 0)
{
lean_object* x_837; lean_object* x_838; 
x_837 = lean_ctor_get(x_199, 0);
lean_dec(x_837);
x_838 = lean_box(0);
lean_ctor_set(x_199, 0, x_838);
return x_199;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_839 = lean_ctor_get(x_199, 1);
lean_inc(x_839);
lean_dec(x_199);
x_840 = lean_box(0);
x_841 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_841, 0, x_840);
lean_ctor_set(x_841, 1, x_839);
return x_841;
}
}
}
else
{
lean_object* x_842; 
lean_free_object(x_8);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_842 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_190, x_10);
return x_842;
}
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; uint8_t x_854; lean_object* x_855; uint8_t x_856; lean_object* x_857; uint8_t x_858; 
x_843 = lean_ctor_get(x_8, 0);
x_844 = lean_ctor_get(x_8, 1);
x_845 = lean_ctor_get(x_8, 2);
x_846 = lean_ctor_get(x_8, 3);
x_847 = lean_ctor_get(x_8, 4);
x_848 = lean_ctor_get(x_8, 5);
x_849 = lean_ctor_get(x_8, 6);
x_850 = lean_ctor_get(x_8, 7);
x_851 = lean_ctor_get(x_8, 8);
x_852 = lean_ctor_get(x_8, 9);
x_853 = lean_ctor_get(x_8, 10);
x_854 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_855 = lean_ctor_get(x_8, 11);
x_856 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_857 = lean_ctor_get(x_8, 12);
lean_inc(x_857);
lean_inc(x_855);
lean_inc(x_853);
lean_inc(x_852);
lean_inc(x_851);
lean_inc(x_850);
lean_inc(x_849);
lean_inc(x_848);
lean_inc(x_847);
lean_inc(x_846);
lean_inc(x_845);
lean_inc(x_844);
lean_inc(x_843);
lean_dec(x_8);
x_858 = lean_nat_dec_eq(x_846, x_847);
if (x_858 == 0)
{
lean_object* x_859; lean_object* x_860; uint8_t x_861; 
x_859 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_860 = lean_ctor_get(x_859, 0);
lean_inc(x_860);
x_861 = lean_unbox(x_860);
lean_dec(x_860);
if (x_861 == 0)
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; uint8_t x_1087; 
x_862 = lean_ctor_get(x_859, 1);
lean_inc(x_862);
lean_dec(x_859);
x_863 = lean_unsigned_to_nat(1u);
x_864 = lean_nat_add(x_846, x_863);
lean_dec(x_846);
x_865 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_865, 0, x_843);
lean_ctor_set(x_865, 1, x_844);
lean_ctor_set(x_865, 2, x_845);
lean_ctor_set(x_865, 3, x_864);
lean_ctor_set(x_865, 4, x_847);
lean_ctor_set(x_865, 5, x_848);
lean_ctor_set(x_865, 6, x_849);
lean_ctor_set(x_865, 7, x_850);
lean_ctor_set(x_865, 8, x_851);
lean_ctor_set(x_865, 9, x_852);
lean_ctor_set(x_865, 10, x_853);
lean_ctor_set(x_865, 11, x_855);
lean_ctor_set(x_865, 12, x_857);
lean_ctor_set_uint8(x_865, sizeof(void*)*13, x_854);
lean_ctor_set_uint8(x_865, sizeof(void*)*13 + 1, x_856);
x_990 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_991 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_990, x_865, x_862);
x_992 = lean_ctor_get(x_991, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_991, 1);
lean_inc(x_993);
if (lean_is_exclusive(x_991)) {
 lean_ctor_release(x_991, 0);
 lean_ctor_release(x_991, 1);
 x_994 = x_991;
} else {
 lean_dec_ref(x_991);
 x_994 = lean_box(0);
}
x_995 = lean_box(0);
x_1087 = lean_unbox(x_992);
lean_dec(x_992);
if (x_1087 == 0)
{
lean_dec(x_994);
x_1020 = x_2;
x_1021 = x_3;
x_1022 = x_4;
x_1023 = x_5;
x_1024 = x_6;
x_1025 = x_7;
x_1026 = x_865;
x_1027 = x_9;
x_1028 = x_993;
goto block_1086;
}
else
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
lean_inc(x_1);
x_1088 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_993);
x_1089 = lean_ctor_get(x_1088, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_1088, 1);
lean_inc(x_1090);
if (lean_is_exclusive(x_1088)) {
 lean_ctor_release(x_1088, 0);
 lean_ctor_release(x_1088, 1);
 x_1091 = x_1088;
} else {
 lean_dec_ref(x_1088);
 x_1091 = lean_box(0);
}
x_1092 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1091)) {
 x_1093 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1093 = x_1091;
 lean_ctor_set_tag(x_1093, 7);
}
lean_ctor_set(x_1093, 0, x_1092);
lean_ctor_set(x_1093, 1, x_1089);
if (lean_is_scalar(x_994)) {
 x_1094 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1094 = x_994;
 lean_ctor_set_tag(x_1094, 7);
}
lean_ctor_set(x_1094, 0, x_1093);
lean_ctor_set(x_1094, 1, x_1092);
x_1095 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_990, x_1094, x_6, x_7, x_865, x_9, x_1090);
x_1096 = lean_ctor_get(x_1095, 1);
lean_inc(x_1096);
lean_dec(x_1095);
x_1020 = x_2;
x_1021 = x_3;
x_1022 = x_4;
x_1023 = x_5;
x_1024 = x_6;
x_1025 = x_7;
x_1026 = x_865;
x_1027 = x_9;
x_1028 = x_1096;
goto block_1086;
}
block_989:
{
if (lean_obj_tag(x_881) == 0)
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; uint8_t x_885; 
lean_dec(x_879);
lean_dec(x_878);
lean_dec(x_877);
lean_dec(x_873);
lean_dec(x_872);
lean_dec(x_870);
x_882 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_883 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_882, x_868, x_880);
x_884 = lean_ctor_get(x_883, 0);
lean_inc(x_884);
x_885 = lean_unbox(x_884);
lean_dec(x_884);
if (x_885 == 0)
{
lean_object* x_886; 
x_886 = lean_ctor_get(x_883, 1);
lean_inc(x_886);
lean_dec(x_883);
x_11 = x_875;
x_12 = x_869;
x_13 = x_874;
x_14 = x_866;
x_15 = x_871;
x_16 = x_876;
x_17 = x_868;
x_18 = x_867;
x_19 = x_886;
goto block_160;
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; 
x_887 = lean_ctor_get(x_883, 1);
lean_inc(x_887);
if (lean_is_exclusive(x_883)) {
 lean_ctor_release(x_883, 0);
 lean_ctor_release(x_883, 1);
 x_888 = x_883;
} else {
 lean_dec_ref(x_883);
 x_888 = lean_box(0);
}
lean_inc(x_874);
x_889 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_874, x_866, x_887);
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_889, 1);
lean_inc(x_891);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 lean_ctor_release(x_889, 1);
 x_892 = x_889;
} else {
 lean_dec_ref(x_889);
 x_892 = lean_box(0);
}
x_893 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_892)) {
 x_894 = lean_alloc_ctor(7, 2, 0);
} else {
 x_894 = x_892;
 lean_ctor_set_tag(x_894, 7);
}
lean_ctor_set(x_894, 0, x_893);
lean_ctor_set(x_894, 1, x_890);
if (lean_is_scalar(x_888)) {
 x_895 = lean_alloc_ctor(7, 2, 0);
} else {
 x_895 = x_888;
 lean_ctor_set_tag(x_895, 7);
}
lean_ctor_set(x_895, 0, x_894);
lean_ctor_set(x_895, 1, x_893);
x_896 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_882, x_895, x_871, x_876, x_868, x_867, x_891);
x_897 = lean_ctor_get(x_896, 1);
lean_inc(x_897);
lean_dec(x_896);
x_11 = x_875;
x_12 = x_869;
x_13 = x_874;
x_14 = x_866;
x_15 = x_871;
x_16 = x_876;
x_17 = x_868;
x_18 = x_867;
x_19 = x_897;
goto block_160;
}
}
else
{
lean_object* x_898; lean_object* x_899; 
lean_dec(x_875);
x_898 = lean_ctor_get(x_881, 0);
lean_inc(x_898);
lean_dec(x_881);
x_899 = lean_ctor_get(x_898, 1);
lean_inc(x_899);
if (lean_obj_tag(x_899) == 0)
{
lean_object* x_900; 
lean_dec(x_899);
lean_dec(x_879);
lean_dec(x_878);
lean_dec(x_877);
lean_dec(x_874);
lean_dec(x_873);
lean_dec(x_872);
lean_dec(x_870);
lean_dec(x_869);
x_900 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_898, x_866, x_871, x_876, x_868, x_867, x_880);
lean_dec(x_867);
lean_dec(x_868);
lean_dec(x_876);
lean_dec(x_871);
lean_dec(x_866);
return x_900;
}
else
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; uint8_t x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; uint8_t x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; 
x_901 = lean_ctor_get(x_898, 0);
lean_inc(x_901);
x_902 = lean_ctor_get(x_899, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_899, 2);
lean_inc(x_903);
if (lean_is_exclusive(x_899)) {
 lean_ctor_release(x_899, 0);
 lean_ctor_release(x_899, 1);
 lean_ctor_release(x_899, 2);
 x_904 = x_899;
} else {
 lean_dec_ref(x_899);
 x_904 = lean_box(0);
}
x_905 = lean_int_mul(x_877, x_901);
x_906 = lean_int_mul(x_902, x_870);
x_907 = l_Lean_Meta_Grind_Arith_gcdExt(x_905, x_906);
lean_dec(x_906);
lean_dec(x_905);
x_908 = lean_ctor_get(x_907, 1);
lean_inc(x_908);
x_909 = lean_ctor_get(x_907, 0);
lean_inc(x_909);
lean_dec(x_907);
x_910 = lean_ctor_get(x_908, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_908, 1);
lean_inc(x_911);
lean_dec(x_908);
x_912 = lean_st_ref_take(x_866, x_880);
x_913 = lean_ctor_get(x_912, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_913, 14);
lean_inc(x_914);
x_915 = lean_ctor_get(x_914, 1);
lean_inc(x_915);
x_916 = lean_ctor_get(x_912, 1);
lean_inc(x_916);
lean_dec(x_912);
x_917 = lean_ctor_get(x_913, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_913, 1);
lean_inc(x_918);
x_919 = lean_ctor_get(x_913, 2);
lean_inc(x_919);
x_920 = lean_ctor_get(x_913, 3);
lean_inc(x_920);
x_921 = lean_ctor_get(x_913, 4);
lean_inc(x_921);
x_922 = lean_ctor_get(x_913, 5);
lean_inc(x_922);
x_923 = lean_ctor_get(x_913, 6);
lean_inc(x_923);
x_924 = lean_ctor_get(x_913, 7);
lean_inc(x_924);
x_925 = lean_ctor_get_uint8(x_913, sizeof(void*)*16);
x_926 = lean_ctor_get(x_913, 8);
lean_inc(x_926);
x_927 = lean_ctor_get(x_913, 9);
lean_inc(x_927);
x_928 = lean_ctor_get(x_913, 10);
lean_inc(x_928);
x_929 = lean_ctor_get(x_913, 11);
lean_inc(x_929);
x_930 = lean_ctor_get(x_913, 12);
lean_inc(x_930);
x_931 = lean_ctor_get(x_913, 13);
lean_inc(x_931);
x_932 = lean_ctor_get(x_913, 15);
lean_inc(x_932);
if (lean_is_exclusive(x_913)) {
 lean_ctor_release(x_913, 0);
 lean_ctor_release(x_913, 1);
 lean_ctor_release(x_913, 2);
 lean_ctor_release(x_913, 3);
 lean_ctor_release(x_913, 4);
 lean_ctor_release(x_913, 5);
 lean_ctor_release(x_913, 6);
 lean_ctor_release(x_913, 7);
 lean_ctor_release(x_913, 8);
 lean_ctor_release(x_913, 9);
 lean_ctor_release(x_913, 10);
 lean_ctor_release(x_913, 11);
 lean_ctor_release(x_913, 12);
 lean_ctor_release(x_913, 13);
 lean_ctor_release(x_913, 14);
 lean_ctor_release(x_913, 15);
 x_933 = x_913;
} else {
 lean_dec_ref(x_913);
 x_933 = lean_box(0);
}
x_934 = lean_ctor_get(x_914, 0);
lean_inc(x_934);
x_935 = lean_ctor_get(x_914, 2);
lean_inc(x_935);
x_936 = lean_ctor_get(x_914, 3);
lean_inc(x_936);
if (lean_is_exclusive(x_914)) {
 lean_ctor_release(x_914, 0);
 lean_ctor_release(x_914, 1);
 lean_ctor_release(x_914, 2);
 lean_ctor_release(x_914, 3);
 x_937 = x_914;
} else {
 lean_dec_ref(x_914);
 x_937 = lean_box(0);
}
x_938 = lean_ctor_get(x_915, 0);
lean_inc(x_938);
x_939 = lean_ctor_get(x_915, 1);
lean_inc(x_939);
x_940 = lean_ctor_get(x_915, 2);
lean_inc(x_940);
x_941 = lean_ctor_get(x_915, 3);
lean_inc(x_941);
x_942 = lean_ctor_get(x_915, 4);
lean_inc(x_942);
x_943 = lean_ctor_get(x_915, 5);
lean_inc(x_943);
x_944 = lean_ctor_get(x_915, 6);
lean_inc(x_944);
x_945 = lean_ctor_get(x_915, 7);
lean_inc(x_945);
x_946 = lean_ctor_get(x_915, 8);
lean_inc(x_946);
x_947 = lean_ctor_get(x_915, 9);
lean_inc(x_947);
x_948 = lean_ctor_get(x_915, 10);
lean_inc(x_948);
x_949 = lean_ctor_get(x_915, 11);
lean_inc(x_949);
x_950 = lean_ctor_get(x_915, 12);
lean_inc(x_950);
x_951 = lean_ctor_get(x_915, 13);
lean_inc(x_951);
x_952 = lean_ctor_get(x_915, 14);
lean_inc(x_952);
x_953 = lean_ctor_get(x_915, 15);
lean_inc(x_953);
x_954 = lean_ctor_get_uint8(x_915, sizeof(void*)*21);
x_955 = lean_ctor_get(x_915, 16);
lean_inc(x_955);
x_956 = lean_ctor_get(x_915, 17);
lean_inc(x_956);
x_957 = lean_ctor_get(x_915, 18);
lean_inc(x_957);
x_958 = lean_ctor_get(x_915, 19);
lean_inc(x_958);
x_959 = lean_ctor_get(x_915, 20);
lean_inc(x_959);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 lean_ctor_release(x_915, 2);
 lean_ctor_release(x_915, 3);
 lean_ctor_release(x_915, 4);
 lean_ctor_release(x_915, 5);
 lean_ctor_release(x_915, 6);
 lean_ctor_release(x_915, 7);
 lean_ctor_release(x_915, 8);
 lean_ctor_release(x_915, 9);
 lean_ctor_release(x_915, 10);
 lean_ctor_release(x_915, 11);
 lean_ctor_release(x_915, 12);
 lean_ctor_release(x_915, 13);
 lean_ctor_release(x_915, 14);
 lean_ctor_release(x_915, 15);
 lean_ctor_release(x_915, 16);
 lean_ctor_release(x_915, 17);
 lean_ctor_release(x_915, 18);
 lean_ctor_release(x_915, 19);
 lean_ctor_release(x_915, 20);
 x_960 = x_915;
} else {
 lean_dec_ref(x_915);
 x_960 = lean_box(0);
}
x_961 = lean_box(0);
x_962 = l_Lean_PersistentArray_set___redArg(x_945, x_869, x_961);
if (lean_is_scalar(x_960)) {
 x_963 = lean_alloc_ctor(0, 21, 1);
} else {
 x_963 = x_960;
}
lean_ctor_set(x_963, 0, x_938);
lean_ctor_set(x_963, 1, x_939);
lean_ctor_set(x_963, 2, x_940);
lean_ctor_set(x_963, 3, x_941);
lean_ctor_set(x_963, 4, x_942);
lean_ctor_set(x_963, 5, x_943);
lean_ctor_set(x_963, 6, x_944);
lean_ctor_set(x_963, 7, x_962);
lean_ctor_set(x_963, 8, x_946);
lean_ctor_set(x_963, 9, x_947);
lean_ctor_set(x_963, 10, x_948);
lean_ctor_set(x_963, 11, x_949);
lean_ctor_set(x_963, 12, x_950);
lean_ctor_set(x_963, 13, x_951);
lean_ctor_set(x_963, 14, x_952);
lean_ctor_set(x_963, 15, x_953);
lean_ctor_set(x_963, 16, x_955);
lean_ctor_set(x_963, 17, x_956);
lean_ctor_set(x_963, 18, x_957);
lean_ctor_set(x_963, 19, x_958);
lean_ctor_set(x_963, 20, x_959);
lean_ctor_set_uint8(x_963, sizeof(void*)*21, x_954);
if (lean_is_scalar(x_937)) {
 x_964 = lean_alloc_ctor(0, 4, 0);
} else {
 x_964 = x_937;
}
lean_ctor_set(x_964, 0, x_934);
lean_ctor_set(x_964, 1, x_963);
lean_ctor_set(x_964, 2, x_935);
lean_ctor_set(x_964, 3, x_936);
if (lean_is_scalar(x_933)) {
 x_965 = lean_alloc_ctor(0, 16, 1);
} else {
 x_965 = x_933;
}
lean_ctor_set(x_965, 0, x_917);
lean_ctor_set(x_965, 1, x_918);
lean_ctor_set(x_965, 2, x_919);
lean_ctor_set(x_965, 3, x_920);
lean_ctor_set(x_965, 4, x_921);
lean_ctor_set(x_965, 5, x_922);
lean_ctor_set(x_965, 6, x_923);
lean_ctor_set(x_965, 7, x_924);
lean_ctor_set(x_965, 8, x_926);
lean_ctor_set(x_965, 9, x_927);
lean_ctor_set(x_965, 10, x_928);
lean_ctor_set(x_965, 11, x_929);
lean_ctor_set(x_965, 12, x_930);
lean_ctor_set(x_965, 13, x_931);
lean_ctor_set(x_965, 14, x_964);
lean_ctor_set(x_965, 15, x_932);
lean_ctor_set_uint8(x_965, sizeof(void*)*16, x_925);
x_966 = lean_st_ref_set(x_866, x_965, x_916);
x_967 = lean_ctor_get(x_966, 1);
lean_inc(x_967);
if (lean_is_exclusive(x_966)) {
 lean_ctor_release(x_966, 0);
 lean_ctor_release(x_966, 1);
 x_968 = x_966;
} else {
 lean_dec_ref(x_966);
 x_968 = lean_box(0);
}
x_969 = lean_int_mul(x_910, x_901);
lean_dec(x_910);
lean_inc(x_878);
x_970 = l_Int_Linear_Poly_mul(x_878, x_969);
lean_dec(x_969);
x_971 = lean_int_mul(x_911, x_870);
lean_dec(x_911);
lean_inc(x_903);
x_972 = l_Int_Linear_Poly_mul(x_903, x_971);
lean_dec(x_971);
x_973 = lean_int_mul(x_870, x_901);
lean_dec(x_901);
lean_dec(x_870);
x_974 = l_Int_Linear_Poly_combine(x_970, x_972);
lean_inc(x_909);
if (lean_is_scalar(x_904)) {
 x_975 = lean_alloc_ctor(1, 3, 0);
} else {
 x_975 = x_904;
}
lean_ctor_set(x_975, 0, x_909);
lean_ctor_set(x_975, 1, x_869);
lean_ctor_set(x_975, 2, x_974);
lean_inc(x_898);
lean_inc(x_874);
if (lean_is_scalar(x_968)) {
 x_976 = lean_alloc_ctor(4, 2, 0);
} else {
 x_976 = x_968;
 lean_ctor_set_tag(x_976, 4);
}
lean_ctor_set(x_976, 0, x_874);
lean_ctor_set(x_976, 1, x_898);
x_977 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_977, 0, x_973);
lean_ctor_set(x_977, 1, x_975);
lean_ctor_set(x_977, 2, x_976);
lean_inc(x_867);
lean_inc(x_868);
lean_inc(x_876);
lean_inc(x_871);
lean_inc(x_879);
lean_inc(x_872);
lean_inc(x_873);
lean_inc(x_866);
x_978 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_977, x_866, x_873, x_872, x_879, x_871, x_876, x_868, x_867, x_967);
if (lean_obj_tag(x_978) == 0)
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_979 = lean_ctor_get(x_978, 1);
lean_inc(x_979);
if (lean_is_exclusive(x_978)) {
 lean_ctor_release(x_978, 0);
 lean_ctor_release(x_978, 1);
 x_980 = x_978;
} else {
 lean_dec_ref(x_978);
 x_980 = lean_box(0);
}
x_981 = l_Int_Linear_Poly_mul(x_878, x_902);
lean_dec(x_902);
x_982 = lean_int_neg(x_877);
lean_dec(x_877);
x_983 = l_Int_Linear_Poly_mul(x_903, x_982);
lean_dec(x_982);
x_984 = l_Int_Linear_Poly_combine(x_981, x_983);
lean_inc(x_898);
if (lean_is_scalar(x_980)) {
 x_985 = lean_alloc_ctor(5, 2, 0);
} else {
 x_985 = x_980;
 lean_ctor_set_tag(x_985, 5);
}
lean_ctor_set(x_985, 0, x_874);
lean_ctor_set(x_985, 1, x_898);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 lean_ctor_release(x_898, 2);
 x_986 = x_898;
} else {
 lean_dec_ref(x_898);
 x_986 = lean_box(0);
}
if (lean_is_scalar(x_986)) {
 x_987 = lean_alloc_ctor(0, 3, 0);
} else {
 x_987 = x_986;
}
lean_ctor_set(x_987, 0, x_909);
lean_ctor_set(x_987, 1, x_984);
lean_ctor_set(x_987, 2, x_985);
x_1 = x_987;
x_2 = x_866;
x_3 = x_873;
x_4 = x_872;
x_5 = x_879;
x_6 = x_871;
x_7 = x_876;
x_8 = x_868;
x_9 = x_867;
x_10 = x_979;
goto _start;
}
else
{
lean_dec(x_909);
lean_dec(x_903);
lean_dec(x_902);
lean_dec(x_898);
lean_dec(x_879);
lean_dec(x_878);
lean_dec(x_877);
lean_dec(x_876);
lean_dec(x_874);
lean_dec(x_873);
lean_dec(x_872);
lean_dec(x_871);
lean_dec(x_868);
lean_dec(x_867);
lean_dec(x_866);
return x_978;
}
}
}
}
block_1019:
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; uint8_t x_1016; 
x_1011 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_1002, x_1010);
x_1012 = lean_ctor_get(x_1011, 0);
lean_inc(x_1012);
x_1013 = lean_ctor_get(x_1012, 7);
lean_inc(x_1013);
lean_dec(x_1012);
x_1014 = lean_ctor_get(x_1011, 1);
lean_inc(x_1014);
lean_dec(x_1011);
x_1015 = lean_ctor_get(x_1013, 2);
lean_inc(x_1015);
x_1016 = lean_nat_dec_lt(x_1000, x_1015);
lean_dec(x_1015);
if (x_1016 == 0)
{
lean_object* x_1017; 
lean_dec(x_1013);
x_1017 = l_outOfBounds___redArg(x_995);
x_866 = x_1002;
x_867 = x_1009;
x_868 = x_1008;
x_869 = x_1000;
x_870 = x_999;
x_871 = x_1006;
x_872 = x_1004;
x_873 = x_1003;
x_874 = x_1001;
x_875 = x_996;
x_876 = x_1007;
x_877 = x_997;
x_878 = x_998;
x_879 = x_1005;
x_880 = x_1014;
x_881 = x_1017;
goto block_989;
}
else
{
lean_object* x_1018; 
x_1018 = l_Lean_PersistentArray_get_x21___redArg(x_995, x_1013, x_1000);
x_866 = x_1002;
x_867 = x_1009;
x_868 = x_1008;
x_869 = x_1000;
x_870 = x_999;
x_871 = x_1006;
x_872 = x_1004;
x_873 = x_1003;
x_874 = x_1001;
x_875 = x_996;
x_876 = x_1007;
x_877 = x_997;
x_878 = x_998;
x_879 = x_1005;
x_880 = x_1014;
x_881 = x_1018;
goto block_989;
}
}
block_1086:
{
lean_object* x_1029; lean_object* x_1030; 
x_1029 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_1026);
x_1030 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_1029, x_1020, x_1024, x_1025, x_1026, x_1027, x_1028);
if (lean_obj_tag(x_1030) == 0)
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; uint8_t x_1035; 
x_1031 = lean_ctor_get(x_1030, 0);
lean_inc(x_1031);
x_1032 = lean_ctor_get(x_1030, 1);
lean_inc(x_1032);
lean_dec(x_1030);
x_1033 = lean_ctor_get(x_1031, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1031, 1);
lean_inc(x_1034);
lean_inc(x_1033);
x_1035 = l_Int_Linear_Poly_isUnsatDvd(x_1033, x_1034);
if (x_1035 == 0)
{
uint8_t x_1036; 
x_1036 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_1031);
if (x_1036 == 0)
{
if (lean_obj_tag(x_1034) == 0)
{
lean_object* x_1037; 
lean_dec(x_1034);
lean_dec(x_1033);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
x_1037 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_1031, x_1020, x_1024, x_1025, x_1026, x_1027, x_1032);
lean_dec(x_1027);
lean_dec(x_1026);
lean_dec(x_1025);
lean_dec(x_1024);
lean_dec(x_1020);
return x_1037;
}
else
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; uint8_t x_1045; uint8_t x_1046; uint8_t x_1047; 
x_1038 = lean_ctor_get(x_1034, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1034, 1);
lean_inc(x_1039);
x_1040 = lean_ctor_get(x_1034, 2);
lean_inc(x_1040);
lean_inc(x_1031);
x_1041 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_1031, x_1020, x_1032);
x_1042 = lean_ctor_get(x_1041, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1041, 1);
lean_inc(x_1043);
lean_dec(x_1041);
x_1044 = lean_box(0);
x_1045 = lean_unbox(x_1042);
lean_dec(x_1042);
x_1046 = lean_unbox(x_1044);
x_1047 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_1045, x_1046);
if (x_1047 == 0)
{
x_996 = x_1034;
x_997 = x_1038;
x_998 = x_1040;
x_999 = x_1033;
x_1000 = x_1039;
x_1001 = x_1031;
x_1002 = x_1020;
x_1003 = x_1021;
x_1004 = x_1022;
x_1005 = x_1023;
x_1006 = x_1024;
x_1007 = x_1025;
x_1008 = x_1026;
x_1009 = x_1027;
x_1010 = x_1043;
goto block_1019;
}
else
{
lean_object* x_1048; lean_object* x_1049; 
x_1048 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_1039, x_1020, x_1043);
x_1049 = lean_ctor_get(x_1048, 1);
lean_inc(x_1049);
lean_dec(x_1048);
x_996 = x_1034;
x_997 = x_1038;
x_998 = x_1040;
x_999 = x_1033;
x_1000 = x_1039;
x_1001 = x_1031;
x_1002 = x_1020;
x_1003 = x_1021;
x_1004 = x_1022;
x_1005 = x_1023;
x_1006 = x_1024;
x_1007 = x_1025;
x_1008 = x_1026;
x_1009 = x_1027;
x_1010 = x_1049;
goto block_1019;
}
}
}
else
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; uint8_t x_1053; 
lean_dec(x_1034);
lean_dec(x_1033);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
x_1050 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_1051 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1050, x_1026, x_1032);
x_1052 = lean_ctor_get(x_1051, 0);
lean_inc(x_1052);
x_1053 = lean_unbox(x_1052);
lean_dec(x_1052);
if (x_1053 == 0)
{
lean_object* x_1054; 
lean_dec(x_1031);
lean_dec(x_1027);
lean_dec(x_1026);
lean_dec(x_1025);
lean_dec(x_1024);
lean_dec(x_1020);
x_1054 = lean_ctor_get(x_1051, 1);
lean_inc(x_1054);
lean_dec(x_1051);
x_180 = x_1054;
goto block_183;
}
else
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
x_1055 = lean_ctor_get(x_1051, 1);
lean_inc(x_1055);
if (lean_is_exclusive(x_1051)) {
 lean_ctor_release(x_1051, 0);
 lean_ctor_release(x_1051, 1);
 x_1056 = x_1051;
} else {
 lean_dec_ref(x_1051);
 x_1056 = lean_box(0);
}
x_1057 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1031, x_1020, x_1055);
lean_dec(x_1020);
x_1058 = lean_ctor_get(x_1057, 0);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1057, 1);
lean_inc(x_1059);
if (lean_is_exclusive(x_1057)) {
 lean_ctor_release(x_1057, 0);
 lean_ctor_release(x_1057, 1);
 x_1060 = x_1057;
} else {
 lean_dec_ref(x_1057);
 x_1060 = lean_box(0);
}
x_1061 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1060)) {
 x_1062 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1062 = x_1060;
 lean_ctor_set_tag(x_1062, 7);
}
lean_ctor_set(x_1062, 0, x_1061);
lean_ctor_set(x_1062, 1, x_1058);
if (lean_is_scalar(x_1056)) {
 x_1063 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1063 = x_1056;
 lean_ctor_set_tag(x_1063, 7);
}
lean_ctor_set(x_1063, 0, x_1062);
lean_ctor_set(x_1063, 1, x_1061);
x_1064 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1050, x_1063, x_1024, x_1025, x_1026, x_1027, x_1059);
lean_dec(x_1027);
lean_dec(x_1026);
lean_dec(x_1025);
lean_dec(x_1024);
x_1065 = lean_ctor_get(x_1064, 1);
lean_inc(x_1065);
lean_dec(x_1064);
x_180 = x_1065;
goto block_183;
}
}
}
else
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; uint8_t x_1069; 
lean_dec(x_1034);
lean_dec(x_1033);
x_1066 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_1067 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1066, x_1026, x_1032);
x_1068 = lean_ctor_get(x_1067, 0);
lean_inc(x_1068);
x_1069 = lean_unbox(x_1068);
lean_dec(x_1068);
if (x_1069 == 0)
{
lean_object* x_1070; 
x_1070 = lean_ctor_get(x_1067, 1);
lean_inc(x_1070);
lean_dec(x_1067);
x_161 = x_1031;
x_162 = x_1020;
x_163 = x_1021;
x_164 = x_1022;
x_165 = x_1023;
x_166 = x_1024;
x_167 = x_1025;
x_168 = x_1026;
x_169 = x_1027;
x_170 = x_1070;
goto block_179;
}
else
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
x_1071 = lean_ctor_get(x_1067, 1);
lean_inc(x_1071);
if (lean_is_exclusive(x_1067)) {
 lean_ctor_release(x_1067, 0);
 lean_ctor_release(x_1067, 1);
 x_1072 = x_1067;
} else {
 lean_dec_ref(x_1067);
 x_1072 = lean_box(0);
}
lean_inc(x_1031);
x_1073 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1031, x_1020, x_1071);
x_1074 = lean_ctor_get(x_1073, 0);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_1073, 1);
lean_inc(x_1075);
if (lean_is_exclusive(x_1073)) {
 lean_ctor_release(x_1073, 0);
 lean_ctor_release(x_1073, 1);
 x_1076 = x_1073;
} else {
 lean_dec_ref(x_1073);
 x_1076 = lean_box(0);
}
x_1077 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1076)) {
 x_1078 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1078 = x_1076;
 lean_ctor_set_tag(x_1078, 7);
}
lean_ctor_set(x_1078, 0, x_1077);
lean_ctor_set(x_1078, 1, x_1074);
if (lean_is_scalar(x_1072)) {
 x_1079 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1079 = x_1072;
 lean_ctor_set_tag(x_1079, 7);
}
lean_ctor_set(x_1079, 0, x_1078);
lean_ctor_set(x_1079, 1, x_1077);
x_1080 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1066, x_1079, x_1024, x_1025, x_1026, x_1027, x_1075);
x_1081 = lean_ctor_get(x_1080, 1);
lean_inc(x_1081);
lean_dec(x_1080);
x_161 = x_1031;
x_162 = x_1020;
x_163 = x_1021;
x_164 = x_1022;
x_165 = x_1023;
x_166 = x_1024;
x_167 = x_1025;
x_168 = x_1026;
x_169 = x_1027;
x_170 = x_1081;
goto block_179;
}
}
}
else
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; 
lean_dec(x_1027);
lean_dec(x_1026);
lean_dec(x_1025);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_dec(x_1020);
x_1082 = lean_ctor_get(x_1030, 0);
lean_inc(x_1082);
x_1083 = lean_ctor_get(x_1030, 1);
lean_inc(x_1083);
if (lean_is_exclusive(x_1030)) {
 lean_ctor_release(x_1030, 0);
 lean_ctor_release(x_1030, 1);
 x_1084 = x_1030;
} else {
 lean_dec_ref(x_1030);
 x_1084 = lean_box(0);
}
if (lean_is_scalar(x_1084)) {
 x_1085 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1085 = x_1084;
}
lean_ctor_set(x_1085, 0, x_1082);
lean_ctor_set(x_1085, 1, x_1083);
return x_1085;
}
}
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
lean_dec(x_857);
lean_dec(x_855);
lean_dec(x_853);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_848);
lean_dec(x_847);
lean_dec(x_846);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1097 = lean_ctor_get(x_859, 1);
lean_inc(x_1097);
if (lean_is_exclusive(x_859)) {
 lean_ctor_release(x_859, 0);
 lean_ctor_release(x_859, 1);
 x_1098 = x_859;
} else {
 lean_dec_ref(x_859);
 x_1098 = lean_box(0);
}
x_1099 = lean_box(0);
if (lean_is_scalar(x_1098)) {
 x_1100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1100 = x_1098;
}
lean_ctor_set(x_1100, 0, x_1099);
lean_ctor_set(x_1100, 1, x_1097);
return x_1100;
}
}
else
{
lean_object* x_1101; 
lean_dec(x_857);
lean_dec(x_855);
lean_dec(x_853);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_847);
lean_dec(x_846);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1101 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_848, x_10);
return x_1101;
}
}
block_160:
{
lean_object* x_20; 
x_20 = l_Int_Linear_Poly_updateOccs___redArg(x_11, x_14, x_15, x_16, x_17, x_18, x_19);
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
lean_ctor_set(x_33, 0, x_13);
x_34 = l_Lean_PersistentArray_set___redArg(x_32, x_12, x_33);
lean_dec(x_12);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
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
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_13);
x_65 = l_Lean_PersistentArray_set___redArg(x_49, x_12, x_64);
lean_dec(x_12);
x_66 = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(x_66, 0, x_42);
lean_ctor_set(x_66, 1, x_43);
lean_ctor_set(x_66, 2, x_44);
lean_ctor_set(x_66, 3, x_45);
lean_ctor_set(x_66, 4, x_46);
lean_ctor_set(x_66, 5, x_47);
lean_ctor_set(x_66, 6, x_48);
lean_ctor_set(x_66, 7, x_65);
lean_ctor_set(x_66, 8, x_50);
lean_ctor_set(x_66, 9, x_51);
lean_ctor_set(x_66, 10, x_52);
lean_ctor_set(x_66, 11, x_53);
lean_ctor_set(x_66, 12, x_54);
lean_ctor_set(x_66, 13, x_55);
lean_ctor_set(x_66, 14, x_56);
lean_ctor_set(x_66, 15, x_57);
lean_ctor_set(x_66, 16, x_59);
lean_ctor_set(x_66, 17, x_60);
lean_ctor_set(x_66, 18, x_61);
lean_ctor_set(x_66, 19, x_62);
lean_ctor_set(x_66, 20, x_63);
lean_ctor_set_uint8(x_66, sizeof(void*)*21, x_58);
lean_ctor_set(x_24, 1, x_66);
x_67 = lean_st_ref_set(x_14, x_23, x_26);
lean_dec(x_14);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
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
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_72 = lean_ctor_get(x_24, 0);
x_73 = lean_ctor_get(x_24, 2);
x_74 = lean_ctor_get(x_24, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_24);
x_75 = lean_ctor_get(x_25, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_25, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_25, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_25, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_25, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_25, 5);
lean_inc(x_80);
x_81 = lean_ctor_get(x_25, 6);
lean_inc(x_81);
x_82 = lean_ctor_get(x_25, 7);
lean_inc(x_82);
x_83 = lean_ctor_get(x_25, 8);
lean_inc(x_83);
x_84 = lean_ctor_get(x_25, 9);
lean_inc(x_84);
x_85 = lean_ctor_get(x_25, 10);
lean_inc(x_85);
x_86 = lean_ctor_get(x_25, 11);
lean_inc(x_86);
x_87 = lean_ctor_get(x_25, 12);
lean_inc(x_87);
x_88 = lean_ctor_get(x_25, 13);
lean_inc(x_88);
x_89 = lean_ctor_get(x_25, 14);
lean_inc(x_89);
x_90 = lean_ctor_get(x_25, 15);
lean_inc(x_90);
x_91 = lean_ctor_get_uint8(x_25, sizeof(void*)*21);
x_92 = lean_ctor_get(x_25, 16);
lean_inc(x_92);
x_93 = lean_ctor_get(x_25, 17);
lean_inc(x_93);
x_94 = lean_ctor_get(x_25, 18);
lean_inc(x_94);
x_95 = lean_ctor_get(x_25, 19);
lean_inc(x_95);
x_96 = lean_ctor_get(x_25, 20);
lean_inc(x_96);
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
 x_97 = x_25;
} else {
 lean_dec_ref(x_25);
 x_97 = lean_box(0);
}
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_13);
x_99 = l_Lean_PersistentArray_set___redArg(x_82, x_12, x_98);
lean_dec(x_12);
if (lean_is_scalar(x_97)) {
 x_100 = lean_alloc_ctor(0, 21, 1);
} else {
 x_100 = x_97;
}
lean_ctor_set(x_100, 0, x_75);
lean_ctor_set(x_100, 1, x_76);
lean_ctor_set(x_100, 2, x_77);
lean_ctor_set(x_100, 3, x_78);
lean_ctor_set(x_100, 4, x_79);
lean_ctor_set(x_100, 5, x_80);
lean_ctor_set(x_100, 6, x_81);
lean_ctor_set(x_100, 7, x_99);
lean_ctor_set(x_100, 8, x_83);
lean_ctor_set(x_100, 9, x_84);
lean_ctor_set(x_100, 10, x_85);
lean_ctor_set(x_100, 11, x_86);
lean_ctor_set(x_100, 12, x_87);
lean_ctor_set(x_100, 13, x_88);
lean_ctor_set(x_100, 14, x_89);
lean_ctor_set(x_100, 15, x_90);
lean_ctor_set(x_100, 16, x_92);
lean_ctor_set(x_100, 17, x_93);
lean_ctor_set(x_100, 18, x_94);
lean_ctor_set(x_100, 19, x_95);
lean_ctor_set(x_100, 20, x_96);
lean_ctor_set_uint8(x_100, sizeof(void*)*21, x_91);
x_101 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_101, 0, x_72);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_101, 2, x_73);
lean_ctor_set(x_101, 3, x_74);
lean_ctor_set(x_23, 14, x_101);
x_102 = lean_st_ref_set(x_14, x_23, x_26);
lean_dec(x_14);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_107 = lean_ctor_get(x_23, 0);
x_108 = lean_ctor_get(x_23, 1);
x_109 = lean_ctor_get(x_23, 2);
x_110 = lean_ctor_get(x_23, 3);
x_111 = lean_ctor_get(x_23, 4);
x_112 = lean_ctor_get(x_23, 5);
x_113 = lean_ctor_get(x_23, 6);
x_114 = lean_ctor_get(x_23, 7);
x_115 = lean_ctor_get_uint8(x_23, sizeof(void*)*16);
x_116 = lean_ctor_get(x_23, 8);
x_117 = lean_ctor_get(x_23, 9);
x_118 = lean_ctor_get(x_23, 10);
x_119 = lean_ctor_get(x_23, 11);
x_120 = lean_ctor_get(x_23, 12);
x_121 = lean_ctor_get(x_23, 13);
x_122 = lean_ctor_get(x_23, 15);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_23);
x_123 = lean_ctor_get(x_24, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_24, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_24, 3);
lean_inc(x_125);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 x_126 = x_24;
} else {
 lean_dec_ref(x_24);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_25, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_25, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_25, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_25, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_25, 4);
lean_inc(x_131);
x_132 = lean_ctor_get(x_25, 5);
lean_inc(x_132);
x_133 = lean_ctor_get(x_25, 6);
lean_inc(x_133);
x_134 = lean_ctor_get(x_25, 7);
lean_inc(x_134);
x_135 = lean_ctor_get(x_25, 8);
lean_inc(x_135);
x_136 = lean_ctor_get(x_25, 9);
lean_inc(x_136);
x_137 = lean_ctor_get(x_25, 10);
lean_inc(x_137);
x_138 = lean_ctor_get(x_25, 11);
lean_inc(x_138);
x_139 = lean_ctor_get(x_25, 12);
lean_inc(x_139);
x_140 = lean_ctor_get(x_25, 13);
lean_inc(x_140);
x_141 = lean_ctor_get(x_25, 14);
lean_inc(x_141);
x_142 = lean_ctor_get(x_25, 15);
lean_inc(x_142);
x_143 = lean_ctor_get_uint8(x_25, sizeof(void*)*21);
x_144 = lean_ctor_get(x_25, 16);
lean_inc(x_144);
x_145 = lean_ctor_get(x_25, 17);
lean_inc(x_145);
x_146 = lean_ctor_get(x_25, 18);
lean_inc(x_146);
x_147 = lean_ctor_get(x_25, 19);
lean_inc(x_147);
x_148 = lean_ctor_get(x_25, 20);
lean_inc(x_148);
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
 x_149 = x_25;
} else {
 lean_dec_ref(x_25);
 x_149 = lean_box(0);
}
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_13);
x_151 = l_Lean_PersistentArray_set___redArg(x_134, x_12, x_150);
lean_dec(x_12);
if (lean_is_scalar(x_149)) {
 x_152 = lean_alloc_ctor(0, 21, 1);
} else {
 x_152 = x_149;
}
lean_ctor_set(x_152, 0, x_127);
lean_ctor_set(x_152, 1, x_128);
lean_ctor_set(x_152, 2, x_129);
lean_ctor_set(x_152, 3, x_130);
lean_ctor_set(x_152, 4, x_131);
lean_ctor_set(x_152, 5, x_132);
lean_ctor_set(x_152, 6, x_133);
lean_ctor_set(x_152, 7, x_151);
lean_ctor_set(x_152, 8, x_135);
lean_ctor_set(x_152, 9, x_136);
lean_ctor_set(x_152, 10, x_137);
lean_ctor_set(x_152, 11, x_138);
lean_ctor_set(x_152, 12, x_139);
lean_ctor_set(x_152, 13, x_140);
lean_ctor_set(x_152, 14, x_141);
lean_ctor_set(x_152, 15, x_142);
lean_ctor_set(x_152, 16, x_144);
lean_ctor_set(x_152, 17, x_145);
lean_ctor_set(x_152, 18, x_146);
lean_ctor_set(x_152, 19, x_147);
lean_ctor_set(x_152, 20, x_148);
lean_ctor_set_uint8(x_152, sizeof(void*)*21, x_143);
if (lean_is_scalar(x_126)) {
 x_153 = lean_alloc_ctor(0, 4, 0);
} else {
 x_153 = x_126;
}
lean_ctor_set(x_153, 0, x_123);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_153, 2, x_124);
lean_ctor_set(x_153, 3, x_125);
x_154 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_154, 0, x_107);
lean_ctor_set(x_154, 1, x_108);
lean_ctor_set(x_154, 2, x_109);
lean_ctor_set(x_154, 3, x_110);
lean_ctor_set(x_154, 4, x_111);
lean_ctor_set(x_154, 5, x_112);
lean_ctor_set(x_154, 6, x_113);
lean_ctor_set(x_154, 7, x_114);
lean_ctor_set(x_154, 8, x_116);
lean_ctor_set(x_154, 9, x_117);
lean_ctor_set(x_154, 10, x_118);
lean_ctor_set(x_154, 11, x_119);
lean_ctor_set(x_154, 12, x_120);
lean_ctor_set(x_154, 13, x_121);
lean_ctor_set(x_154, 14, x_153);
lean_ctor_set(x_154, 15, x_122);
lean_ctor_set_uint8(x_154, sizeof(void*)*16, x_115);
x_155 = lean_st_ref_set(x_14, x_154, x_26);
lean_dec(x_14);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
x_158 = lean_box(0);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_20;
}
}
block_179:
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_171, 0, x_161);
x_172 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_171, x_162, x_163, x_164, x_165, x_166, x_167, x_168, x_169, x_170);
if (lean_obj_tag(x_172) == 0)
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_172, 0);
lean_dec(x_174);
x_175 = lean_box(0);
lean_ctor_set(x_172, 0, x_175);
return x_172;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
lean_dec(x_172);
x_177 = lean_box(0);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
else
{
return x_172;
}
}
block_183:
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_box(0);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
return x_182;
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
x_109 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
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
x_154 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_153, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_151);
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
x_90 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_85);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2668_(lean_object* x_1) {
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
if (builtin) {res = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2668_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

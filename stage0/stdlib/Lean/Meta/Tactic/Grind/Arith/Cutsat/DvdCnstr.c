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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_174; uint8_t x_178; 
x_178 = !lean_is_exclusive(x_8);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_179 = lean_ctor_get(x_8, 0);
x_180 = lean_ctor_get(x_8, 1);
x_181 = lean_ctor_get(x_8, 2);
x_182 = lean_ctor_get(x_8, 3);
x_183 = lean_ctor_get(x_8, 4);
x_184 = lean_ctor_get(x_8, 5);
x_185 = lean_ctor_get(x_8, 6);
x_186 = lean_ctor_get(x_8, 7);
x_187 = lean_ctor_get(x_8, 8);
x_188 = lean_ctor_get(x_8, 9);
x_189 = lean_ctor_get(x_8, 10);
x_190 = lean_ctor_get(x_8, 11);
x_191 = lean_ctor_get(x_8, 12);
x_192 = lean_nat_dec_eq(x_182, x_183);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_193 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_unbox(x_194);
lean_dec(x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_577; lean_object* x_578; uint8_t x_579; 
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
x_197 = lean_unsigned_to_nat(1u);
x_198 = lean_nat_add(x_182, x_197);
lean_dec(x_182);
lean_ctor_set(x_8, 3, x_198);
x_577 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_578 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_577, x_8, x_196);
x_579 = !lean_is_exclusive(x_578);
if (x_579 == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; uint8_t x_704; 
x_580 = lean_ctor_get(x_578, 0);
x_581 = lean_ctor_get(x_578, 1);
x_582 = lean_box(0);
x_704 = lean_unbox(x_580);
lean_dec(x_580);
if (x_704 == 0)
{
lean_free_object(x_578);
x_607 = x_2;
x_608 = x_3;
x_609 = x_4;
x_610 = x_5;
x_611 = x_6;
x_612 = x_7;
x_613 = x_8;
x_614 = x_9;
x_615 = x_581;
goto block_703;
}
else
{
lean_object* x_705; uint8_t x_706; 
lean_inc(x_1);
x_705 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_581);
x_706 = !lean_is_exclusive(x_705);
if (x_706 == 0)
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_707 = lean_ctor_get(x_705, 0);
x_708 = lean_ctor_get(x_705, 1);
x_709 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_705, 7);
lean_ctor_set(x_705, 1, x_707);
lean_ctor_set(x_705, 0, x_709);
lean_ctor_set_tag(x_578, 7);
lean_ctor_set(x_578, 1, x_709);
lean_ctor_set(x_578, 0, x_705);
x_710 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_577, x_578, x_6, x_7, x_8, x_9, x_708);
x_711 = lean_ctor_get(x_710, 1);
lean_inc(x_711);
lean_dec(x_710);
x_607 = x_2;
x_608 = x_3;
x_609 = x_4;
x_610 = x_5;
x_611 = x_6;
x_612 = x_7;
x_613 = x_8;
x_614 = x_9;
x_615 = x_711;
goto block_703;
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_712 = lean_ctor_get(x_705, 0);
x_713 = lean_ctor_get(x_705, 1);
lean_inc(x_713);
lean_inc(x_712);
lean_dec(x_705);
x_714 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_715 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_715, 0, x_714);
lean_ctor_set(x_715, 1, x_712);
lean_ctor_set_tag(x_578, 7);
lean_ctor_set(x_578, 1, x_714);
lean_ctor_set(x_578, 0, x_715);
x_716 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_577, x_578, x_6, x_7, x_8, x_9, x_713);
x_717 = lean_ctor_get(x_716, 1);
lean_inc(x_717);
lean_dec(x_716);
x_607 = x_2;
x_608 = x_3;
x_609 = x_4;
x_610 = x_5;
x_611 = x_6;
x_612 = x_7;
x_613 = x_8;
x_614 = x_9;
x_615 = x_717;
goto block_703;
}
}
block_606:
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_603; 
x_598 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_589, x_597);
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_599, 5);
lean_inc(x_600);
lean_dec(x_599);
x_601 = lean_ctor_get(x_598, 1);
lean_inc(x_601);
lean_dec(x_598);
x_602 = lean_ctor_get(x_600, 2);
lean_inc(x_602);
x_603 = lean_nat_dec_lt(x_586, x_602);
lean_dec(x_602);
if (x_603 == 0)
{
lean_object* x_604; 
lean_dec(x_600);
x_604 = l_outOfBounds___redArg(x_582);
x_199 = x_584;
x_200 = x_595;
x_201 = x_585;
x_202 = x_590;
x_203 = x_593;
x_204 = x_586;
x_205 = x_589;
x_206 = x_588;
x_207 = x_592;
x_208 = x_601;
x_209 = x_583;
x_210 = x_596;
x_211 = x_591;
x_212 = x_594;
x_213 = x_587;
x_214 = x_604;
goto block_576;
}
else
{
lean_object* x_605; 
x_605 = l_Lean_PersistentArray_get_x21___redArg(x_582, x_600, x_586);
x_199 = x_584;
x_200 = x_595;
x_201 = x_585;
x_202 = x_590;
x_203 = x_593;
x_204 = x_586;
x_205 = x_589;
x_206 = x_588;
x_207 = x_592;
x_208 = x_601;
x_209 = x_583;
x_210 = x_596;
x_211 = x_591;
x_212 = x_594;
x_213 = x_587;
x_214 = x_605;
goto block_576;
}
}
block_703:
{
lean_object* x_616; lean_object* x_617; 
x_616 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_613);
x_617 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_616, x_607, x_611, x_612, x_613, x_614, x_615);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; uint8_t x_622; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
lean_dec(x_617);
x_620 = lean_ctor_get(x_618, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_618, 1);
lean_inc(x_621);
lean_inc(x_620);
x_622 = l_Int_Linear_Poly_isUnsatDvd(x_620, x_621);
if (x_622 == 0)
{
uint8_t x_623; 
x_623 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_618);
if (x_623 == 0)
{
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_624; 
lean_dec(x_621);
lean_dec(x_620);
lean_dec(x_610);
lean_dec(x_609);
lean_dec(x_608);
x_624 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_618, x_607, x_611, x_612, x_613, x_614, x_619);
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_607);
return x_624;
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; uint8_t x_632; uint8_t x_633; uint8_t x_634; 
x_625 = lean_ctor_get(x_621, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_621, 1);
lean_inc(x_626);
x_627 = lean_ctor_get(x_621, 2);
lean_inc(x_627);
lean_inc(x_618);
x_628 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_618, x_607, x_619);
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_628, 1);
lean_inc(x_630);
lean_dec(x_628);
x_631 = lean_box(0);
x_632 = lean_unbox(x_629);
lean_dec(x_629);
x_633 = lean_unbox(x_631);
x_634 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_632, x_633);
if (x_634 == 0)
{
x_583 = x_627;
x_584 = x_620;
x_585 = x_618;
x_586 = x_626;
x_587 = x_625;
x_588 = x_621;
x_589 = x_607;
x_590 = x_608;
x_591 = x_609;
x_592 = x_610;
x_593 = x_611;
x_594 = x_612;
x_595 = x_613;
x_596 = x_614;
x_597 = x_630;
goto block_606;
}
else
{
lean_object* x_635; lean_object* x_636; 
x_635 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_626, x_607, x_630);
x_636 = lean_ctor_get(x_635, 1);
lean_inc(x_636);
lean_dec(x_635);
x_583 = x_627;
x_584 = x_620;
x_585 = x_618;
x_586 = x_626;
x_587 = x_625;
x_588 = x_621;
x_589 = x_607;
x_590 = x_608;
x_591 = x_609;
x_592 = x_610;
x_593 = x_611;
x_594 = x_612;
x_595 = x_613;
x_596 = x_614;
x_597 = x_636;
goto block_606;
}
}
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; uint8_t x_640; 
lean_dec(x_621);
lean_dec(x_620);
lean_dec(x_610);
lean_dec(x_609);
lean_dec(x_608);
x_637 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_638 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_637, x_613, x_619);
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_unbox(x_639);
lean_dec(x_639);
if (x_640 == 0)
{
lean_object* x_641; 
lean_dec(x_618);
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_607);
x_641 = lean_ctor_get(x_638, 1);
lean_inc(x_641);
lean_dec(x_638);
x_174 = x_641;
goto block_177;
}
else
{
uint8_t x_642; 
x_642 = !lean_is_exclusive(x_638);
if (x_642 == 0)
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; 
x_643 = lean_ctor_get(x_638, 1);
x_644 = lean_ctor_get(x_638, 0);
lean_dec(x_644);
x_645 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_618, x_607, x_643);
lean_dec(x_607);
x_646 = !lean_is_exclusive(x_645);
if (x_646 == 0)
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_647 = lean_ctor_get(x_645, 0);
x_648 = lean_ctor_get(x_645, 1);
x_649 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_645, 7);
lean_ctor_set(x_645, 1, x_647);
lean_ctor_set(x_645, 0, x_649);
lean_ctor_set_tag(x_638, 7);
lean_ctor_set(x_638, 1, x_649);
lean_ctor_set(x_638, 0, x_645);
x_650 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_637, x_638, x_611, x_612, x_613, x_614, x_648);
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_611);
x_651 = lean_ctor_get(x_650, 1);
lean_inc(x_651);
lean_dec(x_650);
x_174 = x_651;
goto block_177;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_652 = lean_ctor_get(x_645, 0);
x_653 = lean_ctor_get(x_645, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_645);
x_654 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_655 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_655, 0, x_654);
lean_ctor_set(x_655, 1, x_652);
lean_ctor_set_tag(x_638, 7);
lean_ctor_set(x_638, 1, x_654);
lean_ctor_set(x_638, 0, x_655);
x_656 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_637, x_638, x_611, x_612, x_613, x_614, x_653);
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_611);
x_657 = lean_ctor_get(x_656, 1);
lean_inc(x_657);
lean_dec(x_656);
x_174 = x_657;
goto block_177;
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_658 = lean_ctor_get(x_638, 1);
lean_inc(x_658);
lean_dec(x_638);
x_659 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_618, x_607, x_658);
lean_dec(x_607);
x_660 = lean_ctor_get(x_659, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_659, 1);
lean_inc(x_661);
if (lean_is_exclusive(x_659)) {
 lean_ctor_release(x_659, 0);
 lean_ctor_release(x_659, 1);
 x_662 = x_659;
} else {
 lean_dec_ref(x_659);
 x_662 = lean_box(0);
}
x_663 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_662)) {
 x_664 = lean_alloc_ctor(7, 2, 0);
} else {
 x_664 = x_662;
 lean_ctor_set_tag(x_664, 7);
}
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_660);
x_665 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_663);
x_666 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_637, x_665, x_611, x_612, x_613, x_614, x_661);
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_611);
x_667 = lean_ctor_get(x_666, 1);
lean_inc(x_667);
lean_dec(x_666);
x_174 = x_667;
goto block_177;
}
}
}
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; uint8_t x_671; 
lean_dec(x_621);
lean_dec(x_620);
x_668 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_669 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_668, x_613, x_619);
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_unbox(x_670);
lean_dec(x_670);
if (x_671 == 0)
{
lean_object* x_672; 
x_672 = lean_ctor_get(x_669, 1);
lean_inc(x_672);
lean_dec(x_669);
x_155 = x_618;
x_156 = x_607;
x_157 = x_608;
x_158 = x_609;
x_159 = x_610;
x_160 = x_611;
x_161 = x_612;
x_162 = x_613;
x_163 = x_614;
x_164 = x_672;
goto block_173;
}
else
{
uint8_t x_673; 
x_673 = !lean_is_exclusive(x_669);
if (x_673 == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; uint8_t x_677; 
x_674 = lean_ctor_get(x_669, 1);
x_675 = lean_ctor_get(x_669, 0);
lean_dec(x_675);
lean_inc(x_618);
x_676 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_618, x_607, x_674);
x_677 = !lean_is_exclusive(x_676);
if (x_677 == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_678 = lean_ctor_get(x_676, 0);
x_679 = lean_ctor_get(x_676, 1);
x_680 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_676, 7);
lean_ctor_set(x_676, 1, x_678);
lean_ctor_set(x_676, 0, x_680);
lean_ctor_set_tag(x_669, 7);
lean_ctor_set(x_669, 1, x_680);
lean_ctor_set(x_669, 0, x_676);
x_681 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_668, x_669, x_611, x_612, x_613, x_614, x_679);
x_682 = lean_ctor_get(x_681, 1);
lean_inc(x_682);
lean_dec(x_681);
x_155 = x_618;
x_156 = x_607;
x_157 = x_608;
x_158 = x_609;
x_159 = x_610;
x_160 = x_611;
x_161 = x_612;
x_162 = x_613;
x_163 = x_614;
x_164 = x_682;
goto block_173;
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_683 = lean_ctor_get(x_676, 0);
x_684 = lean_ctor_get(x_676, 1);
lean_inc(x_684);
lean_inc(x_683);
lean_dec(x_676);
x_685 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_686 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_686, 0, x_685);
lean_ctor_set(x_686, 1, x_683);
lean_ctor_set_tag(x_669, 7);
lean_ctor_set(x_669, 1, x_685);
lean_ctor_set(x_669, 0, x_686);
x_687 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_668, x_669, x_611, x_612, x_613, x_614, x_684);
x_688 = lean_ctor_get(x_687, 1);
lean_inc(x_688);
lean_dec(x_687);
x_155 = x_618;
x_156 = x_607;
x_157 = x_608;
x_158 = x_609;
x_159 = x_610;
x_160 = x_611;
x_161 = x_612;
x_162 = x_613;
x_163 = x_614;
x_164 = x_688;
goto block_173;
}
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_689 = lean_ctor_get(x_669, 1);
lean_inc(x_689);
lean_dec(x_669);
lean_inc(x_618);
x_690 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_618, x_607, x_689);
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 x_693 = x_690;
} else {
 lean_dec_ref(x_690);
 x_693 = lean_box(0);
}
x_694 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_693)) {
 x_695 = lean_alloc_ctor(7, 2, 0);
} else {
 x_695 = x_693;
 lean_ctor_set_tag(x_695, 7);
}
lean_ctor_set(x_695, 0, x_694);
lean_ctor_set(x_695, 1, x_691);
x_696 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_696, 0, x_695);
lean_ctor_set(x_696, 1, x_694);
x_697 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_668, x_696, x_611, x_612, x_613, x_614, x_692);
x_698 = lean_ctor_get(x_697, 1);
lean_inc(x_698);
lean_dec(x_697);
x_155 = x_618;
x_156 = x_607;
x_157 = x_608;
x_158 = x_609;
x_159 = x_610;
x_160 = x_611;
x_161 = x_612;
x_162 = x_613;
x_163 = x_614;
x_164 = x_698;
goto block_173;
}
}
}
}
else
{
uint8_t x_699; 
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_610);
lean_dec(x_609);
lean_dec(x_608);
lean_dec(x_607);
x_699 = !lean_is_exclusive(x_617);
if (x_699 == 0)
{
return x_617;
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_700 = lean_ctor_get(x_617, 0);
x_701 = lean_ctor_get(x_617, 1);
lean_inc(x_701);
lean_inc(x_700);
lean_dec(x_617);
x_702 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_702, 0, x_700);
lean_ctor_set(x_702, 1, x_701);
return x_702;
}
}
}
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; uint8_t x_812; 
x_718 = lean_ctor_get(x_578, 0);
x_719 = lean_ctor_get(x_578, 1);
lean_inc(x_719);
lean_inc(x_718);
lean_dec(x_578);
x_720 = lean_box(0);
x_812 = lean_unbox(x_718);
lean_dec(x_718);
if (x_812 == 0)
{
x_745 = x_2;
x_746 = x_3;
x_747 = x_4;
x_748 = x_5;
x_749 = x_6;
x_750 = x_7;
x_751 = x_8;
x_752 = x_9;
x_753 = x_719;
goto block_811;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
lean_inc(x_1);
x_813 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_719);
x_814 = lean_ctor_get(x_813, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_813, 1);
lean_inc(x_815);
if (lean_is_exclusive(x_813)) {
 lean_ctor_release(x_813, 0);
 lean_ctor_release(x_813, 1);
 x_816 = x_813;
} else {
 lean_dec_ref(x_813);
 x_816 = lean_box(0);
}
x_817 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_816)) {
 x_818 = lean_alloc_ctor(7, 2, 0);
} else {
 x_818 = x_816;
 lean_ctor_set_tag(x_818, 7);
}
lean_ctor_set(x_818, 0, x_817);
lean_ctor_set(x_818, 1, x_814);
x_819 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_819, 0, x_818);
lean_ctor_set(x_819, 1, x_817);
x_820 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_577, x_819, x_6, x_7, x_8, x_9, x_815);
x_821 = lean_ctor_get(x_820, 1);
lean_inc(x_821);
lean_dec(x_820);
x_745 = x_2;
x_746 = x_3;
x_747 = x_4;
x_748 = x_5;
x_749 = x_6;
x_750 = x_7;
x_751 = x_8;
x_752 = x_9;
x_753 = x_821;
goto block_811;
}
block_744:
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; uint8_t x_741; 
x_736 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_727, x_735);
x_737 = lean_ctor_get(x_736, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_737, 5);
lean_inc(x_738);
lean_dec(x_737);
x_739 = lean_ctor_get(x_736, 1);
lean_inc(x_739);
lean_dec(x_736);
x_740 = lean_ctor_get(x_738, 2);
lean_inc(x_740);
x_741 = lean_nat_dec_lt(x_724, x_740);
lean_dec(x_740);
if (x_741 == 0)
{
lean_object* x_742; 
lean_dec(x_738);
x_742 = l_outOfBounds___redArg(x_720);
x_199 = x_722;
x_200 = x_733;
x_201 = x_723;
x_202 = x_728;
x_203 = x_731;
x_204 = x_724;
x_205 = x_727;
x_206 = x_726;
x_207 = x_730;
x_208 = x_739;
x_209 = x_721;
x_210 = x_734;
x_211 = x_729;
x_212 = x_732;
x_213 = x_725;
x_214 = x_742;
goto block_576;
}
else
{
lean_object* x_743; 
x_743 = l_Lean_PersistentArray_get_x21___redArg(x_720, x_738, x_724);
x_199 = x_722;
x_200 = x_733;
x_201 = x_723;
x_202 = x_728;
x_203 = x_731;
x_204 = x_724;
x_205 = x_727;
x_206 = x_726;
x_207 = x_730;
x_208 = x_739;
x_209 = x_721;
x_210 = x_734;
x_211 = x_729;
x_212 = x_732;
x_213 = x_725;
x_214 = x_743;
goto block_576;
}
}
block_811:
{
lean_object* x_754; lean_object* x_755; 
x_754 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_751);
x_755 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_754, x_745, x_749, x_750, x_751, x_752, x_753);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; uint8_t x_760; 
x_756 = lean_ctor_get(x_755, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_755, 1);
lean_inc(x_757);
lean_dec(x_755);
x_758 = lean_ctor_get(x_756, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_756, 1);
lean_inc(x_759);
lean_inc(x_758);
x_760 = l_Int_Linear_Poly_isUnsatDvd(x_758, x_759);
if (x_760 == 0)
{
uint8_t x_761; 
x_761 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_756);
if (x_761 == 0)
{
if (lean_obj_tag(x_759) == 0)
{
lean_object* x_762; 
lean_dec(x_759);
lean_dec(x_758);
lean_dec(x_748);
lean_dec(x_747);
lean_dec(x_746);
x_762 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_756, x_745, x_749, x_750, x_751, x_752, x_757);
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_dec(x_745);
return x_762;
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; uint8_t x_770; uint8_t x_771; uint8_t x_772; 
x_763 = lean_ctor_get(x_759, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_759, 1);
lean_inc(x_764);
x_765 = lean_ctor_get(x_759, 2);
lean_inc(x_765);
lean_inc(x_756);
x_766 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_756, x_745, x_757);
x_767 = lean_ctor_get(x_766, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_766, 1);
lean_inc(x_768);
lean_dec(x_766);
x_769 = lean_box(0);
x_770 = lean_unbox(x_767);
lean_dec(x_767);
x_771 = lean_unbox(x_769);
x_772 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_770, x_771);
if (x_772 == 0)
{
x_721 = x_765;
x_722 = x_758;
x_723 = x_756;
x_724 = x_764;
x_725 = x_763;
x_726 = x_759;
x_727 = x_745;
x_728 = x_746;
x_729 = x_747;
x_730 = x_748;
x_731 = x_749;
x_732 = x_750;
x_733 = x_751;
x_734 = x_752;
x_735 = x_768;
goto block_744;
}
else
{
lean_object* x_773; lean_object* x_774; 
x_773 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_764, x_745, x_768);
x_774 = lean_ctor_get(x_773, 1);
lean_inc(x_774);
lean_dec(x_773);
x_721 = x_765;
x_722 = x_758;
x_723 = x_756;
x_724 = x_764;
x_725 = x_763;
x_726 = x_759;
x_727 = x_745;
x_728 = x_746;
x_729 = x_747;
x_730 = x_748;
x_731 = x_749;
x_732 = x_750;
x_733 = x_751;
x_734 = x_752;
x_735 = x_774;
goto block_744;
}
}
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; uint8_t x_778; 
lean_dec(x_759);
lean_dec(x_758);
lean_dec(x_748);
lean_dec(x_747);
lean_dec(x_746);
x_775 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_776 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_775, x_751, x_757);
x_777 = lean_ctor_get(x_776, 0);
lean_inc(x_777);
x_778 = lean_unbox(x_777);
lean_dec(x_777);
if (x_778 == 0)
{
lean_object* x_779; 
lean_dec(x_756);
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_dec(x_745);
x_779 = lean_ctor_get(x_776, 1);
lean_inc(x_779);
lean_dec(x_776);
x_174 = x_779;
goto block_177;
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_780 = lean_ctor_get(x_776, 1);
lean_inc(x_780);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_781 = x_776;
} else {
 lean_dec_ref(x_776);
 x_781 = lean_box(0);
}
x_782 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_756, x_745, x_780);
lean_dec(x_745);
x_783 = lean_ctor_get(x_782, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_782, 1);
lean_inc(x_784);
if (lean_is_exclusive(x_782)) {
 lean_ctor_release(x_782, 0);
 lean_ctor_release(x_782, 1);
 x_785 = x_782;
} else {
 lean_dec_ref(x_782);
 x_785 = lean_box(0);
}
x_786 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_785)) {
 x_787 = lean_alloc_ctor(7, 2, 0);
} else {
 x_787 = x_785;
 lean_ctor_set_tag(x_787, 7);
}
lean_ctor_set(x_787, 0, x_786);
lean_ctor_set(x_787, 1, x_783);
if (lean_is_scalar(x_781)) {
 x_788 = lean_alloc_ctor(7, 2, 0);
} else {
 x_788 = x_781;
 lean_ctor_set_tag(x_788, 7);
}
lean_ctor_set(x_788, 0, x_787);
lean_ctor_set(x_788, 1, x_786);
x_789 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_775, x_788, x_749, x_750, x_751, x_752, x_784);
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
x_790 = lean_ctor_get(x_789, 1);
lean_inc(x_790);
lean_dec(x_789);
x_174 = x_790;
goto block_177;
}
}
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; uint8_t x_794; 
lean_dec(x_759);
lean_dec(x_758);
x_791 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_792 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_791, x_751, x_757);
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
x_794 = lean_unbox(x_793);
lean_dec(x_793);
if (x_794 == 0)
{
lean_object* x_795; 
x_795 = lean_ctor_get(x_792, 1);
lean_inc(x_795);
lean_dec(x_792);
x_155 = x_756;
x_156 = x_745;
x_157 = x_746;
x_158 = x_747;
x_159 = x_748;
x_160 = x_749;
x_161 = x_750;
x_162 = x_751;
x_163 = x_752;
x_164 = x_795;
goto block_173;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_796 = lean_ctor_get(x_792, 1);
lean_inc(x_796);
if (lean_is_exclusive(x_792)) {
 lean_ctor_release(x_792, 0);
 lean_ctor_release(x_792, 1);
 x_797 = x_792;
} else {
 lean_dec_ref(x_792);
 x_797 = lean_box(0);
}
lean_inc(x_756);
x_798 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_756, x_745, x_796);
x_799 = lean_ctor_get(x_798, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_798, 1);
lean_inc(x_800);
if (lean_is_exclusive(x_798)) {
 lean_ctor_release(x_798, 0);
 lean_ctor_release(x_798, 1);
 x_801 = x_798;
} else {
 lean_dec_ref(x_798);
 x_801 = lean_box(0);
}
x_802 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_801)) {
 x_803 = lean_alloc_ctor(7, 2, 0);
} else {
 x_803 = x_801;
 lean_ctor_set_tag(x_803, 7);
}
lean_ctor_set(x_803, 0, x_802);
lean_ctor_set(x_803, 1, x_799);
if (lean_is_scalar(x_797)) {
 x_804 = lean_alloc_ctor(7, 2, 0);
} else {
 x_804 = x_797;
 lean_ctor_set_tag(x_804, 7);
}
lean_ctor_set(x_804, 0, x_803);
lean_ctor_set(x_804, 1, x_802);
x_805 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_791, x_804, x_749, x_750, x_751, x_752, x_800);
x_806 = lean_ctor_get(x_805, 1);
lean_inc(x_806);
lean_dec(x_805);
x_155 = x_756;
x_156 = x_745;
x_157 = x_746;
x_158 = x_747;
x_159 = x_748;
x_160 = x_749;
x_161 = x_750;
x_162 = x_751;
x_163 = x_752;
x_164 = x_806;
goto block_173;
}
}
}
else
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_dec(x_748);
lean_dec(x_747);
lean_dec(x_746);
lean_dec(x_745);
x_807 = lean_ctor_get(x_755, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_755, 1);
lean_inc(x_808);
if (lean_is_exclusive(x_755)) {
 lean_ctor_release(x_755, 0);
 lean_ctor_release(x_755, 1);
 x_809 = x_755;
} else {
 lean_dec_ref(x_755);
 x_809 = lean_box(0);
}
if (lean_is_scalar(x_809)) {
 x_810 = lean_alloc_ctor(1, 2, 0);
} else {
 x_810 = x_809;
}
lean_ctor_set(x_810, 0, x_807);
lean_ctor_set(x_810, 1, x_808);
return x_810;
}
}
}
block_576:
{
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_207);
lean_dec(x_202);
lean_dec(x_199);
x_215 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_216 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_215, x_200, x_208);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_unbox(x_217);
lean_dec(x_217);
if (x_218 == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_dec(x_216);
x_11 = x_201;
x_12 = x_204;
x_13 = x_206;
x_14 = x_205;
x_15 = x_203;
x_16 = x_212;
x_17 = x_200;
x_18 = x_210;
x_19 = x_219;
goto block_154;
}
else
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_216);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_221 = lean_ctor_get(x_216, 1);
x_222 = lean_ctor_get(x_216, 0);
lean_dec(x_222);
lean_inc(x_201);
x_223 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_201, x_205, x_221);
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_223, 0);
x_226 = lean_ctor_get(x_223, 1);
x_227 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_223, 7);
lean_ctor_set(x_223, 1, x_225);
lean_ctor_set(x_223, 0, x_227);
lean_ctor_set_tag(x_216, 7);
lean_ctor_set(x_216, 1, x_227);
lean_ctor_set(x_216, 0, x_223);
x_228 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_215, x_216, x_203, x_212, x_200, x_210, x_226);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
x_11 = x_201;
x_12 = x_204;
x_13 = x_206;
x_14 = x_205;
x_15 = x_203;
x_16 = x_212;
x_17 = x_200;
x_18 = x_210;
x_19 = x_229;
goto block_154;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_230 = lean_ctor_get(x_223, 0);
x_231 = lean_ctor_get(x_223, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_223);
x_232 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_233 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_230);
lean_ctor_set_tag(x_216, 7);
lean_ctor_set(x_216, 1, x_232);
lean_ctor_set(x_216, 0, x_233);
x_234 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_215, x_216, x_203, x_212, x_200, x_210, x_231);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
lean_dec(x_234);
x_11 = x_201;
x_12 = x_204;
x_13 = x_206;
x_14 = x_205;
x_15 = x_203;
x_16 = x_212;
x_17 = x_200;
x_18 = x_210;
x_19 = x_235;
goto block_154;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_236 = lean_ctor_get(x_216, 1);
lean_inc(x_236);
lean_dec(x_216);
lean_inc(x_201);
x_237 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_201, x_205, x_236);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_240 = x_237;
} else {
 lean_dec_ref(x_237);
 x_240 = lean_box(0);
}
x_241 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(7, 2, 0);
} else {
 x_242 = x_240;
 lean_ctor_set_tag(x_242, 7);
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_238);
x_243 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_241);
x_244 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_215, x_243, x_203, x_212, x_200, x_210, x_239);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
lean_dec(x_244);
x_11 = x_201;
x_12 = x_204;
x_13 = x_206;
x_14 = x_205;
x_15 = x_203;
x_16 = x_212;
x_17 = x_200;
x_18 = x_210;
x_19 = x_245;
goto block_154;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_206);
x_246 = lean_ctor_get(x_214, 0);
lean_inc(x_246);
lean_dec(x_214);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
lean_dec(x_247);
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_207);
lean_dec(x_204);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_199);
x_248 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_246, x_205, x_203, x_212, x_200, x_210, x_208);
lean_dec(x_210);
lean_dec(x_200);
lean_dec(x_212);
lean_dec(x_203);
lean_dec(x_205);
return x_248;
}
else
{
lean_object* x_249; uint8_t x_250; 
x_249 = lean_ctor_get(x_246, 0);
lean_inc(x_249);
x_250 = !lean_is_exclusive(x_247);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_251 = lean_ctor_get(x_247, 0);
x_252 = lean_ctor_get(x_247, 2);
x_253 = lean_ctor_get(x_247, 1);
lean_dec(x_253);
x_254 = lean_int_mul(x_213, x_249);
x_255 = lean_int_mul(x_251, x_199);
x_256 = l_Lean_Meta_Grind_Arith_gcdExt(x_254, x_255);
lean_dec(x_255);
lean_dec(x_254);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_ctor_get(x_257, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_257, 1);
lean_inc(x_260);
lean_dec(x_257);
x_261 = lean_st_ref_take(x_205, x_208);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_262, 14);
lean_inc(x_263);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_261, 1);
lean_inc(x_265);
lean_dec(x_261);
x_266 = !lean_is_exclusive(x_262);
if (x_266 == 0)
{
lean_object* x_267; uint8_t x_268; 
x_267 = lean_ctor_get(x_262, 14);
lean_dec(x_267);
x_268 = !lean_is_exclusive(x_263);
if (x_268 == 0)
{
lean_object* x_269; uint8_t x_270; 
x_269 = lean_ctor_get(x_263, 1);
lean_dec(x_269);
x_270 = !lean_is_exclusive(x_264);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_271 = lean_ctor_get(x_264, 5);
x_272 = lean_box(0);
x_273 = l_Lean_PersistentArray_set___redArg(x_271, x_204, x_272);
lean_ctor_set(x_264, 5, x_273);
x_274 = lean_st_ref_set(x_205, x_262, x_265);
x_275 = !lean_is_exclusive(x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_276 = lean_ctor_get(x_274, 1);
x_277 = lean_ctor_get(x_274, 0);
lean_dec(x_277);
x_278 = lean_int_mul(x_259, x_249);
lean_dec(x_259);
lean_inc(x_209);
x_279 = l_Int_Linear_Poly_mul(x_209, x_278);
lean_dec(x_278);
x_280 = lean_int_mul(x_260, x_199);
lean_dec(x_260);
lean_inc(x_252);
x_281 = l_Int_Linear_Poly_mul(x_252, x_280);
lean_dec(x_280);
x_282 = lean_int_mul(x_199, x_249);
lean_dec(x_249);
lean_dec(x_199);
x_283 = l_Int_Linear_Poly_combine(x_279, x_281);
lean_inc(x_258);
lean_ctor_set(x_247, 2, x_283);
lean_ctor_set(x_247, 1, x_204);
lean_ctor_set(x_247, 0, x_258);
lean_inc(x_246);
lean_inc(x_201);
lean_ctor_set_tag(x_274, 4);
lean_ctor_set(x_274, 1, x_246);
lean_ctor_set(x_274, 0, x_201);
x_284 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_247);
lean_ctor_set(x_284, 2, x_274);
lean_inc(x_210);
lean_inc(x_200);
lean_inc(x_212);
lean_inc(x_203);
lean_inc(x_207);
lean_inc(x_211);
lean_inc(x_202);
lean_inc(x_205);
x_285 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_284, x_205, x_202, x_211, x_207, x_203, x_212, x_200, x_210, x_276);
if (lean_obj_tag(x_285) == 0)
{
uint8_t x_286; 
x_286 = !lean_is_exclusive(x_285);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_287 = lean_ctor_get(x_285, 1);
x_288 = lean_ctor_get(x_285, 0);
lean_dec(x_288);
x_289 = l_Int_Linear_Poly_mul(x_209, x_251);
lean_dec(x_251);
x_290 = lean_int_neg(x_213);
lean_dec(x_213);
x_291 = l_Int_Linear_Poly_mul(x_252, x_290);
lean_dec(x_290);
x_292 = l_Int_Linear_Poly_combine(x_289, x_291);
lean_inc(x_246);
lean_ctor_set_tag(x_285, 5);
lean_ctor_set(x_285, 1, x_246);
lean_ctor_set(x_285, 0, x_201);
x_293 = !lean_is_exclusive(x_246);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_246, 2);
lean_dec(x_294);
x_295 = lean_ctor_get(x_246, 1);
lean_dec(x_295);
x_296 = lean_ctor_get(x_246, 0);
lean_dec(x_296);
lean_ctor_set(x_246, 2, x_285);
lean_ctor_set(x_246, 1, x_292);
lean_ctor_set(x_246, 0, x_258);
x_1 = x_246;
x_2 = x_205;
x_3 = x_202;
x_4 = x_211;
x_5 = x_207;
x_6 = x_203;
x_7 = x_212;
x_8 = x_200;
x_9 = x_210;
x_10 = x_287;
goto _start;
}
else
{
lean_object* x_298; 
lean_dec(x_246);
x_298 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_298, 0, x_258);
lean_ctor_set(x_298, 1, x_292);
lean_ctor_set(x_298, 2, x_285);
x_1 = x_298;
x_2 = x_205;
x_3 = x_202;
x_4 = x_211;
x_5 = x_207;
x_6 = x_203;
x_7 = x_212;
x_8 = x_200;
x_9 = x_210;
x_10 = x_287;
goto _start;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_300 = lean_ctor_get(x_285, 1);
lean_inc(x_300);
lean_dec(x_285);
x_301 = l_Int_Linear_Poly_mul(x_209, x_251);
lean_dec(x_251);
x_302 = lean_int_neg(x_213);
lean_dec(x_213);
x_303 = l_Int_Linear_Poly_mul(x_252, x_302);
lean_dec(x_302);
x_304 = l_Int_Linear_Poly_combine(x_301, x_303);
lean_inc(x_246);
x_305 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_305, 0, x_201);
lean_ctor_set(x_305, 1, x_246);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 lean_ctor_release(x_246, 2);
 x_306 = x_246;
} else {
 lean_dec_ref(x_246);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(0, 3, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_258);
lean_ctor_set(x_307, 1, x_304);
lean_ctor_set(x_307, 2, x_305);
x_1 = x_307;
x_2 = x_205;
x_3 = x_202;
x_4 = x_211;
x_5 = x_207;
x_6 = x_203;
x_7 = x_212;
x_8 = x_200;
x_9 = x_210;
x_10 = x_300;
goto _start;
}
}
else
{
lean_dec(x_258);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_246);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_207);
lean_dec(x_205);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
return x_285;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_309 = lean_ctor_get(x_274, 1);
lean_inc(x_309);
lean_dec(x_274);
x_310 = lean_int_mul(x_259, x_249);
lean_dec(x_259);
lean_inc(x_209);
x_311 = l_Int_Linear_Poly_mul(x_209, x_310);
lean_dec(x_310);
x_312 = lean_int_mul(x_260, x_199);
lean_dec(x_260);
lean_inc(x_252);
x_313 = l_Int_Linear_Poly_mul(x_252, x_312);
lean_dec(x_312);
x_314 = lean_int_mul(x_199, x_249);
lean_dec(x_249);
lean_dec(x_199);
x_315 = l_Int_Linear_Poly_combine(x_311, x_313);
lean_inc(x_258);
lean_ctor_set(x_247, 2, x_315);
lean_ctor_set(x_247, 1, x_204);
lean_ctor_set(x_247, 0, x_258);
lean_inc(x_246);
lean_inc(x_201);
x_316 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_316, 0, x_201);
lean_ctor_set(x_316, 1, x_246);
x_317 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_247);
lean_ctor_set(x_317, 2, x_316);
lean_inc(x_210);
lean_inc(x_200);
lean_inc(x_212);
lean_inc(x_203);
lean_inc(x_207);
lean_inc(x_211);
lean_inc(x_202);
lean_inc(x_205);
x_318 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_317, x_205, x_202, x_211, x_207, x_203, x_212, x_200, x_210, x_309);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_320 = x_318;
} else {
 lean_dec_ref(x_318);
 x_320 = lean_box(0);
}
x_321 = l_Int_Linear_Poly_mul(x_209, x_251);
lean_dec(x_251);
x_322 = lean_int_neg(x_213);
lean_dec(x_213);
x_323 = l_Int_Linear_Poly_mul(x_252, x_322);
lean_dec(x_322);
x_324 = l_Int_Linear_Poly_combine(x_321, x_323);
lean_inc(x_246);
if (lean_is_scalar(x_320)) {
 x_325 = lean_alloc_ctor(5, 2, 0);
} else {
 x_325 = x_320;
 lean_ctor_set_tag(x_325, 5);
}
lean_ctor_set(x_325, 0, x_201);
lean_ctor_set(x_325, 1, x_246);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 lean_ctor_release(x_246, 2);
 x_326 = x_246;
} else {
 lean_dec_ref(x_246);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(0, 3, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_258);
lean_ctor_set(x_327, 1, x_324);
lean_ctor_set(x_327, 2, x_325);
x_1 = x_327;
x_2 = x_205;
x_3 = x_202;
x_4 = x_211;
x_5 = x_207;
x_6 = x_203;
x_7 = x_212;
x_8 = x_200;
x_9 = x_210;
x_10 = x_319;
goto _start;
}
else
{
lean_dec(x_258);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_246);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_207);
lean_dec(x_205);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
return x_318;
}
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_329 = lean_ctor_get(x_264, 0);
x_330 = lean_ctor_get(x_264, 1);
x_331 = lean_ctor_get(x_264, 2);
x_332 = lean_ctor_get(x_264, 3);
x_333 = lean_ctor_get(x_264, 4);
x_334 = lean_ctor_get(x_264, 5);
x_335 = lean_ctor_get(x_264, 6);
x_336 = lean_ctor_get(x_264, 7);
x_337 = lean_ctor_get(x_264, 8);
x_338 = lean_ctor_get(x_264, 9);
x_339 = lean_ctor_get(x_264, 10);
x_340 = lean_ctor_get(x_264, 11);
x_341 = lean_ctor_get(x_264, 12);
x_342 = lean_ctor_get(x_264, 13);
x_343 = lean_ctor_get_uint8(x_264, sizeof(void*)*19);
x_344 = lean_ctor_get(x_264, 14);
x_345 = lean_ctor_get(x_264, 15);
x_346 = lean_ctor_get(x_264, 16);
x_347 = lean_ctor_get(x_264, 17);
x_348 = lean_ctor_get(x_264, 18);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_264);
x_349 = lean_box(0);
x_350 = l_Lean_PersistentArray_set___redArg(x_334, x_204, x_349);
x_351 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_351, 0, x_329);
lean_ctor_set(x_351, 1, x_330);
lean_ctor_set(x_351, 2, x_331);
lean_ctor_set(x_351, 3, x_332);
lean_ctor_set(x_351, 4, x_333);
lean_ctor_set(x_351, 5, x_350);
lean_ctor_set(x_351, 6, x_335);
lean_ctor_set(x_351, 7, x_336);
lean_ctor_set(x_351, 8, x_337);
lean_ctor_set(x_351, 9, x_338);
lean_ctor_set(x_351, 10, x_339);
lean_ctor_set(x_351, 11, x_340);
lean_ctor_set(x_351, 12, x_341);
lean_ctor_set(x_351, 13, x_342);
lean_ctor_set(x_351, 14, x_344);
lean_ctor_set(x_351, 15, x_345);
lean_ctor_set(x_351, 16, x_346);
lean_ctor_set(x_351, 17, x_347);
lean_ctor_set(x_351, 18, x_348);
lean_ctor_set_uint8(x_351, sizeof(void*)*19, x_343);
lean_ctor_set(x_263, 1, x_351);
x_352 = lean_st_ref_set(x_205, x_262, x_265);
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_354 = x_352;
} else {
 lean_dec_ref(x_352);
 x_354 = lean_box(0);
}
x_355 = lean_int_mul(x_259, x_249);
lean_dec(x_259);
lean_inc(x_209);
x_356 = l_Int_Linear_Poly_mul(x_209, x_355);
lean_dec(x_355);
x_357 = lean_int_mul(x_260, x_199);
lean_dec(x_260);
lean_inc(x_252);
x_358 = l_Int_Linear_Poly_mul(x_252, x_357);
lean_dec(x_357);
x_359 = lean_int_mul(x_199, x_249);
lean_dec(x_249);
lean_dec(x_199);
x_360 = l_Int_Linear_Poly_combine(x_356, x_358);
lean_inc(x_258);
lean_ctor_set(x_247, 2, x_360);
lean_ctor_set(x_247, 1, x_204);
lean_ctor_set(x_247, 0, x_258);
lean_inc(x_246);
lean_inc(x_201);
if (lean_is_scalar(x_354)) {
 x_361 = lean_alloc_ctor(4, 2, 0);
} else {
 x_361 = x_354;
 lean_ctor_set_tag(x_361, 4);
}
lean_ctor_set(x_361, 0, x_201);
lean_ctor_set(x_361, 1, x_246);
x_362 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_247);
lean_ctor_set(x_362, 2, x_361);
lean_inc(x_210);
lean_inc(x_200);
lean_inc(x_212);
lean_inc(x_203);
lean_inc(x_207);
lean_inc(x_211);
lean_inc(x_202);
lean_inc(x_205);
x_363 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_362, x_205, x_202, x_211, x_207, x_203, x_212, x_200, x_210, x_353);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_365 = x_363;
} else {
 lean_dec_ref(x_363);
 x_365 = lean_box(0);
}
x_366 = l_Int_Linear_Poly_mul(x_209, x_251);
lean_dec(x_251);
x_367 = lean_int_neg(x_213);
lean_dec(x_213);
x_368 = l_Int_Linear_Poly_mul(x_252, x_367);
lean_dec(x_367);
x_369 = l_Int_Linear_Poly_combine(x_366, x_368);
lean_inc(x_246);
if (lean_is_scalar(x_365)) {
 x_370 = lean_alloc_ctor(5, 2, 0);
} else {
 x_370 = x_365;
 lean_ctor_set_tag(x_370, 5);
}
lean_ctor_set(x_370, 0, x_201);
lean_ctor_set(x_370, 1, x_246);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 lean_ctor_release(x_246, 2);
 x_371 = x_246;
} else {
 lean_dec_ref(x_246);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(0, 3, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_258);
lean_ctor_set(x_372, 1, x_369);
lean_ctor_set(x_372, 2, x_370);
x_1 = x_372;
x_2 = x_205;
x_3 = x_202;
x_4 = x_211;
x_5 = x_207;
x_6 = x_203;
x_7 = x_212;
x_8 = x_200;
x_9 = x_210;
x_10 = x_364;
goto _start;
}
else
{
lean_dec(x_258);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_246);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_207);
lean_dec(x_205);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
return x_363;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_374 = lean_ctor_get(x_263, 0);
x_375 = lean_ctor_get(x_263, 2);
x_376 = lean_ctor_get(x_263, 3);
lean_inc(x_376);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_263);
x_377 = lean_ctor_get(x_264, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_264, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_264, 2);
lean_inc(x_379);
x_380 = lean_ctor_get(x_264, 3);
lean_inc(x_380);
x_381 = lean_ctor_get(x_264, 4);
lean_inc(x_381);
x_382 = lean_ctor_get(x_264, 5);
lean_inc(x_382);
x_383 = lean_ctor_get(x_264, 6);
lean_inc(x_383);
x_384 = lean_ctor_get(x_264, 7);
lean_inc(x_384);
x_385 = lean_ctor_get(x_264, 8);
lean_inc(x_385);
x_386 = lean_ctor_get(x_264, 9);
lean_inc(x_386);
x_387 = lean_ctor_get(x_264, 10);
lean_inc(x_387);
x_388 = lean_ctor_get(x_264, 11);
lean_inc(x_388);
x_389 = lean_ctor_get(x_264, 12);
lean_inc(x_389);
x_390 = lean_ctor_get(x_264, 13);
lean_inc(x_390);
x_391 = lean_ctor_get_uint8(x_264, sizeof(void*)*19);
x_392 = lean_ctor_get(x_264, 14);
lean_inc(x_392);
x_393 = lean_ctor_get(x_264, 15);
lean_inc(x_393);
x_394 = lean_ctor_get(x_264, 16);
lean_inc(x_394);
x_395 = lean_ctor_get(x_264, 17);
lean_inc(x_395);
x_396 = lean_ctor_get(x_264, 18);
lean_inc(x_396);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 lean_ctor_release(x_264, 2);
 lean_ctor_release(x_264, 3);
 lean_ctor_release(x_264, 4);
 lean_ctor_release(x_264, 5);
 lean_ctor_release(x_264, 6);
 lean_ctor_release(x_264, 7);
 lean_ctor_release(x_264, 8);
 lean_ctor_release(x_264, 9);
 lean_ctor_release(x_264, 10);
 lean_ctor_release(x_264, 11);
 lean_ctor_release(x_264, 12);
 lean_ctor_release(x_264, 13);
 lean_ctor_release(x_264, 14);
 lean_ctor_release(x_264, 15);
 lean_ctor_release(x_264, 16);
 lean_ctor_release(x_264, 17);
 lean_ctor_release(x_264, 18);
 x_397 = x_264;
} else {
 lean_dec_ref(x_264);
 x_397 = lean_box(0);
}
x_398 = lean_box(0);
x_399 = l_Lean_PersistentArray_set___redArg(x_382, x_204, x_398);
if (lean_is_scalar(x_397)) {
 x_400 = lean_alloc_ctor(0, 19, 1);
} else {
 x_400 = x_397;
}
lean_ctor_set(x_400, 0, x_377);
lean_ctor_set(x_400, 1, x_378);
lean_ctor_set(x_400, 2, x_379);
lean_ctor_set(x_400, 3, x_380);
lean_ctor_set(x_400, 4, x_381);
lean_ctor_set(x_400, 5, x_399);
lean_ctor_set(x_400, 6, x_383);
lean_ctor_set(x_400, 7, x_384);
lean_ctor_set(x_400, 8, x_385);
lean_ctor_set(x_400, 9, x_386);
lean_ctor_set(x_400, 10, x_387);
lean_ctor_set(x_400, 11, x_388);
lean_ctor_set(x_400, 12, x_389);
lean_ctor_set(x_400, 13, x_390);
lean_ctor_set(x_400, 14, x_392);
lean_ctor_set(x_400, 15, x_393);
lean_ctor_set(x_400, 16, x_394);
lean_ctor_set(x_400, 17, x_395);
lean_ctor_set(x_400, 18, x_396);
lean_ctor_set_uint8(x_400, sizeof(void*)*19, x_391);
x_401 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_401, 0, x_374);
lean_ctor_set(x_401, 1, x_400);
lean_ctor_set(x_401, 2, x_375);
lean_ctor_set(x_401, 3, x_376);
lean_ctor_set(x_262, 14, x_401);
x_402 = lean_st_ref_set(x_205, x_262, x_265);
x_403 = lean_ctor_get(x_402, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 x_404 = x_402;
} else {
 lean_dec_ref(x_402);
 x_404 = lean_box(0);
}
x_405 = lean_int_mul(x_259, x_249);
lean_dec(x_259);
lean_inc(x_209);
x_406 = l_Int_Linear_Poly_mul(x_209, x_405);
lean_dec(x_405);
x_407 = lean_int_mul(x_260, x_199);
lean_dec(x_260);
lean_inc(x_252);
x_408 = l_Int_Linear_Poly_mul(x_252, x_407);
lean_dec(x_407);
x_409 = lean_int_mul(x_199, x_249);
lean_dec(x_249);
lean_dec(x_199);
x_410 = l_Int_Linear_Poly_combine(x_406, x_408);
lean_inc(x_258);
lean_ctor_set(x_247, 2, x_410);
lean_ctor_set(x_247, 1, x_204);
lean_ctor_set(x_247, 0, x_258);
lean_inc(x_246);
lean_inc(x_201);
if (lean_is_scalar(x_404)) {
 x_411 = lean_alloc_ctor(4, 2, 0);
} else {
 x_411 = x_404;
 lean_ctor_set_tag(x_411, 4);
}
lean_ctor_set(x_411, 0, x_201);
lean_ctor_set(x_411, 1, x_246);
x_412 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_412, 0, x_409);
lean_ctor_set(x_412, 1, x_247);
lean_ctor_set(x_412, 2, x_411);
lean_inc(x_210);
lean_inc(x_200);
lean_inc(x_212);
lean_inc(x_203);
lean_inc(x_207);
lean_inc(x_211);
lean_inc(x_202);
lean_inc(x_205);
x_413 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_412, x_205, x_202, x_211, x_207, x_203, x_212, x_200, x_210, x_403);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_415 = x_413;
} else {
 lean_dec_ref(x_413);
 x_415 = lean_box(0);
}
x_416 = l_Int_Linear_Poly_mul(x_209, x_251);
lean_dec(x_251);
x_417 = lean_int_neg(x_213);
lean_dec(x_213);
x_418 = l_Int_Linear_Poly_mul(x_252, x_417);
lean_dec(x_417);
x_419 = l_Int_Linear_Poly_combine(x_416, x_418);
lean_inc(x_246);
if (lean_is_scalar(x_415)) {
 x_420 = lean_alloc_ctor(5, 2, 0);
} else {
 x_420 = x_415;
 lean_ctor_set_tag(x_420, 5);
}
lean_ctor_set(x_420, 0, x_201);
lean_ctor_set(x_420, 1, x_246);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 lean_ctor_release(x_246, 2);
 x_421 = x_246;
} else {
 lean_dec_ref(x_246);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(0, 3, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_258);
lean_ctor_set(x_422, 1, x_419);
lean_ctor_set(x_422, 2, x_420);
x_1 = x_422;
x_2 = x_205;
x_3 = x_202;
x_4 = x_211;
x_5 = x_207;
x_6 = x_203;
x_7 = x_212;
x_8 = x_200;
x_9 = x_210;
x_10 = x_414;
goto _start;
}
else
{
lean_dec(x_258);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_246);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_207);
lean_dec(x_205);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
return x_413;
}
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_424 = lean_ctor_get(x_262, 0);
x_425 = lean_ctor_get(x_262, 1);
x_426 = lean_ctor_get(x_262, 2);
x_427 = lean_ctor_get(x_262, 3);
x_428 = lean_ctor_get(x_262, 4);
x_429 = lean_ctor_get(x_262, 5);
x_430 = lean_ctor_get(x_262, 6);
x_431 = lean_ctor_get(x_262, 7);
x_432 = lean_ctor_get_uint8(x_262, sizeof(void*)*16);
x_433 = lean_ctor_get(x_262, 8);
x_434 = lean_ctor_get(x_262, 9);
x_435 = lean_ctor_get(x_262, 10);
x_436 = lean_ctor_get(x_262, 11);
x_437 = lean_ctor_get(x_262, 12);
x_438 = lean_ctor_get(x_262, 13);
x_439 = lean_ctor_get(x_262, 15);
lean_inc(x_439);
lean_inc(x_438);
lean_inc(x_437);
lean_inc(x_436);
lean_inc(x_435);
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_431);
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_428);
lean_inc(x_427);
lean_inc(x_426);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_262);
x_440 = lean_ctor_get(x_263, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_263, 2);
lean_inc(x_441);
x_442 = lean_ctor_get(x_263, 3);
lean_inc(x_442);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 lean_ctor_release(x_263, 2);
 lean_ctor_release(x_263, 3);
 x_443 = x_263;
} else {
 lean_dec_ref(x_263);
 x_443 = lean_box(0);
}
x_444 = lean_ctor_get(x_264, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_264, 1);
lean_inc(x_445);
x_446 = lean_ctor_get(x_264, 2);
lean_inc(x_446);
x_447 = lean_ctor_get(x_264, 3);
lean_inc(x_447);
x_448 = lean_ctor_get(x_264, 4);
lean_inc(x_448);
x_449 = lean_ctor_get(x_264, 5);
lean_inc(x_449);
x_450 = lean_ctor_get(x_264, 6);
lean_inc(x_450);
x_451 = lean_ctor_get(x_264, 7);
lean_inc(x_451);
x_452 = lean_ctor_get(x_264, 8);
lean_inc(x_452);
x_453 = lean_ctor_get(x_264, 9);
lean_inc(x_453);
x_454 = lean_ctor_get(x_264, 10);
lean_inc(x_454);
x_455 = lean_ctor_get(x_264, 11);
lean_inc(x_455);
x_456 = lean_ctor_get(x_264, 12);
lean_inc(x_456);
x_457 = lean_ctor_get(x_264, 13);
lean_inc(x_457);
x_458 = lean_ctor_get_uint8(x_264, sizeof(void*)*19);
x_459 = lean_ctor_get(x_264, 14);
lean_inc(x_459);
x_460 = lean_ctor_get(x_264, 15);
lean_inc(x_460);
x_461 = lean_ctor_get(x_264, 16);
lean_inc(x_461);
x_462 = lean_ctor_get(x_264, 17);
lean_inc(x_462);
x_463 = lean_ctor_get(x_264, 18);
lean_inc(x_463);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 lean_ctor_release(x_264, 2);
 lean_ctor_release(x_264, 3);
 lean_ctor_release(x_264, 4);
 lean_ctor_release(x_264, 5);
 lean_ctor_release(x_264, 6);
 lean_ctor_release(x_264, 7);
 lean_ctor_release(x_264, 8);
 lean_ctor_release(x_264, 9);
 lean_ctor_release(x_264, 10);
 lean_ctor_release(x_264, 11);
 lean_ctor_release(x_264, 12);
 lean_ctor_release(x_264, 13);
 lean_ctor_release(x_264, 14);
 lean_ctor_release(x_264, 15);
 lean_ctor_release(x_264, 16);
 lean_ctor_release(x_264, 17);
 lean_ctor_release(x_264, 18);
 x_464 = x_264;
} else {
 lean_dec_ref(x_264);
 x_464 = lean_box(0);
}
x_465 = lean_box(0);
x_466 = l_Lean_PersistentArray_set___redArg(x_449, x_204, x_465);
if (lean_is_scalar(x_464)) {
 x_467 = lean_alloc_ctor(0, 19, 1);
} else {
 x_467 = x_464;
}
lean_ctor_set(x_467, 0, x_444);
lean_ctor_set(x_467, 1, x_445);
lean_ctor_set(x_467, 2, x_446);
lean_ctor_set(x_467, 3, x_447);
lean_ctor_set(x_467, 4, x_448);
lean_ctor_set(x_467, 5, x_466);
lean_ctor_set(x_467, 6, x_450);
lean_ctor_set(x_467, 7, x_451);
lean_ctor_set(x_467, 8, x_452);
lean_ctor_set(x_467, 9, x_453);
lean_ctor_set(x_467, 10, x_454);
lean_ctor_set(x_467, 11, x_455);
lean_ctor_set(x_467, 12, x_456);
lean_ctor_set(x_467, 13, x_457);
lean_ctor_set(x_467, 14, x_459);
lean_ctor_set(x_467, 15, x_460);
lean_ctor_set(x_467, 16, x_461);
lean_ctor_set(x_467, 17, x_462);
lean_ctor_set(x_467, 18, x_463);
lean_ctor_set_uint8(x_467, sizeof(void*)*19, x_458);
if (lean_is_scalar(x_443)) {
 x_468 = lean_alloc_ctor(0, 4, 0);
} else {
 x_468 = x_443;
}
lean_ctor_set(x_468, 0, x_440);
lean_ctor_set(x_468, 1, x_467);
lean_ctor_set(x_468, 2, x_441);
lean_ctor_set(x_468, 3, x_442);
x_469 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_469, 0, x_424);
lean_ctor_set(x_469, 1, x_425);
lean_ctor_set(x_469, 2, x_426);
lean_ctor_set(x_469, 3, x_427);
lean_ctor_set(x_469, 4, x_428);
lean_ctor_set(x_469, 5, x_429);
lean_ctor_set(x_469, 6, x_430);
lean_ctor_set(x_469, 7, x_431);
lean_ctor_set(x_469, 8, x_433);
lean_ctor_set(x_469, 9, x_434);
lean_ctor_set(x_469, 10, x_435);
lean_ctor_set(x_469, 11, x_436);
lean_ctor_set(x_469, 12, x_437);
lean_ctor_set(x_469, 13, x_438);
lean_ctor_set(x_469, 14, x_468);
lean_ctor_set(x_469, 15, x_439);
lean_ctor_set_uint8(x_469, sizeof(void*)*16, x_432);
x_470 = lean_st_ref_set(x_205, x_469, x_265);
x_471 = lean_ctor_get(x_470, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_472 = x_470;
} else {
 lean_dec_ref(x_470);
 x_472 = lean_box(0);
}
x_473 = lean_int_mul(x_259, x_249);
lean_dec(x_259);
lean_inc(x_209);
x_474 = l_Int_Linear_Poly_mul(x_209, x_473);
lean_dec(x_473);
x_475 = lean_int_mul(x_260, x_199);
lean_dec(x_260);
lean_inc(x_252);
x_476 = l_Int_Linear_Poly_mul(x_252, x_475);
lean_dec(x_475);
x_477 = lean_int_mul(x_199, x_249);
lean_dec(x_249);
lean_dec(x_199);
x_478 = l_Int_Linear_Poly_combine(x_474, x_476);
lean_inc(x_258);
lean_ctor_set(x_247, 2, x_478);
lean_ctor_set(x_247, 1, x_204);
lean_ctor_set(x_247, 0, x_258);
lean_inc(x_246);
lean_inc(x_201);
if (lean_is_scalar(x_472)) {
 x_479 = lean_alloc_ctor(4, 2, 0);
} else {
 x_479 = x_472;
 lean_ctor_set_tag(x_479, 4);
}
lean_ctor_set(x_479, 0, x_201);
lean_ctor_set(x_479, 1, x_246);
x_480 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_480, 0, x_477);
lean_ctor_set(x_480, 1, x_247);
lean_ctor_set(x_480, 2, x_479);
lean_inc(x_210);
lean_inc(x_200);
lean_inc(x_212);
lean_inc(x_203);
lean_inc(x_207);
lean_inc(x_211);
lean_inc(x_202);
lean_inc(x_205);
x_481 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_480, x_205, x_202, x_211, x_207, x_203, x_212, x_200, x_210, x_471);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_483 = x_481;
} else {
 lean_dec_ref(x_481);
 x_483 = lean_box(0);
}
x_484 = l_Int_Linear_Poly_mul(x_209, x_251);
lean_dec(x_251);
x_485 = lean_int_neg(x_213);
lean_dec(x_213);
x_486 = l_Int_Linear_Poly_mul(x_252, x_485);
lean_dec(x_485);
x_487 = l_Int_Linear_Poly_combine(x_484, x_486);
lean_inc(x_246);
if (lean_is_scalar(x_483)) {
 x_488 = lean_alloc_ctor(5, 2, 0);
} else {
 x_488 = x_483;
 lean_ctor_set_tag(x_488, 5);
}
lean_ctor_set(x_488, 0, x_201);
lean_ctor_set(x_488, 1, x_246);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 lean_ctor_release(x_246, 2);
 x_489 = x_246;
} else {
 lean_dec_ref(x_246);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(0, 3, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_258);
lean_ctor_set(x_490, 1, x_487);
lean_ctor_set(x_490, 2, x_488);
x_1 = x_490;
x_2 = x_205;
x_3 = x_202;
x_4 = x_211;
x_5 = x_207;
x_6 = x_203;
x_7 = x_212;
x_8 = x_200;
x_9 = x_210;
x_10 = x_482;
goto _start;
}
else
{
lean_dec(x_258);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_246);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_207);
lean_dec(x_205);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
return x_481;
}
}
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; uint8_t x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_492 = lean_ctor_get(x_247, 0);
x_493 = lean_ctor_get(x_247, 2);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_247);
x_494 = lean_int_mul(x_213, x_249);
x_495 = lean_int_mul(x_492, x_199);
x_496 = l_Lean_Meta_Grind_Arith_gcdExt(x_494, x_495);
lean_dec(x_495);
lean_dec(x_494);
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 0);
lean_inc(x_498);
lean_dec(x_496);
x_499 = lean_ctor_get(x_497, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_497, 1);
lean_inc(x_500);
lean_dec(x_497);
x_501 = lean_st_ref_take(x_205, x_208);
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_502, 14);
lean_inc(x_503);
x_504 = lean_ctor_get(x_503, 1);
lean_inc(x_504);
x_505 = lean_ctor_get(x_501, 1);
lean_inc(x_505);
lean_dec(x_501);
x_506 = lean_ctor_get(x_502, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_502, 1);
lean_inc(x_507);
x_508 = lean_ctor_get(x_502, 2);
lean_inc(x_508);
x_509 = lean_ctor_get(x_502, 3);
lean_inc(x_509);
x_510 = lean_ctor_get(x_502, 4);
lean_inc(x_510);
x_511 = lean_ctor_get(x_502, 5);
lean_inc(x_511);
x_512 = lean_ctor_get(x_502, 6);
lean_inc(x_512);
x_513 = lean_ctor_get(x_502, 7);
lean_inc(x_513);
x_514 = lean_ctor_get_uint8(x_502, sizeof(void*)*16);
x_515 = lean_ctor_get(x_502, 8);
lean_inc(x_515);
x_516 = lean_ctor_get(x_502, 9);
lean_inc(x_516);
x_517 = lean_ctor_get(x_502, 10);
lean_inc(x_517);
x_518 = lean_ctor_get(x_502, 11);
lean_inc(x_518);
x_519 = lean_ctor_get(x_502, 12);
lean_inc(x_519);
x_520 = lean_ctor_get(x_502, 13);
lean_inc(x_520);
x_521 = lean_ctor_get(x_502, 15);
lean_inc(x_521);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 lean_ctor_release(x_502, 2);
 lean_ctor_release(x_502, 3);
 lean_ctor_release(x_502, 4);
 lean_ctor_release(x_502, 5);
 lean_ctor_release(x_502, 6);
 lean_ctor_release(x_502, 7);
 lean_ctor_release(x_502, 8);
 lean_ctor_release(x_502, 9);
 lean_ctor_release(x_502, 10);
 lean_ctor_release(x_502, 11);
 lean_ctor_release(x_502, 12);
 lean_ctor_release(x_502, 13);
 lean_ctor_release(x_502, 14);
 lean_ctor_release(x_502, 15);
 x_522 = x_502;
} else {
 lean_dec_ref(x_502);
 x_522 = lean_box(0);
}
x_523 = lean_ctor_get(x_503, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_503, 2);
lean_inc(x_524);
x_525 = lean_ctor_get(x_503, 3);
lean_inc(x_525);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 lean_ctor_release(x_503, 2);
 lean_ctor_release(x_503, 3);
 x_526 = x_503;
} else {
 lean_dec_ref(x_503);
 x_526 = lean_box(0);
}
x_527 = lean_ctor_get(x_504, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_504, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_504, 2);
lean_inc(x_529);
x_530 = lean_ctor_get(x_504, 3);
lean_inc(x_530);
x_531 = lean_ctor_get(x_504, 4);
lean_inc(x_531);
x_532 = lean_ctor_get(x_504, 5);
lean_inc(x_532);
x_533 = lean_ctor_get(x_504, 6);
lean_inc(x_533);
x_534 = lean_ctor_get(x_504, 7);
lean_inc(x_534);
x_535 = lean_ctor_get(x_504, 8);
lean_inc(x_535);
x_536 = lean_ctor_get(x_504, 9);
lean_inc(x_536);
x_537 = lean_ctor_get(x_504, 10);
lean_inc(x_537);
x_538 = lean_ctor_get(x_504, 11);
lean_inc(x_538);
x_539 = lean_ctor_get(x_504, 12);
lean_inc(x_539);
x_540 = lean_ctor_get(x_504, 13);
lean_inc(x_540);
x_541 = lean_ctor_get_uint8(x_504, sizeof(void*)*19);
x_542 = lean_ctor_get(x_504, 14);
lean_inc(x_542);
x_543 = lean_ctor_get(x_504, 15);
lean_inc(x_543);
x_544 = lean_ctor_get(x_504, 16);
lean_inc(x_544);
x_545 = lean_ctor_get(x_504, 17);
lean_inc(x_545);
x_546 = lean_ctor_get(x_504, 18);
lean_inc(x_546);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 lean_ctor_release(x_504, 1);
 lean_ctor_release(x_504, 2);
 lean_ctor_release(x_504, 3);
 lean_ctor_release(x_504, 4);
 lean_ctor_release(x_504, 5);
 lean_ctor_release(x_504, 6);
 lean_ctor_release(x_504, 7);
 lean_ctor_release(x_504, 8);
 lean_ctor_release(x_504, 9);
 lean_ctor_release(x_504, 10);
 lean_ctor_release(x_504, 11);
 lean_ctor_release(x_504, 12);
 lean_ctor_release(x_504, 13);
 lean_ctor_release(x_504, 14);
 lean_ctor_release(x_504, 15);
 lean_ctor_release(x_504, 16);
 lean_ctor_release(x_504, 17);
 lean_ctor_release(x_504, 18);
 x_547 = x_504;
} else {
 lean_dec_ref(x_504);
 x_547 = lean_box(0);
}
x_548 = lean_box(0);
x_549 = l_Lean_PersistentArray_set___redArg(x_532, x_204, x_548);
if (lean_is_scalar(x_547)) {
 x_550 = lean_alloc_ctor(0, 19, 1);
} else {
 x_550 = x_547;
}
lean_ctor_set(x_550, 0, x_527);
lean_ctor_set(x_550, 1, x_528);
lean_ctor_set(x_550, 2, x_529);
lean_ctor_set(x_550, 3, x_530);
lean_ctor_set(x_550, 4, x_531);
lean_ctor_set(x_550, 5, x_549);
lean_ctor_set(x_550, 6, x_533);
lean_ctor_set(x_550, 7, x_534);
lean_ctor_set(x_550, 8, x_535);
lean_ctor_set(x_550, 9, x_536);
lean_ctor_set(x_550, 10, x_537);
lean_ctor_set(x_550, 11, x_538);
lean_ctor_set(x_550, 12, x_539);
lean_ctor_set(x_550, 13, x_540);
lean_ctor_set(x_550, 14, x_542);
lean_ctor_set(x_550, 15, x_543);
lean_ctor_set(x_550, 16, x_544);
lean_ctor_set(x_550, 17, x_545);
lean_ctor_set(x_550, 18, x_546);
lean_ctor_set_uint8(x_550, sizeof(void*)*19, x_541);
if (lean_is_scalar(x_526)) {
 x_551 = lean_alloc_ctor(0, 4, 0);
} else {
 x_551 = x_526;
}
lean_ctor_set(x_551, 0, x_523);
lean_ctor_set(x_551, 1, x_550);
lean_ctor_set(x_551, 2, x_524);
lean_ctor_set(x_551, 3, x_525);
if (lean_is_scalar(x_522)) {
 x_552 = lean_alloc_ctor(0, 16, 1);
} else {
 x_552 = x_522;
}
lean_ctor_set(x_552, 0, x_506);
lean_ctor_set(x_552, 1, x_507);
lean_ctor_set(x_552, 2, x_508);
lean_ctor_set(x_552, 3, x_509);
lean_ctor_set(x_552, 4, x_510);
lean_ctor_set(x_552, 5, x_511);
lean_ctor_set(x_552, 6, x_512);
lean_ctor_set(x_552, 7, x_513);
lean_ctor_set(x_552, 8, x_515);
lean_ctor_set(x_552, 9, x_516);
lean_ctor_set(x_552, 10, x_517);
lean_ctor_set(x_552, 11, x_518);
lean_ctor_set(x_552, 12, x_519);
lean_ctor_set(x_552, 13, x_520);
lean_ctor_set(x_552, 14, x_551);
lean_ctor_set(x_552, 15, x_521);
lean_ctor_set_uint8(x_552, sizeof(void*)*16, x_514);
x_553 = lean_st_ref_set(x_205, x_552, x_505);
x_554 = lean_ctor_get(x_553, 1);
lean_inc(x_554);
if (lean_is_exclusive(x_553)) {
 lean_ctor_release(x_553, 0);
 lean_ctor_release(x_553, 1);
 x_555 = x_553;
} else {
 lean_dec_ref(x_553);
 x_555 = lean_box(0);
}
x_556 = lean_int_mul(x_499, x_249);
lean_dec(x_499);
lean_inc(x_209);
x_557 = l_Int_Linear_Poly_mul(x_209, x_556);
lean_dec(x_556);
x_558 = lean_int_mul(x_500, x_199);
lean_dec(x_500);
lean_inc(x_493);
x_559 = l_Int_Linear_Poly_mul(x_493, x_558);
lean_dec(x_558);
x_560 = lean_int_mul(x_199, x_249);
lean_dec(x_249);
lean_dec(x_199);
x_561 = l_Int_Linear_Poly_combine(x_557, x_559);
lean_inc(x_498);
x_562 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_562, 0, x_498);
lean_ctor_set(x_562, 1, x_204);
lean_ctor_set(x_562, 2, x_561);
lean_inc(x_246);
lean_inc(x_201);
if (lean_is_scalar(x_555)) {
 x_563 = lean_alloc_ctor(4, 2, 0);
} else {
 x_563 = x_555;
 lean_ctor_set_tag(x_563, 4);
}
lean_ctor_set(x_563, 0, x_201);
lean_ctor_set(x_563, 1, x_246);
x_564 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_564, 0, x_560);
lean_ctor_set(x_564, 1, x_562);
lean_ctor_set(x_564, 2, x_563);
lean_inc(x_210);
lean_inc(x_200);
lean_inc(x_212);
lean_inc(x_203);
lean_inc(x_207);
lean_inc(x_211);
lean_inc(x_202);
lean_inc(x_205);
x_565 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_564, x_205, x_202, x_211, x_207, x_203, x_212, x_200, x_210, x_554);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_566 = lean_ctor_get(x_565, 1);
lean_inc(x_566);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_567 = x_565;
} else {
 lean_dec_ref(x_565);
 x_567 = lean_box(0);
}
x_568 = l_Int_Linear_Poly_mul(x_209, x_492);
lean_dec(x_492);
x_569 = lean_int_neg(x_213);
lean_dec(x_213);
x_570 = l_Int_Linear_Poly_mul(x_493, x_569);
lean_dec(x_569);
x_571 = l_Int_Linear_Poly_combine(x_568, x_570);
lean_inc(x_246);
if (lean_is_scalar(x_567)) {
 x_572 = lean_alloc_ctor(5, 2, 0);
} else {
 x_572 = x_567;
 lean_ctor_set_tag(x_572, 5);
}
lean_ctor_set(x_572, 0, x_201);
lean_ctor_set(x_572, 1, x_246);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 lean_ctor_release(x_246, 2);
 x_573 = x_246;
} else {
 lean_dec_ref(x_246);
 x_573 = lean_box(0);
}
if (lean_is_scalar(x_573)) {
 x_574 = lean_alloc_ctor(0, 3, 0);
} else {
 x_574 = x_573;
}
lean_ctor_set(x_574, 0, x_498);
lean_ctor_set(x_574, 1, x_571);
lean_ctor_set(x_574, 2, x_572);
x_1 = x_574;
x_2 = x_205;
x_3 = x_202;
x_4 = x_211;
x_5 = x_207;
x_6 = x_203;
x_7 = x_212;
x_8 = x_200;
x_9 = x_210;
x_10 = x_566;
goto _start;
}
else
{
lean_dec(x_498);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_246);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_207);
lean_dec(x_205);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
return x_565;
}
}
}
}
}
}
else
{
uint8_t x_822; 
lean_free_object(x_8);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_822 = !lean_is_exclusive(x_193);
if (x_822 == 0)
{
lean_object* x_823; lean_object* x_824; 
x_823 = lean_ctor_get(x_193, 0);
lean_dec(x_823);
x_824 = lean_box(0);
lean_ctor_set(x_193, 0, x_824);
return x_193;
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_825 = lean_ctor_get(x_193, 1);
lean_inc(x_825);
lean_dec(x_193);
x_826 = lean_box(0);
x_827 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_825);
return x_827;
}
}
}
else
{
lean_object* x_828; 
lean_free_object(x_8);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_828 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_184, x_10);
return x_828;
}
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; uint8_t x_840; lean_object* x_841; uint8_t x_842; lean_object* x_843; uint8_t x_844; 
x_829 = lean_ctor_get(x_8, 0);
x_830 = lean_ctor_get(x_8, 1);
x_831 = lean_ctor_get(x_8, 2);
x_832 = lean_ctor_get(x_8, 3);
x_833 = lean_ctor_get(x_8, 4);
x_834 = lean_ctor_get(x_8, 5);
x_835 = lean_ctor_get(x_8, 6);
x_836 = lean_ctor_get(x_8, 7);
x_837 = lean_ctor_get(x_8, 8);
x_838 = lean_ctor_get(x_8, 9);
x_839 = lean_ctor_get(x_8, 10);
x_840 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_841 = lean_ctor_get(x_8, 11);
x_842 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_843 = lean_ctor_get(x_8, 12);
lean_inc(x_843);
lean_inc(x_841);
lean_inc(x_839);
lean_inc(x_838);
lean_inc(x_837);
lean_inc(x_836);
lean_inc(x_835);
lean_inc(x_834);
lean_inc(x_833);
lean_inc(x_832);
lean_inc(x_831);
lean_inc(x_830);
lean_inc(x_829);
lean_dec(x_8);
x_844 = lean_nat_dec_eq(x_832, x_833);
if (x_844 == 0)
{
lean_object* x_845; lean_object* x_846; uint8_t x_847; 
x_845 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
x_847 = lean_unbox(x_846);
lean_dec(x_846);
if (x_847 == 0)
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; uint8_t x_1071; 
x_848 = lean_ctor_get(x_845, 1);
lean_inc(x_848);
lean_dec(x_845);
x_849 = lean_unsigned_to_nat(1u);
x_850 = lean_nat_add(x_832, x_849);
lean_dec(x_832);
x_851 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_851, 0, x_829);
lean_ctor_set(x_851, 1, x_830);
lean_ctor_set(x_851, 2, x_831);
lean_ctor_set(x_851, 3, x_850);
lean_ctor_set(x_851, 4, x_833);
lean_ctor_set(x_851, 5, x_834);
lean_ctor_set(x_851, 6, x_835);
lean_ctor_set(x_851, 7, x_836);
lean_ctor_set(x_851, 8, x_837);
lean_ctor_set(x_851, 9, x_838);
lean_ctor_set(x_851, 10, x_839);
lean_ctor_set(x_851, 11, x_841);
lean_ctor_set(x_851, 12, x_843);
lean_ctor_set_uint8(x_851, sizeof(void*)*13, x_840);
lean_ctor_set_uint8(x_851, sizeof(void*)*13 + 1, x_842);
x_974 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_975 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_974, x_851, x_848);
x_976 = lean_ctor_get(x_975, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_975, 1);
lean_inc(x_977);
if (lean_is_exclusive(x_975)) {
 lean_ctor_release(x_975, 0);
 lean_ctor_release(x_975, 1);
 x_978 = x_975;
} else {
 lean_dec_ref(x_975);
 x_978 = lean_box(0);
}
x_979 = lean_box(0);
x_1071 = lean_unbox(x_976);
lean_dec(x_976);
if (x_1071 == 0)
{
lean_dec(x_978);
x_1004 = x_2;
x_1005 = x_3;
x_1006 = x_4;
x_1007 = x_5;
x_1008 = x_6;
x_1009 = x_7;
x_1010 = x_851;
x_1011 = x_9;
x_1012 = x_977;
goto block_1070;
}
else
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
lean_inc(x_1);
x_1072 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_977);
x_1073 = lean_ctor_get(x_1072, 0);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_1072, 1);
lean_inc(x_1074);
if (lean_is_exclusive(x_1072)) {
 lean_ctor_release(x_1072, 0);
 lean_ctor_release(x_1072, 1);
 x_1075 = x_1072;
} else {
 lean_dec_ref(x_1072);
 x_1075 = lean_box(0);
}
x_1076 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1075)) {
 x_1077 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1077 = x_1075;
 lean_ctor_set_tag(x_1077, 7);
}
lean_ctor_set(x_1077, 0, x_1076);
lean_ctor_set(x_1077, 1, x_1073);
if (lean_is_scalar(x_978)) {
 x_1078 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1078 = x_978;
 lean_ctor_set_tag(x_1078, 7);
}
lean_ctor_set(x_1078, 0, x_1077);
lean_ctor_set(x_1078, 1, x_1076);
x_1079 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_974, x_1078, x_6, x_7, x_851, x_9, x_1074);
x_1080 = lean_ctor_get(x_1079, 1);
lean_inc(x_1080);
lean_dec(x_1079);
x_1004 = x_2;
x_1005 = x_3;
x_1006 = x_4;
x_1007 = x_5;
x_1008 = x_6;
x_1009 = x_7;
x_1010 = x_851;
x_1011 = x_9;
x_1012 = x_1080;
goto block_1070;
}
block_973:
{
if (lean_obj_tag(x_867) == 0)
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; uint8_t x_871; 
lean_dec(x_866);
lean_dec(x_864);
lean_dec(x_862);
lean_dec(x_860);
lean_dec(x_855);
lean_dec(x_852);
x_868 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_869 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_868, x_853, x_861);
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_unbox(x_870);
lean_dec(x_870);
if (x_871 == 0)
{
lean_object* x_872; 
x_872 = lean_ctor_get(x_869, 1);
lean_inc(x_872);
lean_dec(x_869);
x_11 = x_854;
x_12 = x_857;
x_13 = x_859;
x_14 = x_858;
x_15 = x_856;
x_16 = x_865;
x_17 = x_853;
x_18 = x_863;
x_19 = x_872;
goto block_154;
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_873 = lean_ctor_get(x_869, 1);
lean_inc(x_873);
if (lean_is_exclusive(x_869)) {
 lean_ctor_release(x_869, 0);
 lean_ctor_release(x_869, 1);
 x_874 = x_869;
} else {
 lean_dec_ref(x_869);
 x_874 = lean_box(0);
}
lean_inc(x_854);
x_875 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_854, x_858, x_873);
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
if (lean_is_exclusive(x_875)) {
 lean_ctor_release(x_875, 0);
 lean_ctor_release(x_875, 1);
 x_878 = x_875;
} else {
 lean_dec_ref(x_875);
 x_878 = lean_box(0);
}
x_879 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_878)) {
 x_880 = lean_alloc_ctor(7, 2, 0);
} else {
 x_880 = x_878;
 lean_ctor_set_tag(x_880, 7);
}
lean_ctor_set(x_880, 0, x_879);
lean_ctor_set(x_880, 1, x_876);
if (lean_is_scalar(x_874)) {
 x_881 = lean_alloc_ctor(7, 2, 0);
} else {
 x_881 = x_874;
 lean_ctor_set_tag(x_881, 7);
}
lean_ctor_set(x_881, 0, x_880);
lean_ctor_set(x_881, 1, x_879);
x_882 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_868, x_881, x_856, x_865, x_853, x_863, x_877);
x_883 = lean_ctor_get(x_882, 1);
lean_inc(x_883);
lean_dec(x_882);
x_11 = x_854;
x_12 = x_857;
x_13 = x_859;
x_14 = x_858;
x_15 = x_856;
x_16 = x_865;
x_17 = x_853;
x_18 = x_863;
x_19 = x_883;
goto block_154;
}
}
else
{
lean_object* x_884; lean_object* x_885; 
lean_dec(x_859);
x_884 = lean_ctor_get(x_867, 0);
lean_inc(x_884);
lean_dec(x_867);
x_885 = lean_ctor_get(x_884, 1);
lean_inc(x_885);
if (lean_obj_tag(x_885) == 0)
{
lean_object* x_886; 
lean_dec(x_885);
lean_dec(x_866);
lean_dec(x_864);
lean_dec(x_862);
lean_dec(x_860);
lean_dec(x_857);
lean_dec(x_855);
lean_dec(x_854);
lean_dec(x_852);
x_886 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_884, x_858, x_856, x_865, x_853, x_863, x_861);
lean_dec(x_863);
lean_dec(x_853);
lean_dec(x_865);
lean_dec(x_856);
lean_dec(x_858);
return x_886;
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; uint8_t x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; uint8_t x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
x_887 = lean_ctor_get(x_884, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_885, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_885, 2);
lean_inc(x_889);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 lean_ctor_release(x_885, 1);
 lean_ctor_release(x_885, 2);
 x_890 = x_885;
} else {
 lean_dec_ref(x_885);
 x_890 = lean_box(0);
}
x_891 = lean_int_mul(x_866, x_887);
x_892 = lean_int_mul(x_888, x_852);
x_893 = l_Lean_Meta_Grind_Arith_gcdExt(x_891, x_892);
lean_dec(x_892);
lean_dec(x_891);
x_894 = lean_ctor_get(x_893, 1);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 0);
lean_inc(x_895);
lean_dec(x_893);
x_896 = lean_ctor_get(x_894, 0);
lean_inc(x_896);
x_897 = lean_ctor_get(x_894, 1);
lean_inc(x_897);
lean_dec(x_894);
x_898 = lean_st_ref_take(x_858, x_861);
x_899 = lean_ctor_get(x_898, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_899, 14);
lean_inc(x_900);
x_901 = lean_ctor_get(x_900, 1);
lean_inc(x_901);
x_902 = lean_ctor_get(x_898, 1);
lean_inc(x_902);
lean_dec(x_898);
x_903 = lean_ctor_get(x_899, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_899, 1);
lean_inc(x_904);
x_905 = lean_ctor_get(x_899, 2);
lean_inc(x_905);
x_906 = lean_ctor_get(x_899, 3);
lean_inc(x_906);
x_907 = lean_ctor_get(x_899, 4);
lean_inc(x_907);
x_908 = lean_ctor_get(x_899, 5);
lean_inc(x_908);
x_909 = lean_ctor_get(x_899, 6);
lean_inc(x_909);
x_910 = lean_ctor_get(x_899, 7);
lean_inc(x_910);
x_911 = lean_ctor_get_uint8(x_899, sizeof(void*)*16);
x_912 = lean_ctor_get(x_899, 8);
lean_inc(x_912);
x_913 = lean_ctor_get(x_899, 9);
lean_inc(x_913);
x_914 = lean_ctor_get(x_899, 10);
lean_inc(x_914);
x_915 = lean_ctor_get(x_899, 11);
lean_inc(x_915);
x_916 = lean_ctor_get(x_899, 12);
lean_inc(x_916);
x_917 = lean_ctor_get(x_899, 13);
lean_inc(x_917);
x_918 = lean_ctor_get(x_899, 15);
lean_inc(x_918);
if (lean_is_exclusive(x_899)) {
 lean_ctor_release(x_899, 0);
 lean_ctor_release(x_899, 1);
 lean_ctor_release(x_899, 2);
 lean_ctor_release(x_899, 3);
 lean_ctor_release(x_899, 4);
 lean_ctor_release(x_899, 5);
 lean_ctor_release(x_899, 6);
 lean_ctor_release(x_899, 7);
 lean_ctor_release(x_899, 8);
 lean_ctor_release(x_899, 9);
 lean_ctor_release(x_899, 10);
 lean_ctor_release(x_899, 11);
 lean_ctor_release(x_899, 12);
 lean_ctor_release(x_899, 13);
 lean_ctor_release(x_899, 14);
 lean_ctor_release(x_899, 15);
 x_919 = x_899;
} else {
 lean_dec_ref(x_899);
 x_919 = lean_box(0);
}
x_920 = lean_ctor_get(x_900, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_900, 2);
lean_inc(x_921);
x_922 = lean_ctor_get(x_900, 3);
lean_inc(x_922);
if (lean_is_exclusive(x_900)) {
 lean_ctor_release(x_900, 0);
 lean_ctor_release(x_900, 1);
 lean_ctor_release(x_900, 2);
 lean_ctor_release(x_900, 3);
 x_923 = x_900;
} else {
 lean_dec_ref(x_900);
 x_923 = lean_box(0);
}
x_924 = lean_ctor_get(x_901, 0);
lean_inc(x_924);
x_925 = lean_ctor_get(x_901, 1);
lean_inc(x_925);
x_926 = lean_ctor_get(x_901, 2);
lean_inc(x_926);
x_927 = lean_ctor_get(x_901, 3);
lean_inc(x_927);
x_928 = lean_ctor_get(x_901, 4);
lean_inc(x_928);
x_929 = lean_ctor_get(x_901, 5);
lean_inc(x_929);
x_930 = lean_ctor_get(x_901, 6);
lean_inc(x_930);
x_931 = lean_ctor_get(x_901, 7);
lean_inc(x_931);
x_932 = lean_ctor_get(x_901, 8);
lean_inc(x_932);
x_933 = lean_ctor_get(x_901, 9);
lean_inc(x_933);
x_934 = lean_ctor_get(x_901, 10);
lean_inc(x_934);
x_935 = lean_ctor_get(x_901, 11);
lean_inc(x_935);
x_936 = lean_ctor_get(x_901, 12);
lean_inc(x_936);
x_937 = lean_ctor_get(x_901, 13);
lean_inc(x_937);
x_938 = lean_ctor_get_uint8(x_901, sizeof(void*)*19);
x_939 = lean_ctor_get(x_901, 14);
lean_inc(x_939);
x_940 = lean_ctor_get(x_901, 15);
lean_inc(x_940);
x_941 = lean_ctor_get(x_901, 16);
lean_inc(x_941);
x_942 = lean_ctor_get(x_901, 17);
lean_inc(x_942);
x_943 = lean_ctor_get(x_901, 18);
lean_inc(x_943);
if (lean_is_exclusive(x_901)) {
 lean_ctor_release(x_901, 0);
 lean_ctor_release(x_901, 1);
 lean_ctor_release(x_901, 2);
 lean_ctor_release(x_901, 3);
 lean_ctor_release(x_901, 4);
 lean_ctor_release(x_901, 5);
 lean_ctor_release(x_901, 6);
 lean_ctor_release(x_901, 7);
 lean_ctor_release(x_901, 8);
 lean_ctor_release(x_901, 9);
 lean_ctor_release(x_901, 10);
 lean_ctor_release(x_901, 11);
 lean_ctor_release(x_901, 12);
 lean_ctor_release(x_901, 13);
 lean_ctor_release(x_901, 14);
 lean_ctor_release(x_901, 15);
 lean_ctor_release(x_901, 16);
 lean_ctor_release(x_901, 17);
 lean_ctor_release(x_901, 18);
 x_944 = x_901;
} else {
 lean_dec_ref(x_901);
 x_944 = lean_box(0);
}
x_945 = lean_box(0);
x_946 = l_Lean_PersistentArray_set___redArg(x_929, x_857, x_945);
if (lean_is_scalar(x_944)) {
 x_947 = lean_alloc_ctor(0, 19, 1);
} else {
 x_947 = x_944;
}
lean_ctor_set(x_947, 0, x_924);
lean_ctor_set(x_947, 1, x_925);
lean_ctor_set(x_947, 2, x_926);
lean_ctor_set(x_947, 3, x_927);
lean_ctor_set(x_947, 4, x_928);
lean_ctor_set(x_947, 5, x_946);
lean_ctor_set(x_947, 6, x_930);
lean_ctor_set(x_947, 7, x_931);
lean_ctor_set(x_947, 8, x_932);
lean_ctor_set(x_947, 9, x_933);
lean_ctor_set(x_947, 10, x_934);
lean_ctor_set(x_947, 11, x_935);
lean_ctor_set(x_947, 12, x_936);
lean_ctor_set(x_947, 13, x_937);
lean_ctor_set(x_947, 14, x_939);
lean_ctor_set(x_947, 15, x_940);
lean_ctor_set(x_947, 16, x_941);
lean_ctor_set(x_947, 17, x_942);
lean_ctor_set(x_947, 18, x_943);
lean_ctor_set_uint8(x_947, sizeof(void*)*19, x_938);
if (lean_is_scalar(x_923)) {
 x_948 = lean_alloc_ctor(0, 4, 0);
} else {
 x_948 = x_923;
}
lean_ctor_set(x_948, 0, x_920);
lean_ctor_set(x_948, 1, x_947);
lean_ctor_set(x_948, 2, x_921);
lean_ctor_set(x_948, 3, x_922);
if (lean_is_scalar(x_919)) {
 x_949 = lean_alloc_ctor(0, 16, 1);
} else {
 x_949 = x_919;
}
lean_ctor_set(x_949, 0, x_903);
lean_ctor_set(x_949, 1, x_904);
lean_ctor_set(x_949, 2, x_905);
lean_ctor_set(x_949, 3, x_906);
lean_ctor_set(x_949, 4, x_907);
lean_ctor_set(x_949, 5, x_908);
lean_ctor_set(x_949, 6, x_909);
lean_ctor_set(x_949, 7, x_910);
lean_ctor_set(x_949, 8, x_912);
lean_ctor_set(x_949, 9, x_913);
lean_ctor_set(x_949, 10, x_914);
lean_ctor_set(x_949, 11, x_915);
lean_ctor_set(x_949, 12, x_916);
lean_ctor_set(x_949, 13, x_917);
lean_ctor_set(x_949, 14, x_948);
lean_ctor_set(x_949, 15, x_918);
lean_ctor_set_uint8(x_949, sizeof(void*)*16, x_911);
x_950 = lean_st_ref_set(x_858, x_949, x_902);
x_951 = lean_ctor_get(x_950, 1);
lean_inc(x_951);
if (lean_is_exclusive(x_950)) {
 lean_ctor_release(x_950, 0);
 lean_ctor_release(x_950, 1);
 x_952 = x_950;
} else {
 lean_dec_ref(x_950);
 x_952 = lean_box(0);
}
x_953 = lean_int_mul(x_896, x_887);
lean_dec(x_896);
lean_inc(x_862);
x_954 = l_Int_Linear_Poly_mul(x_862, x_953);
lean_dec(x_953);
x_955 = lean_int_mul(x_897, x_852);
lean_dec(x_897);
lean_inc(x_889);
x_956 = l_Int_Linear_Poly_mul(x_889, x_955);
lean_dec(x_955);
x_957 = lean_int_mul(x_852, x_887);
lean_dec(x_887);
lean_dec(x_852);
x_958 = l_Int_Linear_Poly_combine(x_954, x_956);
lean_inc(x_895);
if (lean_is_scalar(x_890)) {
 x_959 = lean_alloc_ctor(1, 3, 0);
} else {
 x_959 = x_890;
}
lean_ctor_set(x_959, 0, x_895);
lean_ctor_set(x_959, 1, x_857);
lean_ctor_set(x_959, 2, x_958);
lean_inc(x_884);
lean_inc(x_854);
if (lean_is_scalar(x_952)) {
 x_960 = lean_alloc_ctor(4, 2, 0);
} else {
 x_960 = x_952;
 lean_ctor_set_tag(x_960, 4);
}
lean_ctor_set(x_960, 0, x_854);
lean_ctor_set(x_960, 1, x_884);
x_961 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_961, 0, x_957);
lean_ctor_set(x_961, 1, x_959);
lean_ctor_set(x_961, 2, x_960);
lean_inc(x_863);
lean_inc(x_853);
lean_inc(x_865);
lean_inc(x_856);
lean_inc(x_860);
lean_inc(x_864);
lean_inc(x_855);
lean_inc(x_858);
x_962 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_961, x_858, x_855, x_864, x_860, x_856, x_865, x_853, x_863, x_951);
if (lean_obj_tag(x_962) == 0)
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; 
x_963 = lean_ctor_get(x_962, 1);
lean_inc(x_963);
if (lean_is_exclusive(x_962)) {
 lean_ctor_release(x_962, 0);
 lean_ctor_release(x_962, 1);
 x_964 = x_962;
} else {
 lean_dec_ref(x_962);
 x_964 = lean_box(0);
}
x_965 = l_Int_Linear_Poly_mul(x_862, x_888);
lean_dec(x_888);
x_966 = lean_int_neg(x_866);
lean_dec(x_866);
x_967 = l_Int_Linear_Poly_mul(x_889, x_966);
lean_dec(x_966);
x_968 = l_Int_Linear_Poly_combine(x_965, x_967);
lean_inc(x_884);
if (lean_is_scalar(x_964)) {
 x_969 = lean_alloc_ctor(5, 2, 0);
} else {
 x_969 = x_964;
 lean_ctor_set_tag(x_969, 5);
}
lean_ctor_set(x_969, 0, x_854);
lean_ctor_set(x_969, 1, x_884);
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 lean_ctor_release(x_884, 1);
 lean_ctor_release(x_884, 2);
 x_970 = x_884;
} else {
 lean_dec_ref(x_884);
 x_970 = lean_box(0);
}
if (lean_is_scalar(x_970)) {
 x_971 = lean_alloc_ctor(0, 3, 0);
} else {
 x_971 = x_970;
}
lean_ctor_set(x_971, 0, x_895);
lean_ctor_set(x_971, 1, x_968);
lean_ctor_set(x_971, 2, x_969);
x_1 = x_971;
x_2 = x_858;
x_3 = x_855;
x_4 = x_864;
x_5 = x_860;
x_6 = x_856;
x_7 = x_865;
x_8 = x_853;
x_9 = x_863;
x_10 = x_963;
goto _start;
}
else
{
lean_dec(x_895);
lean_dec(x_889);
lean_dec(x_888);
lean_dec(x_884);
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_862);
lean_dec(x_860);
lean_dec(x_858);
lean_dec(x_856);
lean_dec(x_855);
lean_dec(x_854);
lean_dec(x_853);
return x_962;
}
}
}
}
block_1003:
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; uint8_t x_1000; 
x_995 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_986, x_994);
x_996 = lean_ctor_get(x_995, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_996, 5);
lean_inc(x_997);
lean_dec(x_996);
x_998 = lean_ctor_get(x_995, 1);
lean_inc(x_998);
lean_dec(x_995);
x_999 = lean_ctor_get(x_997, 2);
lean_inc(x_999);
x_1000 = lean_nat_dec_lt(x_983, x_999);
lean_dec(x_999);
if (x_1000 == 0)
{
lean_object* x_1001; 
lean_dec(x_997);
x_1001 = l_outOfBounds___redArg(x_979);
x_852 = x_981;
x_853 = x_992;
x_854 = x_982;
x_855 = x_987;
x_856 = x_990;
x_857 = x_983;
x_858 = x_986;
x_859 = x_985;
x_860 = x_989;
x_861 = x_998;
x_862 = x_980;
x_863 = x_993;
x_864 = x_988;
x_865 = x_991;
x_866 = x_984;
x_867 = x_1001;
goto block_973;
}
else
{
lean_object* x_1002; 
x_1002 = l_Lean_PersistentArray_get_x21___redArg(x_979, x_997, x_983);
x_852 = x_981;
x_853 = x_992;
x_854 = x_982;
x_855 = x_987;
x_856 = x_990;
x_857 = x_983;
x_858 = x_986;
x_859 = x_985;
x_860 = x_989;
x_861 = x_998;
x_862 = x_980;
x_863 = x_993;
x_864 = x_988;
x_865 = x_991;
x_866 = x_984;
x_867 = x_1002;
goto block_973;
}
}
block_1070:
{
lean_object* x_1013; lean_object* x_1014; 
x_1013 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_1010);
x_1014 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_1013, x_1004, x_1008, x_1009, x_1010, x_1011, x_1012);
if (lean_obj_tag(x_1014) == 0)
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; uint8_t x_1019; 
x_1015 = lean_ctor_get(x_1014, 0);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_1014, 1);
lean_inc(x_1016);
lean_dec(x_1014);
x_1017 = lean_ctor_get(x_1015, 0);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_1015, 1);
lean_inc(x_1018);
lean_inc(x_1017);
x_1019 = l_Int_Linear_Poly_isUnsatDvd(x_1017, x_1018);
if (x_1019 == 0)
{
uint8_t x_1020; 
x_1020 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_1015);
if (x_1020 == 0)
{
if (lean_obj_tag(x_1018) == 0)
{
lean_object* x_1021; 
lean_dec(x_1018);
lean_dec(x_1017);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1005);
x_1021 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_1015, x_1004, x_1008, x_1009, x_1010, x_1011, x_1016);
lean_dec(x_1011);
lean_dec(x_1010);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_1004);
return x_1021;
}
else
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; uint8_t x_1029; uint8_t x_1030; uint8_t x_1031; 
x_1022 = lean_ctor_get(x_1018, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1018, 1);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_1018, 2);
lean_inc(x_1024);
lean_inc(x_1015);
x_1025 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_1015, x_1004, x_1016);
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1025, 1);
lean_inc(x_1027);
lean_dec(x_1025);
x_1028 = lean_box(0);
x_1029 = lean_unbox(x_1026);
lean_dec(x_1026);
x_1030 = lean_unbox(x_1028);
x_1031 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_1029, x_1030);
if (x_1031 == 0)
{
x_980 = x_1024;
x_981 = x_1017;
x_982 = x_1015;
x_983 = x_1023;
x_984 = x_1022;
x_985 = x_1018;
x_986 = x_1004;
x_987 = x_1005;
x_988 = x_1006;
x_989 = x_1007;
x_990 = x_1008;
x_991 = x_1009;
x_992 = x_1010;
x_993 = x_1011;
x_994 = x_1027;
goto block_1003;
}
else
{
lean_object* x_1032; lean_object* x_1033; 
x_1032 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_1023, x_1004, x_1027);
x_1033 = lean_ctor_get(x_1032, 1);
lean_inc(x_1033);
lean_dec(x_1032);
x_980 = x_1024;
x_981 = x_1017;
x_982 = x_1015;
x_983 = x_1023;
x_984 = x_1022;
x_985 = x_1018;
x_986 = x_1004;
x_987 = x_1005;
x_988 = x_1006;
x_989 = x_1007;
x_990 = x_1008;
x_991 = x_1009;
x_992 = x_1010;
x_993 = x_1011;
x_994 = x_1033;
goto block_1003;
}
}
}
else
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; uint8_t x_1037; 
lean_dec(x_1018);
lean_dec(x_1017);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1005);
x_1034 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_1035 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1034, x_1010, x_1016);
x_1036 = lean_ctor_get(x_1035, 0);
lean_inc(x_1036);
x_1037 = lean_unbox(x_1036);
lean_dec(x_1036);
if (x_1037 == 0)
{
lean_object* x_1038; 
lean_dec(x_1015);
lean_dec(x_1011);
lean_dec(x_1010);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_1004);
x_1038 = lean_ctor_get(x_1035, 1);
lean_inc(x_1038);
lean_dec(x_1035);
x_174 = x_1038;
goto block_177;
}
else
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; 
x_1039 = lean_ctor_get(x_1035, 1);
lean_inc(x_1039);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 lean_ctor_release(x_1035, 1);
 x_1040 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1040 = lean_box(0);
}
x_1041 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1015, x_1004, x_1039);
lean_dec(x_1004);
x_1042 = lean_ctor_get(x_1041, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1041, 1);
lean_inc(x_1043);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1044 = x_1041;
} else {
 lean_dec_ref(x_1041);
 x_1044 = lean_box(0);
}
x_1045 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1044)) {
 x_1046 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1046 = x_1044;
 lean_ctor_set_tag(x_1046, 7);
}
lean_ctor_set(x_1046, 0, x_1045);
lean_ctor_set(x_1046, 1, x_1042);
if (lean_is_scalar(x_1040)) {
 x_1047 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1047 = x_1040;
 lean_ctor_set_tag(x_1047, 7);
}
lean_ctor_set(x_1047, 0, x_1046);
lean_ctor_set(x_1047, 1, x_1045);
x_1048 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1034, x_1047, x_1008, x_1009, x_1010, x_1011, x_1043);
lean_dec(x_1011);
lean_dec(x_1010);
lean_dec(x_1009);
lean_dec(x_1008);
x_1049 = lean_ctor_get(x_1048, 1);
lean_inc(x_1049);
lean_dec(x_1048);
x_174 = x_1049;
goto block_177;
}
}
}
else
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; uint8_t x_1053; 
lean_dec(x_1018);
lean_dec(x_1017);
x_1050 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_1051 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1050, x_1010, x_1016);
x_1052 = lean_ctor_get(x_1051, 0);
lean_inc(x_1052);
x_1053 = lean_unbox(x_1052);
lean_dec(x_1052);
if (x_1053 == 0)
{
lean_object* x_1054; 
x_1054 = lean_ctor_get(x_1051, 1);
lean_inc(x_1054);
lean_dec(x_1051);
x_155 = x_1015;
x_156 = x_1004;
x_157 = x_1005;
x_158 = x_1006;
x_159 = x_1007;
x_160 = x_1008;
x_161 = x_1009;
x_162 = x_1010;
x_163 = x_1011;
x_164 = x_1054;
goto block_173;
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
lean_inc(x_1015);
x_1057 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1015, x_1004, x_1055);
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
x_1064 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1050, x_1063, x_1008, x_1009, x_1010, x_1011, x_1059);
x_1065 = lean_ctor_get(x_1064, 1);
lean_inc(x_1065);
lean_dec(x_1064);
x_155 = x_1015;
x_156 = x_1004;
x_157 = x_1005;
x_158 = x_1006;
x_159 = x_1007;
x_160 = x_1008;
x_161 = x_1009;
x_162 = x_1010;
x_163 = x_1011;
x_164 = x_1065;
goto block_173;
}
}
}
else
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
lean_dec(x_1011);
lean_dec(x_1010);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1005);
lean_dec(x_1004);
x_1066 = lean_ctor_get(x_1014, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1014, 1);
lean_inc(x_1067);
if (lean_is_exclusive(x_1014)) {
 lean_ctor_release(x_1014, 0);
 lean_ctor_release(x_1014, 1);
 x_1068 = x_1014;
} else {
 lean_dec_ref(x_1014);
 x_1068 = lean_box(0);
}
if (lean_is_scalar(x_1068)) {
 x_1069 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1069 = x_1068;
}
lean_ctor_set(x_1069, 0, x_1066);
lean_ctor_set(x_1069, 1, x_1067);
return x_1069;
}
}
}
else
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
lean_dec(x_843);
lean_dec(x_841);
lean_dec(x_839);
lean_dec(x_838);
lean_dec(x_837);
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_834);
lean_dec(x_833);
lean_dec(x_832);
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1081 = lean_ctor_get(x_845, 1);
lean_inc(x_1081);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 lean_ctor_release(x_845, 1);
 x_1082 = x_845;
} else {
 lean_dec_ref(x_845);
 x_1082 = lean_box(0);
}
x_1083 = lean_box(0);
if (lean_is_scalar(x_1082)) {
 x_1084 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1084 = x_1082;
}
lean_ctor_set(x_1084, 0, x_1083);
lean_ctor_set(x_1084, 1, x_1081);
return x_1084;
}
}
else
{
lean_object* x_1085; 
lean_dec(x_843);
lean_dec(x_841);
lean_dec(x_839);
lean_dec(x_838);
lean_dec(x_837);
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_833);
lean_dec(x_832);
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1085 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_834, x_10);
return x_1085;
}
}
block_154:
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
x_32 = lean_ctor_get(x_25, 5);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_11);
x_34 = l_Lean_PersistentArray_set___redArg(x_32, x_12, x_33);
lean_dec(x_12);
lean_ctor_set(x_25, 5, x_34);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
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
x_56 = lean_ctor_get_uint8(x_25, sizeof(void*)*19);
x_57 = lean_ctor_get(x_25, 14);
x_58 = lean_ctor_get(x_25, 15);
x_59 = lean_ctor_get(x_25, 16);
x_60 = lean_ctor_get(x_25, 17);
x_61 = lean_ctor_get(x_25, 18);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
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
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_11);
x_63 = l_Lean_PersistentArray_set___redArg(x_47, x_12, x_62);
lean_dec(x_12);
x_64 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_64, 0, x_42);
lean_ctor_set(x_64, 1, x_43);
lean_ctor_set(x_64, 2, x_44);
lean_ctor_set(x_64, 3, x_45);
lean_ctor_set(x_64, 4, x_46);
lean_ctor_set(x_64, 5, x_63);
lean_ctor_set(x_64, 6, x_48);
lean_ctor_set(x_64, 7, x_49);
lean_ctor_set(x_64, 8, x_50);
lean_ctor_set(x_64, 9, x_51);
lean_ctor_set(x_64, 10, x_52);
lean_ctor_set(x_64, 11, x_53);
lean_ctor_set(x_64, 12, x_54);
lean_ctor_set(x_64, 13, x_55);
lean_ctor_set(x_64, 14, x_57);
lean_ctor_set(x_64, 15, x_58);
lean_ctor_set(x_64, 16, x_59);
lean_ctor_set(x_64, 17, x_60);
lean_ctor_set(x_64, 18, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*19, x_56);
lean_ctor_set(x_24, 1, x_64);
x_65 = lean_st_ref_set(x_14, x_23, x_26);
lean_dec(x_14);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_70 = lean_ctor_get(x_24, 0);
x_71 = lean_ctor_get(x_24, 2);
x_72 = lean_ctor_get(x_24, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_24);
x_73 = lean_ctor_get(x_25, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_25, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_25, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_25, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_25, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_25, 5);
lean_inc(x_78);
x_79 = lean_ctor_get(x_25, 6);
lean_inc(x_79);
x_80 = lean_ctor_get(x_25, 7);
lean_inc(x_80);
x_81 = lean_ctor_get(x_25, 8);
lean_inc(x_81);
x_82 = lean_ctor_get(x_25, 9);
lean_inc(x_82);
x_83 = lean_ctor_get(x_25, 10);
lean_inc(x_83);
x_84 = lean_ctor_get(x_25, 11);
lean_inc(x_84);
x_85 = lean_ctor_get(x_25, 12);
lean_inc(x_85);
x_86 = lean_ctor_get(x_25, 13);
lean_inc(x_86);
x_87 = lean_ctor_get_uint8(x_25, sizeof(void*)*19);
x_88 = lean_ctor_get(x_25, 14);
lean_inc(x_88);
x_89 = lean_ctor_get(x_25, 15);
lean_inc(x_89);
x_90 = lean_ctor_get(x_25, 16);
lean_inc(x_90);
x_91 = lean_ctor_get(x_25, 17);
lean_inc(x_91);
x_92 = lean_ctor_get(x_25, 18);
lean_inc(x_92);
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
 x_93 = x_25;
} else {
 lean_dec_ref(x_25);
 x_93 = lean_box(0);
}
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_11);
x_95 = l_Lean_PersistentArray_set___redArg(x_78, x_12, x_94);
lean_dec(x_12);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(0, 19, 1);
} else {
 x_96 = x_93;
}
lean_ctor_set(x_96, 0, x_73);
lean_ctor_set(x_96, 1, x_74);
lean_ctor_set(x_96, 2, x_75);
lean_ctor_set(x_96, 3, x_76);
lean_ctor_set(x_96, 4, x_77);
lean_ctor_set(x_96, 5, x_95);
lean_ctor_set(x_96, 6, x_79);
lean_ctor_set(x_96, 7, x_80);
lean_ctor_set(x_96, 8, x_81);
lean_ctor_set(x_96, 9, x_82);
lean_ctor_set(x_96, 10, x_83);
lean_ctor_set(x_96, 11, x_84);
lean_ctor_set(x_96, 12, x_85);
lean_ctor_set(x_96, 13, x_86);
lean_ctor_set(x_96, 14, x_88);
lean_ctor_set(x_96, 15, x_89);
lean_ctor_set(x_96, 16, x_90);
lean_ctor_set(x_96, 17, x_91);
lean_ctor_set(x_96, 18, x_92);
lean_ctor_set_uint8(x_96, sizeof(void*)*19, x_87);
x_97 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_97, 0, x_70);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_71);
lean_ctor_set(x_97, 3, x_72);
lean_ctor_set(x_23, 14, x_97);
x_98 = lean_st_ref_set(x_14, x_23, x_26);
lean_dec(x_14);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_box(0);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_103 = lean_ctor_get(x_23, 0);
x_104 = lean_ctor_get(x_23, 1);
x_105 = lean_ctor_get(x_23, 2);
x_106 = lean_ctor_get(x_23, 3);
x_107 = lean_ctor_get(x_23, 4);
x_108 = lean_ctor_get(x_23, 5);
x_109 = lean_ctor_get(x_23, 6);
x_110 = lean_ctor_get(x_23, 7);
x_111 = lean_ctor_get_uint8(x_23, sizeof(void*)*16);
x_112 = lean_ctor_get(x_23, 8);
x_113 = lean_ctor_get(x_23, 9);
x_114 = lean_ctor_get(x_23, 10);
x_115 = lean_ctor_get(x_23, 11);
x_116 = lean_ctor_get(x_23, 12);
x_117 = lean_ctor_get(x_23, 13);
x_118 = lean_ctor_get(x_23, 15);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_23);
x_119 = lean_ctor_get(x_24, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_24, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_24, 3);
lean_inc(x_121);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 x_122 = x_24;
} else {
 lean_dec_ref(x_24);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_25, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_25, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_25, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_25, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_25, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_25, 5);
lean_inc(x_128);
x_129 = lean_ctor_get(x_25, 6);
lean_inc(x_129);
x_130 = lean_ctor_get(x_25, 7);
lean_inc(x_130);
x_131 = lean_ctor_get(x_25, 8);
lean_inc(x_131);
x_132 = lean_ctor_get(x_25, 9);
lean_inc(x_132);
x_133 = lean_ctor_get(x_25, 10);
lean_inc(x_133);
x_134 = lean_ctor_get(x_25, 11);
lean_inc(x_134);
x_135 = lean_ctor_get(x_25, 12);
lean_inc(x_135);
x_136 = lean_ctor_get(x_25, 13);
lean_inc(x_136);
x_137 = lean_ctor_get_uint8(x_25, sizeof(void*)*19);
x_138 = lean_ctor_get(x_25, 14);
lean_inc(x_138);
x_139 = lean_ctor_get(x_25, 15);
lean_inc(x_139);
x_140 = lean_ctor_get(x_25, 16);
lean_inc(x_140);
x_141 = lean_ctor_get(x_25, 17);
lean_inc(x_141);
x_142 = lean_ctor_get(x_25, 18);
lean_inc(x_142);
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
 x_143 = x_25;
} else {
 lean_dec_ref(x_25);
 x_143 = lean_box(0);
}
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_11);
x_145 = l_Lean_PersistentArray_set___redArg(x_128, x_12, x_144);
lean_dec(x_12);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 19, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_123);
lean_ctor_set(x_146, 1, x_124);
lean_ctor_set(x_146, 2, x_125);
lean_ctor_set(x_146, 3, x_126);
lean_ctor_set(x_146, 4, x_127);
lean_ctor_set(x_146, 5, x_145);
lean_ctor_set(x_146, 6, x_129);
lean_ctor_set(x_146, 7, x_130);
lean_ctor_set(x_146, 8, x_131);
lean_ctor_set(x_146, 9, x_132);
lean_ctor_set(x_146, 10, x_133);
lean_ctor_set(x_146, 11, x_134);
lean_ctor_set(x_146, 12, x_135);
lean_ctor_set(x_146, 13, x_136);
lean_ctor_set(x_146, 14, x_138);
lean_ctor_set(x_146, 15, x_139);
lean_ctor_set(x_146, 16, x_140);
lean_ctor_set(x_146, 17, x_141);
lean_ctor_set(x_146, 18, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*19, x_137);
if (lean_is_scalar(x_122)) {
 x_147 = lean_alloc_ctor(0, 4, 0);
} else {
 x_147 = x_122;
}
lean_ctor_set(x_147, 0, x_119);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_120);
lean_ctor_set(x_147, 3, x_121);
x_148 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_148, 0, x_103);
lean_ctor_set(x_148, 1, x_104);
lean_ctor_set(x_148, 2, x_105);
lean_ctor_set(x_148, 3, x_106);
lean_ctor_set(x_148, 4, x_107);
lean_ctor_set(x_148, 5, x_108);
lean_ctor_set(x_148, 6, x_109);
lean_ctor_set(x_148, 7, x_110);
lean_ctor_set(x_148, 8, x_112);
lean_ctor_set(x_148, 9, x_113);
lean_ctor_set(x_148, 10, x_114);
lean_ctor_set(x_148, 11, x_115);
lean_ctor_set(x_148, 12, x_116);
lean_ctor_set(x_148, 13, x_117);
lean_ctor_set(x_148, 14, x_147);
lean_ctor_set(x_148, 15, x_118);
lean_ctor_set_uint8(x_148, sizeof(void*)*16, x_111);
x_149 = lean_st_ref_set(x_14, x_148, x_26);
lean_dec(x_14);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
x_152 = lean_box(0);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_150);
return x_153;
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
block_173:
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_155);
x_166 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_165, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_166, 0);
lean_dec(x_168);
x_169 = lean_box(0);
lean_ctor_set(x_166, 0, x_169);
return x_166;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_166, 1);
lean_inc(x_170);
lean_dec(x_166);
x_171 = lean_box(0);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
return x_166;
}
}
block_177:
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_box(0);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
return x_176;
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

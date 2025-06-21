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
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getForeignVars___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2669_(lean_object*);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_168; uint8_t x_172; 
x_172 = !lean_is_exclusive(x_8);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_173 = lean_ctor_get(x_8, 0);
x_174 = lean_ctor_get(x_8, 1);
x_175 = lean_ctor_get(x_8, 2);
x_176 = lean_ctor_get(x_8, 3);
x_177 = lean_ctor_get(x_8, 4);
x_178 = lean_ctor_get(x_8, 5);
x_179 = lean_ctor_get(x_8, 6);
x_180 = lean_ctor_get(x_8, 7);
x_181 = lean_ctor_get(x_8, 8);
x_182 = lean_ctor_get(x_8, 9);
x_183 = lean_ctor_get(x_8, 10);
x_184 = lean_ctor_get(x_8, 11);
x_185 = lean_ctor_get(x_8, 12);
x_186 = lean_nat_dec_eq(x_176, x_177);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
lean_dec(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_563; lean_object* x_564; uint8_t x_565; 
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_191 = lean_unsigned_to_nat(1u);
x_192 = lean_nat_add(x_176, x_191);
lean_dec(x_176);
lean_ctor_set(x_8, 3, x_192);
x_563 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_564 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_563, x_8, x_190);
x_565 = !lean_is_exclusive(x_564);
if (x_565 == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; uint8_t x_690; 
x_566 = lean_ctor_get(x_564, 0);
x_567 = lean_ctor_get(x_564, 1);
x_568 = lean_box(0);
x_690 = lean_unbox(x_566);
lean_dec(x_566);
if (x_690 == 0)
{
lean_free_object(x_564);
x_593 = x_2;
x_594 = x_3;
x_595 = x_4;
x_596 = x_5;
x_597 = x_6;
x_598 = x_7;
x_599 = x_8;
x_600 = x_9;
x_601 = x_567;
goto block_689;
}
else
{
lean_object* x_691; uint8_t x_692; 
lean_inc(x_1);
x_691 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_567);
x_692 = !lean_is_exclusive(x_691);
if (x_692 == 0)
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_693 = lean_ctor_get(x_691, 0);
x_694 = lean_ctor_get(x_691, 1);
x_695 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_691, 7);
lean_ctor_set(x_691, 1, x_693);
lean_ctor_set(x_691, 0, x_695);
lean_ctor_set_tag(x_564, 7);
lean_ctor_set(x_564, 1, x_695);
lean_ctor_set(x_564, 0, x_691);
x_696 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_563, x_564, x_6, x_7, x_8, x_9, x_694);
x_697 = lean_ctor_get(x_696, 1);
lean_inc(x_697);
lean_dec(x_696);
x_593 = x_2;
x_594 = x_3;
x_595 = x_4;
x_596 = x_5;
x_597 = x_6;
x_598 = x_7;
x_599 = x_8;
x_600 = x_9;
x_601 = x_697;
goto block_689;
}
else
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_698 = lean_ctor_get(x_691, 0);
x_699 = lean_ctor_get(x_691, 1);
lean_inc(x_699);
lean_inc(x_698);
lean_dec(x_691);
x_700 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_701 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_701, 0, x_700);
lean_ctor_set(x_701, 1, x_698);
lean_ctor_set_tag(x_564, 7);
lean_ctor_set(x_564, 1, x_700);
lean_ctor_set(x_564, 0, x_701);
x_702 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_563, x_564, x_6, x_7, x_8, x_9, x_699);
x_703 = lean_ctor_get(x_702, 1);
lean_inc(x_703);
lean_dec(x_702);
x_593 = x_2;
x_594 = x_3;
x_595 = x_4;
x_596 = x_5;
x_597 = x_6;
x_598 = x_7;
x_599 = x_8;
x_600 = x_9;
x_601 = x_703;
goto block_689;
}
}
block_592:
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; uint8_t x_589; 
x_584 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_575, x_583);
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_585, 5);
lean_inc(x_586);
lean_dec(x_585);
x_587 = lean_ctor_get(x_584, 1);
lean_inc(x_587);
lean_dec(x_584);
x_588 = lean_ctor_get(x_586, 2);
lean_inc(x_588);
x_589 = lean_nat_dec_lt(x_571, x_588);
lean_dec(x_588);
if (x_589 == 0)
{
lean_object* x_590; 
lean_dec(x_586);
x_590 = l_outOfBounds___redArg(x_568);
x_193 = x_587;
x_194 = x_576;
x_195 = x_571;
x_196 = x_572;
x_197 = x_574;
x_198 = x_575;
x_199 = x_577;
x_200 = x_581;
x_201 = x_569;
x_202 = x_582;
x_203 = x_570;
x_204 = x_580;
x_205 = x_573;
x_206 = x_578;
x_207 = x_579;
x_208 = x_590;
goto block_562;
}
else
{
lean_object* x_591; 
x_591 = l_Lean_PersistentArray_get_x21___redArg(x_568, x_586, x_571);
x_193 = x_587;
x_194 = x_576;
x_195 = x_571;
x_196 = x_572;
x_197 = x_574;
x_198 = x_575;
x_199 = x_577;
x_200 = x_581;
x_201 = x_569;
x_202 = x_582;
x_203 = x_570;
x_204 = x_580;
x_205 = x_573;
x_206 = x_578;
x_207 = x_579;
x_208 = x_591;
goto block_562;
}
}
block_689:
{
lean_object* x_602; lean_object* x_603; 
x_602 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_599);
x_603 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_602, x_593, x_597, x_598, x_599, x_600, x_601);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; uint8_t x_608; 
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
lean_dec(x_603);
x_606 = lean_ctor_get(x_604, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_604, 1);
lean_inc(x_607);
lean_inc(x_606);
x_608 = l_Int_Linear_Poly_isUnsatDvd(x_606, x_607);
if (x_608 == 0)
{
uint8_t x_609; 
x_609 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_604);
if (x_609 == 0)
{
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_610; 
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
x_610 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_604, x_593, x_597, x_598, x_599, x_600, x_605);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_593);
return x_610;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; uint8_t x_618; uint8_t x_619; uint8_t x_620; 
x_611 = lean_ctor_get(x_607, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_607, 1);
lean_inc(x_612);
x_613 = lean_ctor_get(x_607, 2);
lean_inc(x_613);
lean_inc(x_604);
x_614 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_604, x_593, x_605);
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_614, 1);
lean_inc(x_616);
lean_dec(x_614);
x_617 = lean_box(0);
x_618 = lean_unbox(x_615);
lean_dec(x_615);
x_619 = lean_unbox(x_617);
x_620 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_618, x_619);
if (x_620 == 0)
{
x_569 = x_607;
x_570 = x_613;
x_571 = x_612;
x_572 = x_611;
x_573 = x_606;
x_574 = x_604;
x_575 = x_593;
x_576 = x_594;
x_577 = x_595;
x_578 = x_596;
x_579 = x_597;
x_580 = x_598;
x_581 = x_599;
x_582 = x_600;
x_583 = x_616;
goto block_592;
}
else
{
lean_object* x_621; lean_object* x_622; 
x_621 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_612, x_593, x_616);
x_622 = lean_ctor_get(x_621, 1);
lean_inc(x_622);
lean_dec(x_621);
x_569 = x_607;
x_570 = x_613;
x_571 = x_612;
x_572 = x_611;
x_573 = x_606;
x_574 = x_604;
x_575 = x_593;
x_576 = x_594;
x_577 = x_595;
x_578 = x_596;
x_579 = x_597;
x_580 = x_598;
x_581 = x_599;
x_582 = x_600;
x_583 = x_622;
goto block_592;
}
}
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; uint8_t x_626; 
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
x_623 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_624 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_623, x_599, x_605);
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_unbox(x_625);
lean_dec(x_625);
if (x_626 == 0)
{
lean_object* x_627; 
lean_dec(x_604);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_593);
x_627 = lean_ctor_get(x_624, 1);
lean_inc(x_627);
lean_dec(x_624);
x_168 = x_627;
goto block_171;
}
else
{
uint8_t x_628; 
x_628 = !lean_is_exclusive(x_624);
if (x_628 == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; uint8_t x_632; 
x_629 = lean_ctor_get(x_624, 1);
x_630 = lean_ctor_get(x_624, 0);
lean_dec(x_630);
x_631 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_604, x_593, x_629);
lean_dec(x_593);
x_632 = !lean_is_exclusive(x_631);
if (x_632 == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_633 = lean_ctor_get(x_631, 0);
x_634 = lean_ctor_get(x_631, 1);
x_635 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_631, 7);
lean_ctor_set(x_631, 1, x_633);
lean_ctor_set(x_631, 0, x_635);
lean_ctor_set_tag(x_624, 7);
lean_ctor_set(x_624, 1, x_635);
lean_ctor_set(x_624, 0, x_631);
x_636 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_623, x_624, x_597, x_598, x_599, x_600, x_634);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
x_637 = lean_ctor_get(x_636, 1);
lean_inc(x_637);
lean_dec(x_636);
x_168 = x_637;
goto block_171;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_638 = lean_ctor_get(x_631, 0);
x_639 = lean_ctor_get(x_631, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_631);
x_640 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_641 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_638);
lean_ctor_set_tag(x_624, 7);
lean_ctor_set(x_624, 1, x_640);
lean_ctor_set(x_624, 0, x_641);
x_642 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_623, x_624, x_597, x_598, x_599, x_600, x_639);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
x_643 = lean_ctor_get(x_642, 1);
lean_inc(x_643);
lean_dec(x_642);
x_168 = x_643;
goto block_171;
}
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_644 = lean_ctor_get(x_624, 1);
lean_inc(x_644);
lean_dec(x_624);
x_645 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_604, x_593, x_644);
lean_dec(x_593);
x_646 = lean_ctor_get(x_645, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_645, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_645)) {
 lean_ctor_release(x_645, 0);
 lean_ctor_release(x_645, 1);
 x_648 = x_645;
} else {
 lean_dec_ref(x_645);
 x_648 = lean_box(0);
}
x_649 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_648)) {
 x_650 = lean_alloc_ctor(7, 2, 0);
} else {
 x_650 = x_648;
 lean_ctor_set_tag(x_650, 7);
}
lean_ctor_set(x_650, 0, x_649);
lean_ctor_set(x_650, 1, x_646);
x_651 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_649);
x_652 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_623, x_651, x_597, x_598, x_599, x_600, x_647);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
x_653 = lean_ctor_get(x_652, 1);
lean_inc(x_653);
lean_dec(x_652);
x_168 = x_653;
goto block_171;
}
}
}
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_657; 
lean_dec(x_607);
lean_dec(x_606);
x_654 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_655 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_654, x_599, x_605);
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_unbox(x_656);
lean_dec(x_656);
if (x_657 == 0)
{
lean_object* x_658; 
x_658 = lean_ctor_get(x_655, 1);
lean_inc(x_658);
lean_dec(x_655);
x_149 = x_604;
x_150 = x_593;
x_151 = x_594;
x_152 = x_595;
x_153 = x_596;
x_154 = x_597;
x_155 = x_598;
x_156 = x_599;
x_157 = x_600;
x_158 = x_658;
goto block_167;
}
else
{
uint8_t x_659; 
x_659 = !lean_is_exclusive(x_655);
if (x_659 == 0)
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; uint8_t x_663; 
x_660 = lean_ctor_get(x_655, 1);
x_661 = lean_ctor_get(x_655, 0);
lean_dec(x_661);
lean_inc(x_604);
x_662 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_604, x_593, x_660);
x_663 = !lean_is_exclusive(x_662);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_664 = lean_ctor_get(x_662, 0);
x_665 = lean_ctor_get(x_662, 1);
x_666 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_662, 7);
lean_ctor_set(x_662, 1, x_664);
lean_ctor_set(x_662, 0, x_666);
lean_ctor_set_tag(x_655, 7);
lean_ctor_set(x_655, 1, x_666);
lean_ctor_set(x_655, 0, x_662);
x_667 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_654, x_655, x_597, x_598, x_599, x_600, x_665);
x_668 = lean_ctor_get(x_667, 1);
lean_inc(x_668);
lean_dec(x_667);
x_149 = x_604;
x_150 = x_593;
x_151 = x_594;
x_152 = x_595;
x_153 = x_596;
x_154 = x_597;
x_155 = x_598;
x_156 = x_599;
x_157 = x_600;
x_158 = x_668;
goto block_167;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_669 = lean_ctor_get(x_662, 0);
x_670 = lean_ctor_get(x_662, 1);
lean_inc(x_670);
lean_inc(x_669);
lean_dec(x_662);
x_671 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_672 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_669);
lean_ctor_set_tag(x_655, 7);
lean_ctor_set(x_655, 1, x_671);
lean_ctor_set(x_655, 0, x_672);
x_673 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_654, x_655, x_597, x_598, x_599, x_600, x_670);
x_674 = lean_ctor_get(x_673, 1);
lean_inc(x_674);
lean_dec(x_673);
x_149 = x_604;
x_150 = x_593;
x_151 = x_594;
x_152 = x_595;
x_153 = x_596;
x_154 = x_597;
x_155 = x_598;
x_156 = x_599;
x_157 = x_600;
x_158 = x_674;
goto block_167;
}
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_675 = lean_ctor_get(x_655, 1);
lean_inc(x_675);
lean_dec(x_655);
lean_inc(x_604);
x_676 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_604, x_593, x_675);
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_676, 1);
lean_inc(x_678);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 lean_ctor_release(x_676, 1);
 x_679 = x_676;
} else {
 lean_dec_ref(x_676);
 x_679 = lean_box(0);
}
x_680 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_679)) {
 x_681 = lean_alloc_ctor(7, 2, 0);
} else {
 x_681 = x_679;
 lean_ctor_set_tag(x_681, 7);
}
lean_ctor_set(x_681, 0, x_680);
lean_ctor_set(x_681, 1, x_677);
x_682 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_682, 0, x_681);
lean_ctor_set(x_682, 1, x_680);
x_683 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_654, x_682, x_597, x_598, x_599, x_600, x_678);
x_684 = lean_ctor_get(x_683, 1);
lean_inc(x_684);
lean_dec(x_683);
x_149 = x_604;
x_150 = x_593;
x_151 = x_594;
x_152 = x_595;
x_153 = x_596;
x_154 = x_597;
x_155 = x_598;
x_156 = x_599;
x_157 = x_600;
x_158 = x_684;
goto block_167;
}
}
}
}
else
{
uint8_t x_685; 
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_593);
x_685 = !lean_is_exclusive(x_603);
if (x_685 == 0)
{
return x_603;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_686 = lean_ctor_get(x_603, 0);
x_687 = lean_ctor_get(x_603, 1);
lean_inc(x_687);
lean_inc(x_686);
lean_dec(x_603);
x_688 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_688, 0, x_686);
lean_ctor_set(x_688, 1, x_687);
return x_688;
}
}
}
}
else
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; uint8_t x_798; 
x_704 = lean_ctor_get(x_564, 0);
x_705 = lean_ctor_get(x_564, 1);
lean_inc(x_705);
lean_inc(x_704);
lean_dec(x_564);
x_706 = lean_box(0);
x_798 = lean_unbox(x_704);
lean_dec(x_704);
if (x_798 == 0)
{
x_731 = x_2;
x_732 = x_3;
x_733 = x_4;
x_734 = x_5;
x_735 = x_6;
x_736 = x_7;
x_737 = x_8;
x_738 = x_9;
x_739 = x_705;
goto block_797;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_inc(x_1);
x_799 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_705);
x_800 = lean_ctor_get(x_799, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_799, 1);
lean_inc(x_801);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_802 = x_799;
} else {
 lean_dec_ref(x_799);
 x_802 = lean_box(0);
}
x_803 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_802)) {
 x_804 = lean_alloc_ctor(7, 2, 0);
} else {
 x_804 = x_802;
 lean_ctor_set_tag(x_804, 7);
}
lean_ctor_set(x_804, 0, x_803);
lean_ctor_set(x_804, 1, x_800);
x_805 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_805, 0, x_804);
lean_ctor_set(x_805, 1, x_803);
x_806 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_563, x_805, x_6, x_7, x_8, x_9, x_801);
x_807 = lean_ctor_get(x_806, 1);
lean_inc(x_807);
lean_dec(x_806);
x_731 = x_2;
x_732 = x_3;
x_733 = x_4;
x_734 = x_5;
x_735 = x_6;
x_736 = x_7;
x_737 = x_8;
x_738 = x_9;
x_739 = x_807;
goto block_797;
}
block_730:
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; uint8_t x_727; 
x_722 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_713, x_721);
x_723 = lean_ctor_get(x_722, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_723, 5);
lean_inc(x_724);
lean_dec(x_723);
x_725 = lean_ctor_get(x_722, 1);
lean_inc(x_725);
lean_dec(x_722);
x_726 = lean_ctor_get(x_724, 2);
lean_inc(x_726);
x_727 = lean_nat_dec_lt(x_709, x_726);
lean_dec(x_726);
if (x_727 == 0)
{
lean_object* x_728; 
lean_dec(x_724);
x_728 = l_outOfBounds___redArg(x_706);
x_193 = x_725;
x_194 = x_714;
x_195 = x_709;
x_196 = x_710;
x_197 = x_712;
x_198 = x_713;
x_199 = x_715;
x_200 = x_719;
x_201 = x_707;
x_202 = x_720;
x_203 = x_708;
x_204 = x_718;
x_205 = x_711;
x_206 = x_716;
x_207 = x_717;
x_208 = x_728;
goto block_562;
}
else
{
lean_object* x_729; 
x_729 = l_Lean_PersistentArray_get_x21___redArg(x_706, x_724, x_709);
x_193 = x_725;
x_194 = x_714;
x_195 = x_709;
x_196 = x_710;
x_197 = x_712;
x_198 = x_713;
x_199 = x_715;
x_200 = x_719;
x_201 = x_707;
x_202 = x_720;
x_203 = x_708;
x_204 = x_718;
x_205 = x_711;
x_206 = x_716;
x_207 = x_717;
x_208 = x_729;
goto block_562;
}
}
block_797:
{
lean_object* x_740; lean_object* x_741; 
x_740 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_737);
x_741 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_740, x_731, x_735, x_736, x_737, x_738, x_739);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; uint8_t x_746; 
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_741, 1);
lean_inc(x_743);
lean_dec(x_741);
x_744 = lean_ctor_get(x_742, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_742, 1);
lean_inc(x_745);
lean_inc(x_744);
x_746 = l_Int_Linear_Poly_isUnsatDvd(x_744, x_745);
if (x_746 == 0)
{
uint8_t x_747; 
x_747 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_742);
if (x_747 == 0)
{
if (lean_obj_tag(x_745) == 0)
{
lean_object* x_748; 
lean_dec(x_745);
lean_dec(x_744);
lean_dec(x_734);
lean_dec(x_733);
lean_dec(x_732);
x_748 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_742, x_731, x_735, x_736, x_737, x_738, x_743);
lean_dec(x_738);
lean_dec(x_737);
lean_dec(x_736);
lean_dec(x_735);
lean_dec(x_731);
return x_748;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; uint8_t x_756; uint8_t x_757; uint8_t x_758; 
x_749 = lean_ctor_get(x_745, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_745, 1);
lean_inc(x_750);
x_751 = lean_ctor_get(x_745, 2);
lean_inc(x_751);
lean_inc(x_742);
x_752 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_742, x_731, x_743);
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_752, 1);
lean_inc(x_754);
lean_dec(x_752);
x_755 = lean_box(0);
x_756 = lean_unbox(x_753);
lean_dec(x_753);
x_757 = lean_unbox(x_755);
x_758 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_756, x_757);
if (x_758 == 0)
{
x_707 = x_745;
x_708 = x_751;
x_709 = x_750;
x_710 = x_749;
x_711 = x_744;
x_712 = x_742;
x_713 = x_731;
x_714 = x_732;
x_715 = x_733;
x_716 = x_734;
x_717 = x_735;
x_718 = x_736;
x_719 = x_737;
x_720 = x_738;
x_721 = x_754;
goto block_730;
}
else
{
lean_object* x_759; lean_object* x_760; 
x_759 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_750, x_731, x_754);
x_760 = lean_ctor_get(x_759, 1);
lean_inc(x_760);
lean_dec(x_759);
x_707 = x_745;
x_708 = x_751;
x_709 = x_750;
x_710 = x_749;
x_711 = x_744;
x_712 = x_742;
x_713 = x_731;
x_714 = x_732;
x_715 = x_733;
x_716 = x_734;
x_717 = x_735;
x_718 = x_736;
x_719 = x_737;
x_720 = x_738;
x_721 = x_760;
goto block_730;
}
}
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; uint8_t x_764; 
lean_dec(x_745);
lean_dec(x_744);
lean_dec(x_734);
lean_dec(x_733);
lean_dec(x_732);
x_761 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_762 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_761, x_737, x_743);
x_763 = lean_ctor_get(x_762, 0);
lean_inc(x_763);
x_764 = lean_unbox(x_763);
lean_dec(x_763);
if (x_764 == 0)
{
lean_object* x_765; 
lean_dec(x_742);
lean_dec(x_738);
lean_dec(x_737);
lean_dec(x_736);
lean_dec(x_735);
lean_dec(x_731);
x_765 = lean_ctor_get(x_762, 1);
lean_inc(x_765);
lean_dec(x_762);
x_168 = x_765;
goto block_171;
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_766 = lean_ctor_get(x_762, 1);
lean_inc(x_766);
if (lean_is_exclusive(x_762)) {
 lean_ctor_release(x_762, 0);
 lean_ctor_release(x_762, 1);
 x_767 = x_762;
} else {
 lean_dec_ref(x_762);
 x_767 = lean_box(0);
}
x_768 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_742, x_731, x_766);
lean_dec(x_731);
x_769 = lean_ctor_get(x_768, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_768, 1);
lean_inc(x_770);
if (lean_is_exclusive(x_768)) {
 lean_ctor_release(x_768, 0);
 lean_ctor_release(x_768, 1);
 x_771 = x_768;
} else {
 lean_dec_ref(x_768);
 x_771 = lean_box(0);
}
x_772 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_771)) {
 x_773 = lean_alloc_ctor(7, 2, 0);
} else {
 x_773 = x_771;
 lean_ctor_set_tag(x_773, 7);
}
lean_ctor_set(x_773, 0, x_772);
lean_ctor_set(x_773, 1, x_769);
if (lean_is_scalar(x_767)) {
 x_774 = lean_alloc_ctor(7, 2, 0);
} else {
 x_774 = x_767;
 lean_ctor_set_tag(x_774, 7);
}
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_772);
x_775 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_761, x_774, x_735, x_736, x_737, x_738, x_770);
lean_dec(x_738);
lean_dec(x_737);
lean_dec(x_736);
lean_dec(x_735);
x_776 = lean_ctor_get(x_775, 1);
lean_inc(x_776);
lean_dec(x_775);
x_168 = x_776;
goto block_171;
}
}
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; uint8_t x_780; 
lean_dec(x_745);
lean_dec(x_744);
x_777 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_778 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_777, x_737, x_743);
x_779 = lean_ctor_get(x_778, 0);
lean_inc(x_779);
x_780 = lean_unbox(x_779);
lean_dec(x_779);
if (x_780 == 0)
{
lean_object* x_781; 
x_781 = lean_ctor_get(x_778, 1);
lean_inc(x_781);
lean_dec(x_778);
x_149 = x_742;
x_150 = x_731;
x_151 = x_732;
x_152 = x_733;
x_153 = x_734;
x_154 = x_735;
x_155 = x_736;
x_156 = x_737;
x_157 = x_738;
x_158 = x_781;
goto block_167;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_782 = lean_ctor_get(x_778, 1);
lean_inc(x_782);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_783 = x_778;
} else {
 lean_dec_ref(x_778);
 x_783 = lean_box(0);
}
lean_inc(x_742);
x_784 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_742, x_731, x_782);
x_785 = lean_ctor_get(x_784, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_784, 1);
lean_inc(x_786);
if (lean_is_exclusive(x_784)) {
 lean_ctor_release(x_784, 0);
 lean_ctor_release(x_784, 1);
 x_787 = x_784;
} else {
 lean_dec_ref(x_784);
 x_787 = lean_box(0);
}
x_788 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_787)) {
 x_789 = lean_alloc_ctor(7, 2, 0);
} else {
 x_789 = x_787;
 lean_ctor_set_tag(x_789, 7);
}
lean_ctor_set(x_789, 0, x_788);
lean_ctor_set(x_789, 1, x_785);
if (lean_is_scalar(x_783)) {
 x_790 = lean_alloc_ctor(7, 2, 0);
} else {
 x_790 = x_783;
 lean_ctor_set_tag(x_790, 7);
}
lean_ctor_set(x_790, 0, x_789);
lean_ctor_set(x_790, 1, x_788);
x_791 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_777, x_790, x_735, x_736, x_737, x_738, x_786);
x_792 = lean_ctor_get(x_791, 1);
lean_inc(x_792);
lean_dec(x_791);
x_149 = x_742;
x_150 = x_731;
x_151 = x_732;
x_152 = x_733;
x_153 = x_734;
x_154 = x_735;
x_155 = x_736;
x_156 = x_737;
x_157 = x_738;
x_158 = x_792;
goto block_167;
}
}
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
lean_dec(x_738);
lean_dec(x_737);
lean_dec(x_736);
lean_dec(x_735);
lean_dec(x_734);
lean_dec(x_733);
lean_dec(x_732);
lean_dec(x_731);
x_793 = lean_ctor_get(x_741, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_741, 1);
lean_inc(x_794);
if (lean_is_exclusive(x_741)) {
 lean_ctor_release(x_741, 0);
 lean_ctor_release(x_741, 1);
 x_795 = x_741;
} else {
 lean_dec_ref(x_741);
 x_795 = lean_box(0);
}
if (lean_is_scalar(x_795)) {
 x_796 = lean_alloc_ctor(1, 2, 0);
} else {
 x_796 = x_795;
}
lean_ctor_set(x_796, 0, x_793);
lean_ctor_set(x_796, 1, x_794);
return x_796;
}
}
}
block_562:
{
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_203);
lean_dec(x_199);
lean_dec(x_196);
lean_dec(x_194);
x_209 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_210 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_209, x_200, x_193);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_unbox(x_211);
lean_dec(x_211);
if (x_212 == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec(x_210);
x_11 = x_201;
x_12 = x_195;
x_13 = x_197;
x_14 = x_198;
x_15 = x_207;
x_16 = x_204;
x_17 = x_200;
x_18 = x_202;
x_19 = x_213;
goto block_148;
}
else
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_210);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_215 = lean_ctor_get(x_210, 1);
x_216 = lean_ctor_get(x_210, 0);
lean_dec(x_216);
lean_inc(x_197);
x_217 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_197, x_198, x_215);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_219 = lean_ctor_get(x_217, 0);
x_220 = lean_ctor_get(x_217, 1);
x_221 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_217, 7);
lean_ctor_set(x_217, 1, x_219);
lean_ctor_set(x_217, 0, x_221);
lean_ctor_set_tag(x_210, 7);
lean_ctor_set(x_210, 1, x_221);
lean_ctor_set(x_210, 0, x_217);
x_222 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_209, x_210, x_207, x_204, x_200, x_202, x_220);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_11 = x_201;
x_12 = x_195;
x_13 = x_197;
x_14 = x_198;
x_15 = x_207;
x_16 = x_204;
x_17 = x_200;
x_18 = x_202;
x_19 = x_223;
goto block_148;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_224 = lean_ctor_get(x_217, 0);
x_225 = lean_ctor_get(x_217, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_217);
x_226 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_227 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_224);
lean_ctor_set_tag(x_210, 7);
lean_ctor_set(x_210, 1, x_226);
lean_ctor_set(x_210, 0, x_227);
x_228 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_209, x_210, x_207, x_204, x_200, x_202, x_225);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
x_11 = x_201;
x_12 = x_195;
x_13 = x_197;
x_14 = x_198;
x_15 = x_207;
x_16 = x_204;
x_17 = x_200;
x_18 = x_202;
x_19 = x_229;
goto block_148;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_230 = lean_ctor_get(x_210, 1);
lean_inc(x_230);
lean_dec(x_210);
lean_inc(x_197);
x_231 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_197, x_198, x_230);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_234 = x_231;
} else {
 lean_dec_ref(x_231);
 x_234 = lean_box(0);
}
x_235 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(7, 2, 0);
} else {
 x_236 = x_234;
 lean_ctor_set_tag(x_236, 7);
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_232);
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_235);
x_238 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_209, x_237, x_207, x_204, x_200, x_202, x_233);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
x_11 = x_201;
x_12 = x_195;
x_13 = x_197;
x_14 = x_198;
x_15 = x_207;
x_16 = x_204;
x_17 = x_200;
x_18 = x_202;
x_19 = x_239;
goto block_148;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_201);
x_240 = lean_ctor_get(x_208, 0);
lean_inc(x_240);
lean_dec(x_208);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; 
lean_dec(x_241);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_203);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
x_242 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_240, x_198, x_207, x_204, x_200, x_202, x_193);
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_204);
lean_dec(x_207);
lean_dec(x_198);
return x_242;
}
else
{
lean_object* x_243; uint8_t x_244; 
x_243 = lean_ctor_get(x_240, 0);
lean_inc(x_243);
x_244 = !lean_is_exclusive(x_241);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_245 = lean_ctor_get(x_241, 0);
x_246 = lean_ctor_get(x_241, 2);
x_247 = lean_ctor_get(x_241, 1);
lean_dec(x_247);
x_248 = lean_int_mul(x_196, x_243);
x_249 = lean_int_mul(x_245, x_205);
x_250 = l_Lean_Meta_Grind_Arith_gcdExt(x_248, x_249);
lean_dec(x_249);
lean_dec(x_248);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec(x_251);
x_255 = lean_st_ref_take(x_198, x_193);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_256, 14);
lean_inc(x_257);
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
x_259 = lean_ctor_get(x_255, 1);
lean_inc(x_259);
lean_dec(x_255);
x_260 = !lean_is_exclusive(x_256);
if (x_260 == 0)
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_256, 14);
lean_dec(x_261);
x_262 = !lean_is_exclusive(x_257);
if (x_262 == 0)
{
lean_object* x_263; uint8_t x_264; 
x_263 = lean_ctor_get(x_257, 1);
lean_dec(x_263);
x_264 = !lean_is_exclusive(x_258);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_265 = lean_ctor_get(x_258, 5);
x_266 = lean_box(0);
x_267 = l_Lean_PersistentArray_set___redArg(x_265, x_195, x_266);
lean_ctor_set(x_258, 5, x_267);
x_268 = lean_st_ref_set(x_198, x_256, x_259);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_270 = lean_ctor_get(x_268, 1);
x_271 = lean_ctor_get(x_268, 0);
lean_dec(x_271);
x_272 = lean_int_mul(x_253, x_243);
lean_dec(x_253);
lean_inc(x_203);
x_273 = l_Int_Linear_Poly_mul(x_203, x_272);
lean_dec(x_272);
x_274 = lean_int_mul(x_254, x_205);
lean_dec(x_254);
lean_inc(x_246);
x_275 = l_Int_Linear_Poly_mul(x_246, x_274);
lean_dec(x_274);
x_276 = lean_int_mul(x_205, x_243);
lean_dec(x_243);
lean_dec(x_205);
x_277 = l_Int_Linear_Poly_combine(x_273, x_275);
lean_inc(x_252);
lean_ctor_set(x_241, 2, x_277);
lean_ctor_set(x_241, 1, x_195);
lean_ctor_set(x_241, 0, x_252);
lean_inc(x_240);
lean_inc(x_197);
lean_ctor_set_tag(x_268, 4);
lean_ctor_set(x_268, 1, x_240);
lean_ctor_set(x_268, 0, x_197);
x_278 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_241);
lean_ctor_set(x_278, 2, x_268);
lean_inc(x_202);
lean_inc(x_200);
lean_inc(x_204);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_199);
lean_inc(x_194);
lean_inc(x_198);
x_279 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_278, x_198, x_194, x_199, x_206, x_207, x_204, x_200, x_202, x_270);
if (lean_obj_tag(x_279) == 0)
{
uint8_t x_280; 
x_280 = !lean_is_exclusive(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_281 = lean_ctor_get(x_279, 1);
x_282 = lean_ctor_get(x_279, 0);
lean_dec(x_282);
x_283 = l_Int_Linear_Poly_mul(x_203, x_245);
lean_dec(x_245);
x_284 = lean_int_neg(x_196);
lean_dec(x_196);
x_285 = l_Int_Linear_Poly_mul(x_246, x_284);
lean_dec(x_284);
x_286 = l_Int_Linear_Poly_combine(x_283, x_285);
lean_inc(x_240);
lean_ctor_set_tag(x_279, 5);
lean_ctor_set(x_279, 1, x_240);
lean_ctor_set(x_279, 0, x_197);
x_287 = !lean_is_exclusive(x_240);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_240, 2);
lean_dec(x_288);
x_289 = lean_ctor_get(x_240, 1);
lean_dec(x_289);
x_290 = lean_ctor_get(x_240, 0);
lean_dec(x_290);
lean_ctor_set(x_240, 2, x_279);
lean_ctor_set(x_240, 1, x_286);
lean_ctor_set(x_240, 0, x_252);
x_1 = x_240;
x_2 = x_198;
x_3 = x_194;
x_4 = x_199;
x_5 = x_206;
x_6 = x_207;
x_7 = x_204;
x_8 = x_200;
x_9 = x_202;
x_10 = x_281;
goto _start;
}
else
{
lean_object* x_292; 
lean_dec(x_240);
x_292 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_292, 0, x_252);
lean_ctor_set(x_292, 1, x_286);
lean_ctor_set(x_292, 2, x_279);
x_1 = x_292;
x_2 = x_198;
x_3 = x_194;
x_4 = x_199;
x_5 = x_206;
x_6 = x_207;
x_7 = x_204;
x_8 = x_200;
x_9 = x_202;
x_10 = x_281;
goto _start;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_294 = lean_ctor_get(x_279, 1);
lean_inc(x_294);
lean_dec(x_279);
x_295 = l_Int_Linear_Poly_mul(x_203, x_245);
lean_dec(x_245);
x_296 = lean_int_neg(x_196);
lean_dec(x_196);
x_297 = l_Int_Linear_Poly_mul(x_246, x_296);
lean_dec(x_296);
x_298 = l_Int_Linear_Poly_combine(x_295, x_297);
lean_inc(x_240);
x_299 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_299, 0, x_197);
lean_ctor_set(x_299, 1, x_240);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 lean_ctor_release(x_240, 2);
 x_300 = x_240;
} else {
 lean_dec_ref(x_240);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(0, 3, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_252);
lean_ctor_set(x_301, 1, x_298);
lean_ctor_set(x_301, 2, x_299);
x_1 = x_301;
x_2 = x_198;
x_3 = x_194;
x_4 = x_199;
x_5 = x_206;
x_6 = x_207;
x_7 = x_204;
x_8 = x_200;
x_9 = x_202;
x_10 = x_294;
goto _start;
}
}
else
{
lean_dec(x_252);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_240);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_194);
return x_279;
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_303 = lean_ctor_get(x_268, 1);
lean_inc(x_303);
lean_dec(x_268);
x_304 = lean_int_mul(x_253, x_243);
lean_dec(x_253);
lean_inc(x_203);
x_305 = l_Int_Linear_Poly_mul(x_203, x_304);
lean_dec(x_304);
x_306 = lean_int_mul(x_254, x_205);
lean_dec(x_254);
lean_inc(x_246);
x_307 = l_Int_Linear_Poly_mul(x_246, x_306);
lean_dec(x_306);
x_308 = lean_int_mul(x_205, x_243);
lean_dec(x_243);
lean_dec(x_205);
x_309 = l_Int_Linear_Poly_combine(x_305, x_307);
lean_inc(x_252);
lean_ctor_set(x_241, 2, x_309);
lean_ctor_set(x_241, 1, x_195);
lean_ctor_set(x_241, 0, x_252);
lean_inc(x_240);
lean_inc(x_197);
x_310 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_310, 0, x_197);
lean_ctor_set(x_310, 1, x_240);
x_311 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_241);
lean_ctor_set(x_311, 2, x_310);
lean_inc(x_202);
lean_inc(x_200);
lean_inc(x_204);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_199);
lean_inc(x_194);
lean_inc(x_198);
x_312 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_311, x_198, x_194, x_199, x_206, x_207, x_204, x_200, x_202, x_303);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_314 = x_312;
} else {
 lean_dec_ref(x_312);
 x_314 = lean_box(0);
}
x_315 = l_Int_Linear_Poly_mul(x_203, x_245);
lean_dec(x_245);
x_316 = lean_int_neg(x_196);
lean_dec(x_196);
x_317 = l_Int_Linear_Poly_mul(x_246, x_316);
lean_dec(x_316);
x_318 = l_Int_Linear_Poly_combine(x_315, x_317);
lean_inc(x_240);
if (lean_is_scalar(x_314)) {
 x_319 = lean_alloc_ctor(5, 2, 0);
} else {
 x_319 = x_314;
 lean_ctor_set_tag(x_319, 5);
}
lean_ctor_set(x_319, 0, x_197);
lean_ctor_set(x_319, 1, x_240);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 lean_ctor_release(x_240, 2);
 x_320 = x_240;
} else {
 lean_dec_ref(x_240);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(0, 3, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_252);
lean_ctor_set(x_321, 1, x_318);
lean_ctor_set(x_321, 2, x_319);
x_1 = x_321;
x_2 = x_198;
x_3 = x_194;
x_4 = x_199;
x_5 = x_206;
x_6 = x_207;
x_7 = x_204;
x_8 = x_200;
x_9 = x_202;
x_10 = x_313;
goto _start;
}
else
{
lean_dec(x_252);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_240);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_194);
return x_312;
}
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_323 = lean_ctor_get(x_258, 0);
x_324 = lean_ctor_get(x_258, 1);
x_325 = lean_ctor_get(x_258, 2);
x_326 = lean_ctor_get(x_258, 3);
x_327 = lean_ctor_get(x_258, 4);
x_328 = lean_ctor_get(x_258, 5);
x_329 = lean_ctor_get(x_258, 6);
x_330 = lean_ctor_get(x_258, 7);
x_331 = lean_ctor_get(x_258, 8);
x_332 = lean_ctor_get(x_258, 9);
x_333 = lean_ctor_get(x_258, 10);
x_334 = lean_ctor_get(x_258, 11);
x_335 = lean_ctor_get(x_258, 12);
x_336 = lean_ctor_get(x_258, 13);
x_337 = lean_ctor_get_uint8(x_258, sizeof(void*)*17);
x_338 = lean_ctor_get(x_258, 14);
x_339 = lean_ctor_get(x_258, 15);
x_340 = lean_ctor_get(x_258, 16);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_258);
x_341 = lean_box(0);
x_342 = l_Lean_PersistentArray_set___redArg(x_328, x_195, x_341);
x_343 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_343, 0, x_323);
lean_ctor_set(x_343, 1, x_324);
lean_ctor_set(x_343, 2, x_325);
lean_ctor_set(x_343, 3, x_326);
lean_ctor_set(x_343, 4, x_327);
lean_ctor_set(x_343, 5, x_342);
lean_ctor_set(x_343, 6, x_329);
lean_ctor_set(x_343, 7, x_330);
lean_ctor_set(x_343, 8, x_331);
lean_ctor_set(x_343, 9, x_332);
lean_ctor_set(x_343, 10, x_333);
lean_ctor_set(x_343, 11, x_334);
lean_ctor_set(x_343, 12, x_335);
lean_ctor_set(x_343, 13, x_336);
lean_ctor_set(x_343, 14, x_338);
lean_ctor_set(x_343, 15, x_339);
lean_ctor_set(x_343, 16, x_340);
lean_ctor_set_uint8(x_343, sizeof(void*)*17, x_337);
lean_ctor_set(x_257, 1, x_343);
x_344 = lean_st_ref_set(x_198, x_256, x_259);
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_346 = x_344;
} else {
 lean_dec_ref(x_344);
 x_346 = lean_box(0);
}
x_347 = lean_int_mul(x_253, x_243);
lean_dec(x_253);
lean_inc(x_203);
x_348 = l_Int_Linear_Poly_mul(x_203, x_347);
lean_dec(x_347);
x_349 = lean_int_mul(x_254, x_205);
lean_dec(x_254);
lean_inc(x_246);
x_350 = l_Int_Linear_Poly_mul(x_246, x_349);
lean_dec(x_349);
x_351 = lean_int_mul(x_205, x_243);
lean_dec(x_243);
lean_dec(x_205);
x_352 = l_Int_Linear_Poly_combine(x_348, x_350);
lean_inc(x_252);
lean_ctor_set(x_241, 2, x_352);
lean_ctor_set(x_241, 1, x_195);
lean_ctor_set(x_241, 0, x_252);
lean_inc(x_240);
lean_inc(x_197);
if (lean_is_scalar(x_346)) {
 x_353 = lean_alloc_ctor(4, 2, 0);
} else {
 x_353 = x_346;
 lean_ctor_set_tag(x_353, 4);
}
lean_ctor_set(x_353, 0, x_197);
lean_ctor_set(x_353, 1, x_240);
x_354 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_241);
lean_ctor_set(x_354, 2, x_353);
lean_inc(x_202);
lean_inc(x_200);
lean_inc(x_204);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_199);
lean_inc(x_194);
lean_inc(x_198);
x_355 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_354, x_198, x_194, x_199, x_206, x_207, x_204, x_200, x_202, x_345);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_356 = lean_ctor_get(x_355, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_357 = x_355;
} else {
 lean_dec_ref(x_355);
 x_357 = lean_box(0);
}
x_358 = l_Int_Linear_Poly_mul(x_203, x_245);
lean_dec(x_245);
x_359 = lean_int_neg(x_196);
lean_dec(x_196);
x_360 = l_Int_Linear_Poly_mul(x_246, x_359);
lean_dec(x_359);
x_361 = l_Int_Linear_Poly_combine(x_358, x_360);
lean_inc(x_240);
if (lean_is_scalar(x_357)) {
 x_362 = lean_alloc_ctor(5, 2, 0);
} else {
 x_362 = x_357;
 lean_ctor_set_tag(x_362, 5);
}
lean_ctor_set(x_362, 0, x_197);
lean_ctor_set(x_362, 1, x_240);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 lean_ctor_release(x_240, 2);
 x_363 = x_240;
} else {
 lean_dec_ref(x_240);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(0, 3, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_252);
lean_ctor_set(x_364, 1, x_361);
lean_ctor_set(x_364, 2, x_362);
x_1 = x_364;
x_2 = x_198;
x_3 = x_194;
x_4 = x_199;
x_5 = x_206;
x_6 = x_207;
x_7 = x_204;
x_8 = x_200;
x_9 = x_202;
x_10 = x_356;
goto _start;
}
else
{
lean_dec(x_252);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_240);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_194);
return x_355;
}
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_366 = lean_ctor_get(x_257, 0);
x_367 = lean_ctor_get(x_257, 2);
x_368 = lean_ctor_get(x_257, 3);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_257);
x_369 = lean_ctor_get(x_258, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_258, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_258, 2);
lean_inc(x_371);
x_372 = lean_ctor_get(x_258, 3);
lean_inc(x_372);
x_373 = lean_ctor_get(x_258, 4);
lean_inc(x_373);
x_374 = lean_ctor_get(x_258, 5);
lean_inc(x_374);
x_375 = lean_ctor_get(x_258, 6);
lean_inc(x_375);
x_376 = lean_ctor_get(x_258, 7);
lean_inc(x_376);
x_377 = lean_ctor_get(x_258, 8);
lean_inc(x_377);
x_378 = lean_ctor_get(x_258, 9);
lean_inc(x_378);
x_379 = lean_ctor_get(x_258, 10);
lean_inc(x_379);
x_380 = lean_ctor_get(x_258, 11);
lean_inc(x_380);
x_381 = lean_ctor_get(x_258, 12);
lean_inc(x_381);
x_382 = lean_ctor_get(x_258, 13);
lean_inc(x_382);
x_383 = lean_ctor_get_uint8(x_258, sizeof(void*)*17);
x_384 = lean_ctor_get(x_258, 14);
lean_inc(x_384);
x_385 = lean_ctor_get(x_258, 15);
lean_inc(x_385);
x_386 = lean_ctor_get(x_258, 16);
lean_inc(x_386);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 lean_ctor_release(x_258, 3);
 lean_ctor_release(x_258, 4);
 lean_ctor_release(x_258, 5);
 lean_ctor_release(x_258, 6);
 lean_ctor_release(x_258, 7);
 lean_ctor_release(x_258, 8);
 lean_ctor_release(x_258, 9);
 lean_ctor_release(x_258, 10);
 lean_ctor_release(x_258, 11);
 lean_ctor_release(x_258, 12);
 lean_ctor_release(x_258, 13);
 lean_ctor_release(x_258, 14);
 lean_ctor_release(x_258, 15);
 lean_ctor_release(x_258, 16);
 x_387 = x_258;
} else {
 lean_dec_ref(x_258);
 x_387 = lean_box(0);
}
x_388 = lean_box(0);
x_389 = l_Lean_PersistentArray_set___redArg(x_374, x_195, x_388);
if (lean_is_scalar(x_387)) {
 x_390 = lean_alloc_ctor(0, 17, 1);
} else {
 x_390 = x_387;
}
lean_ctor_set(x_390, 0, x_369);
lean_ctor_set(x_390, 1, x_370);
lean_ctor_set(x_390, 2, x_371);
lean_ctor_set(x_390, 3, x_372);
lean_ctor_set(x_390, 4, x_373);
lean_ctor_set(x_390, 5, x_389);
lean_ctor_set(x_390, 6, x_375);
lean_ctor_set(x_390, 7, x_376);
lean_ctor_set(x_390, 8, x_377);
lean_ctor_set(x_390, 9, x_378);
lean_ctor_set(x_390, 10, x_379);
lean_ctor_set(x_390, 11, x_380);
lean_ctor_set(x_390, 12, x_381);
lean_ctor_set(x_390, 13, x_382);
lean_ctor_set(x_390, 14, x_384);
lean_ctor_set(x_390, 15, x_385);
lean_ctor_set(x_390, 16, x_386);
lean_ctor_set_uint8(x_390, sizeof(void*)*17, x_383);
x_391 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_391, 0, x_366);
lean_ctor_set(x_391, 1, x_390);
lean_ctor_set(x_391, 2, x_367);
lean_ctor_set(x_391, 3, x_368);
lean_ctor_set(x_256, 14, x_391);
x_392 = lean_st_ref_set(x_198, x_256, x_259);
x_393 = lean_ctor_get(x_392, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_394 = x_392;
} else {
 lean_dec_ref(x_392);
 x_394 = lean_box(0);
}
x_395 = lean_int_mul(x_253, x_243);
lean_dec(x_253);
lean_inc(x_203);
x_396 = l_Int_Linear_Poly_mul(x_203, x_395);
lean_dec(x_395);
x_397 = lean_int_mul(x_254, x_205);
lean_dec(x_254);
lean_inc(x_246);
x_398 = l_Int_Linear_Poly_mul(x_246, x_397);
lean_dec(x_397);
x_399 = lean_int_mul(x_205, x_243);
lean_dec(x_243);
lean_dec(x_205);
x_400 = l_Int_Linear_Poly_combine(x_396, x_398);
lean_inc(x_252);
lean_ctor_set(x_241, 2, x_400);
lean_ctor_set(x_241, 1, x_195);
lean_ctor_set(x_241, 0, x_252);
lean_inc(x_240);
lean_inc(x_197);
if (lean_is_scalar(x_394)) {
 x_401 = lean_alloc_ctor(4, 2, 0);
} else {
 x_401 = x_394;
 lean_ctor_set_tag(x_401, 4);
}
lean_ctor_set(x_401, 0, x_197);
lean_ctor_set(x_401, 1, x_240);
x_402 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_241);
lean_ctor_set(x_402, 2, x_401);
lean_inc(x_202);
lean_inc(x_200);
lean_inc(x_204);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_199);
lean_inc(x_194);
lean_inc(x_198);
x_403 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_402, x_198, x_194, x_199, x_206, x_207, x_204, x_200, x_202, x_393);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_405 = x_403;
} else {
 lean_dec_ref(x_403);
 x_405 = lean_box(0);
}
x_406 = l_Int_Linear_Poly_mul(x_203, x_245);
lean_dec(x_245);
x_407 = lean_int_neg(x_196);
lean_dec(x_196);
x_408 = l_Int_Linear_Poly_mul(x_246, x_407);
lean_dec(x_407);
x_409 = l_Int_Linear_Poly_combine(x_406, x_408);
lean_inc(x_240);
if (lean_is_scalar(x_405)) {
 x_410 = lean_alloc_ctor(5, 2, 0);
} else {
 x_410 = x_405;
 lean_ctor_set_tag(x_410, 5);
}
lean_ctor_set(x_410, 0, x_197);
lean_ctor_set(x_410, 1, x_240);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 lean_ctor_release(x_240, 2);
 x_411 = x_240;
} else {
 lean_dec_ref(x_240);
 x_411 = lean_box(0);
}
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(0, 3, 0);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_252);
lean_ctor_set(x_412, 1, x_409);
lean_ctor_set(x_412, 2, x_410);
x_1 = x_412;
x_2 = x_198;
x_3 = x_194;
x_4 = x_199;
x_5 = x_206;
x_6 = x_207;
x_7 = x_204;
x_8 = x_200;
x_9 = x_202;
x_10 = x_404;
goto _start;
}
else
{
lean_dec(x_252);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_240);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_194);
return x_403;
}
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_414 = lean_ctor_get(x_256, 0);
x_415 = lean_ctor_get(x_256, 1);
x_416 = lean_ctor_get(x_256, 2);
x_417 = lean_ctor_get(x_256, 3);
x_418 = lean_ctor_get(x_256, 4);
x_419 = lean_ctor_get(x_256, 5);
x_420 = lean_ctor_get(x_256, 6);
x_421 = lean_ctor_get(x_256, 7);
x_422 = lean_ctor_get_uint8(x_256, sizeof(void*)*16);
x_423 = lean_ctor_get(x_256, 8);
x_424 = lean_ctor_get(x_256, 9);
x_425 = lean_ctor_get(x_256, 10);
x_426 = lean_ctor_get(x_256, 11);
x_427 = lean_ctor_get(x_256, 12);
x_428 = lean_ctor_get(x_256, 13);
x_429 = lean_ctor_get(x_256, 15);
lean_inc(x_429);
lean_inc(x_428);
lean_inc(x_427);
lean_inc(x_426);
lean_inc(x_425);
lean_inc(x_424);
lean_inc(x_423);
lean_inc(x_421);
lean_inc(x_420);
lean_inc(x_419);
lean_inc(x_418);
lean_inc(x_417);
lean_inc(x_416);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_256);
x_430 = lean_ctor_get(x_257, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_257, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_257, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 lean_ctor_release(x_257, 2);
 lean_ctor_release(x_257, 3);
 x_433 = x_257;
} else {
 lean_dec_ref(x_257);
 x_433 = lean_box(0);
}
x_434 = lean_ctor_get(x_258, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_258, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_258, 2);
lean_inc(x_436);
x_437 = lean_ctor_get(x_258, 3);
lean_inc(x_437);
x_438 = lean_ctor_get(x_258, 4);
lean_inc(x_438);
x_439 = lean_ctor_get(x_258, 5);
lean_inc(x_439);
x_440 = lean_ctor_get(x_258, 6);
lean_inc(x_440);
x_441 = lean_ctor_get(x_258, 7);
lean_inc(x_441);
x_442 = lean_ctor_get(x_258, 8);
lean_inc(x_442);
x_443 = lean_ctor_get(x_258, 9);
lean_inc(x_443);
x_444 = lean_ctor_get(x_258, 10);
lean_inc(x_444);
x_445 = lean_ctor_get(x_258, 11);
lean_inc(x_445);
x_446 = lean_ctor_get(x_258, 12);
lean_inc(x_446);
x_447 = lean_ctor_get(x_258, 13);
lean_inc(x_447);
x_448 = lean_ctor_get_uint8(x_258, sizeof(void*)*17);
x_449 = lean_ctor_get(x_258, 14);
lean_inc(x_449);
x_450 = lean_ctor_get(x_258, 15);
lean_inc(x_450);
x_451 = lean_ctor_get(x_258, 16);
lean_inc(x_451);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 lean_ctor_release(x_258, 3);
 lean_ctor_release(x_258, 4);
 lean_ctor_release(x_258, 5);
 lean_ctor_release(x_258, 6);
 lean_ctor_release(x_258, 7);
 lean_ctor_release(x_258, 8);
 lean_ctor_release(x_258, 9);
 lean_ctor_release(x_258, 10);
 lean_ctor_release(x_258, 11);
 lean_ctor_release(x_258, 12);
 lean_ctor_release(x_258, 13);
 lean_ctor_release(x_258, 14);
 lean_ctor_release(x_258, 15);
 lean_ctor_release(x_258, 16);
 x_452 = x_258;
} else {
 lean_dec_ref(x_258);
 x_452 = lean_box(0);
}
x_453 = lean_box(0);
x_454 = l_Lean_PersistentArray_set___redArg(x_439, x_195, x_453);
if (lean_is_scalar(x_452)) {
 x_455 = lean_alloc_ctor(0, 17, 1);
} else {
 x_455 = x_452;
}
lean_ctor_set(x_455, 0, x_434);
lean_ctor_set(x_455, 1, x_435);
lean_ctor_set(x_455, 2, x_436);
lean_ctor_set(x_455, 3, x_437);
lean_ctor_set(x_455, 4, x_438);
lean_ctor_set(x_455, 5, x_454);
lean_ctor_set(x_455, 6, x_440);
lean_ctor_set(x_455, 7, x_441);
lean_ctor_set(x_455, 8, x_442);
lean_ctor_set(x_455, 9, x_443);
lean_ctor_set(x_455, 10, x_444);
lean_ctor_set(x_455, 11, x_445);
lean_ctor_set(x_455, 12, x_446);
lean_ctor_set(x_455, 13, x_447);
lean_ctor_set(x_455, 14, x_449);
lean_ctor_set(x_455, 15, x_450);
lean_ctor_set(x_455, 16, x_451);
lean_ctor_set_uint8(x_455, sizeof(void*)*17, x_448);
if (lean_is_scalar(x_433)) {
 x_456 = lean_alloc_ctor(0, 4, 0);
} else {
 x_456 = x_433;
}
lean_ctor_set(x_456, 0, x_430);
lean_ctor_set(x_456, 1, x_455);
lean_ctor_set(x_456, 2, x_431);
lean_ctor_set(x_456, 3, x_432);
x_457 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_457, 0, x_414);
lean_ctor_set(x_457, 1, x_415);
lean_ctor_set(x_457, 2, x_416);
lean_ctor_set(x_457, 3, x_417);
lean_ctor_set(x_457, 4, x_418);
lean_ctor_set(x_457, 5, x_419);
lean_ctor_set(x_457, 6, x_420);
lean_ctor_set(x_457, 7, x_421);
lean_ctor_set(x_457, 8, x_423);
lean_ctor_set(x_457, 9, x_424);
lean_ctor_set(x_457, 10, x_425);
lean_ctor_set(x_457, 11, x_426);
lean_ctor_set(x_457, 12, x_427);
lean_ctor_set(x_457, 13, x_428);
lean_ctor_set(x_457, 14, x_456);
lean_ctor_set(x_457, 15, x_429);
lean_ctor_set_uint8(x_457, sizeof(void*)*16, x_422);
x_458 = lean_st_ref_set(x_198, x_457, x_259);
x_459 = lean_ctor_get(x_458, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_460 = x_458;
} else {
 lean_dec_ref(x_458);
 x_460 = lean_box(0);
}
x_461 = lean_int_mul(x_253, x_243);
lean_dec(x_253);
lean_inc(x_203);
x_462 = l_Int_Linear_Poly_mul(x_203, x_461);
lean_dec(x_461);
x_463 = lean_int_mul(x_254, x_205);
lean_dec(x_254);
lean_inc(x_246);
x_464 = l_Int_Linear_Poly_mul(x_246, x_463);
lean_dec(x_463);
x_465 = lean_int_mul(x_205, x_243);
lean_dec(x_243);
lean_dec(x_205);
x_466 = l_Int_Linear_Poly_combine(x_462, x_464);
lean_inc(x_252);
lean_ctor_set(x_241, 2, x_466);
lean_ctor_set(x_241, 1, x_195);
lean_ctor_set(x_241, 0, x_252);
lean_inc(x_240);
lean_inc(x_197);
if (lean_is_scalar(x_460)) {
 x_467 = lean_alloc_ctor(4, 2, 0);
} else {
 x_467 = x_460;
 lean_ctor_set_tag(x_467, 4);
}
lean_ctor_set(x_467, 0, x_197);
lean_ctor_set(x_467, 1, x_240);
x_468 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_468, 0, x_465);
lean_ctor_set(x_468, 1, x_241);
lean_ctor_set(x_468, 2, x_467);
lean_inc(x_202);
lean_inc(x_200);
lean_inc(x_204);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_199);
lean_inc(x_194);
lean_inc(x_198);
x_469 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_468, x_198, x_194, x_199, x_206, x_207, x_204, x_200, x_202, x_459);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_470 = lean_ctor_get(x_469, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_471 = x_469;
} else {
 lean_dec_ref(x_469);
 x_471 = lean_box(0);
}
x_472 = l_Int_Linear_Poly_mul(x_203, x_245);
lean_dec(x_245);
x_473 = lean_int_neg(x_196);
lean_dec(x_196);
x_474 = l_Int_Linear_Poly_mul(x_246, x_473);
lean_dec(x_473);
x_475 = l_Int_Linear_Poly_combine(x_472, x_474);
lean_inc(x_240);
if (lean_is_scalar(x_471)) {
 x_476 = lean_alloc_ctor(5, 2, 0);
} else {
 x_476 = x_471;
 lean_ctor_set_tag(x_476, 5);
}
lean_ctor_set(x_476, 0, x_197);
lean_ctor_set(x_476, 1, x_240);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 lean_ctor_release(x_240, 2);
 x_477 = x_240;
} else {
 lean_dec_ref(x_240);
 x_477 = lean_box(0);
}
if (lean_is_scalar(x_477)) {
 x_478 = lean_alloc_ctor(0, 3, 0);
} else {
 x_478 = x_477;
}
lean_ctor_set(x_478, 0, x_252);
lean_ctor_set(x_478, 1, x_475);
lean_ctor_set(x_478, 2, x_476);
x_1 = x_478;
x_2 = x_198;
x_3 = x_194;
x_4 = x_199;
x_5 = x_206;
x_6 = x_207;
x_7 = x_204;
x_8 = x_200;
x_9 = x_202;
x_10 = x_470;
goto _start;
}
else
{
lean_dec(x_252);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_240);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_194);
return x_469;
}
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; uint8_t x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_480 = lean_ctor_get(x_241, 0);
x_481 = lean_ctor_get(x_241, 2);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_241);
x_482 = lean_int_mul(x_196, x_243);
x_483 = lean_int_mul(x_480, x_205);
x_484 = l_Lean_Meta_Grind_Arith_gcdExt(x_482, x_483);
lean_dec(x_483);
lean_dec(x_482);
x_485 = lean_ctor_get(x_484, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_484, 0);
lean_inc(x_486);
lean_dec(x_484);
x_487 = lean_ctor_get(x_485, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_485, 1);
lean_inc(x_488);
lean_dec(x_485);
x_489 = lean_st_ref_take(x_198, x_193);
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_490, 14);
lean_inc(x_491);
x_492 = lean_ctor_get(x_491, 1);
lean_inc(x_492);
x_493 = lean_ctor_get(x_489, 1);
lean_inc(x_493);
lean_dec(x_489);
x_494 = lean_ctor_get(x_490, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_490, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_490, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_490, 3);
lean_inc(x_497);
x_498 = lean_ctor_get(x_490, 4);
lean_inc(x_498);
x_499 = lean_ctor_get(x_490, 5);
lean_inc(x_499);
x_500 = lean_ctor_get(x_490, 6);
lean_inc(x_500);
x_501 = lean_ctor_get(x_490, 7);
lean_inc(x_501);
x_502 = lean_ctor_get_uint8(x_490, sizeof(void*)*16);
x_503 = lean_ctor_get(x_490, 8);
lean_inc(x_503);
x_504 = lean_ctor_get(x_490, 9);
lean_inc(x_504);
x_505 = lean_ctor_get(x_490, 10);
lean_inc(x_505);
x_506 = lean_ctor_get(x_490, 11);
lean_inc(x_506);
x_507 = lean_ctor_get(x_490, 12);
lean_inc(x_507);
x_508 = lean_ctor_get(x_490, 13);
lean_inc(x_508);
x_509 = lean_ctor_get(x_490, 15);
lean_inc(x_509);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 lean_ctor_release(x_490, 2);
 lean_ctor_release(x_490, 3);
 lean_ctor_release(x_490, 4);
 lean_ctor_release(x_490, 5);
 lean_ctor_release(x_490, 6);
 lean_ctor_release(x_490, 7);
 lean_ctor_release(x_490, 8);
 lean_ctor_release(x_490, 9);
 lean_ctor_release(x_490, 10);
 lean_ctor_release(x_490, 11);
 lean_ctor_release(x_490, 12);
 lean_ctor_release(x_490, 13);
 lean_ctor_release(x_490, 14);
 lean_ctor_release(x_490, 15);
 x_510 = x_490;
} else {
 lean_dec_ref(x_490);
 x_510 = lean_box(0);
}
x_511 = lean_ctor_get(x_491, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_491, 2);
lean_inc(x_512);
x_513 = lean_ctor_get(x_491, 3);
lean_inc(x_513);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 lean_ctor_release(x_491, 2);
 lean_ctor_release(x_491, 3);
 x_514 = x_491;
} else {
 lean_dec_ref(x_491);
 x_514 = lean_box(0);
}
x_515 = lean_ctor_get(x_492, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_492, 1);
lean_inc(x_516);
x_517 = lean_ctor_get(x_492, 2);
lean_inc(x_517);
x_518 = lean_ctor_get(x_492, 3);
lean_inc(x_518);
x_519 = lean_ctor_get(x_492, 4);
lean_inc(x_519);
x_520 = lean_ctor_get(x_492, 5);
lean_inc(x_520);
x_521 = lean_ctor_get(x_492, 6);
lean_inc(x_521);
x_522 = lean_ctor_get(x_492, 7);
lean_inc(x_522);
x_523 = lean_ctor_get(x_492, 8);
lean_inc(x_523);
x_524 = lean_ctor_get(x_492, 9);
lean_inc(x_524);
x_525 = lean_ctor_get(x_492, 10);
lean_inc(x_525);
x_526 = lean_ctor_get(x_492, 11);
lean_inc(x_526);
x_527 = lean_ctor_get(x_492, 12);
lean_inc(x_527);
x_528 = lean_ctor_get(x_492, 13);
lean_inc(x_528);
x_529 = lean_ctor_get_uint8(x_492, sizeof(void*)*17);
x_530 = lean_ctor_get(x_492, 14);
lean_inc(x_530);
x_531 = lean_ctor_get(x_492, 15);
lean_inc(x_531);
x_532 = lean_ctor_get(x_492, 16);
lean_inc(x_532);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 lean_ctor_release(x_492, 2);
 lean_ctor_release(x_492, 3);
 lean_ctor_release(x_492, 4);
 lean_ctor_release(x_492, 5);
 lean_ctor_release(x_492, 6);
 lean_ctor_release(x_492, 7);
 lean_ctor_release(x_492, 8);
 lean_ctor_release(x_492, 9);
 lean_ctor_release(x_492, 10);
 lean_ctor_release(x_492, 11);
 lean_ctor_release(x_492, 12);
 lean_ctor_release(x_492, 13);
 lean_ctor_release(x_492, 14);
 lean_ctor_release(x_492, 15);
 lean_ctor_release(x_492, 16);
 x_533 = x_492;
} else {
 lean_dec_ref(x_492);
 x_533 = lean_box(0);
}
x_534 = lean_box(0);
x_535 = l_Lean_PersistentArray_set___redArg(x_520, x_195, x_534);
if (lean_is_scalar(x_533)) {
 x_536 = lean_alloc_ctor(0, 17, 1);
} else {
 x_536 = x_533;
}
lean_ctor_set(x_536, 0, x_515);
lean_ctor_set(x_536, 1, x_516);
lean_ctor_set(x_536, 2, x_517);
lean_ctor_set(x_536, 3, x_518);
lean_ctor_set(x_536, 4, x_519);
lean_ctor_set(x_536, 5, x_535);
lean_ctor_set(x_536, 6, x_521);
lean_ctor_set(x_536, 7, x_522);
lean_ctor_set(x_536, 8, x_523);
lean_ctor_set(x_536, 9, x_524);
lean_ctor_set(x_536, 10, x_525);
lean_ctor_set(x_536, 11, x_526);
lean_ctor_set(x_536, 12, x_527);
lean_ctor_set(x_536, 13, x_528);
lean_ctor_set(x_536, 14, x_530);
lean_ctor_set(x_536, 15, x_531);
lean_ctor_set(x_536, 16, x_532);
lean_ctor_set_uint8(x_536, sizeof(void*)*17, x_529);
if (lean_is_scalar(x_514)) {
 x_537 = lean_alloc_ctor(0, 4, 0);
} else {
 x_537 = x_514;
}
lean_ctor_set(x_537, 0, x_511);
lean_ctor_set(x_537, 1, x_536);
lean_ctor_set(x_537, 2, x_512);
lean_ctor_set(x_537, 3, x_513);
if (lean_is_scalar(x_510)) {
 x_538 = lean_alloc_ctor(0, 16, 1);
} else {
 x_538 = x_510;
}
lean_ctor_set(x_538, 0, x_494);
lean_ctor_set(x_538, 1, x_495);
lean_ctor_set(x_538, 2, x_496);
lean_ctor_set(x_538, 3, x_497);
lean_ctor_set(x_538, 4, x_498);
lean_ctor_set(x_538, 5, x_499);
lean_ctor_set(x_538, 6, x_500);
lean_ctor_set(x_538, 7, x_501);
lean_ctor_set(x_538, 8, x_503);
lean_ctor_set(x_538, 9, x_504);
lean_ctor_set(x_538, 10, x_505);
lean_ctor_set(x_538, 11, x_506);
lean_ctor_set(x_538, 12, x_507);
lean_ctor_set(x_538, 13, x_508);
lean_ctor_set(x_538, 14, x_537);
lean_ctor_set(x_538, 15, x_509);
lean_ctor_set_uint8(x_538, sizeof(void*)*16, x_502);
x_539 = lean_st_ref_set(x_198, x_538, x_493);
x_540 = lean_ctor_get(x_539, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_541 = x_539;
} else {
 lean_dec_ref(x_539);
 x_541 = lean_box(0);
}
x_542 = lean_int_mul(x_487, x_243);
lean_dec(x_487);
lean_inc(x_203);
x_543 = l_Int_Linear_Poly_mul(x_203, x_542);
lean_dec(x_542);
x_544 = lean_int_mul(x_488, x_205);
lean_dec(x_488);
lean_inc(x_481);
x_545 = l_Int_Linear_Poly_mul(x_481, x_544);
lean_dec(x_544);
x_546 = lean_int_mul(x_205, x_243);
lean_dec(x_243);
lean_dec(x_205);
x_547 = l_Int_Linear_Poly_combine(x_543, x_545);
lean_inc(x_486);
x_548 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_548, 0, x_486);
lean_ctor_set(x_548, 1, x_195);
lean_ctor_set(x_548, 2, x_547);
lean_inc(x_240);
lean_inc(x_197);
if (lean_is_scalar(x_541)) {
 x_549 = lean_alloc_ctor(4, 2, 0);
} else {
 x_549 = x_541;
 lean_ctor_set_tag(x_549, 4);
}
lean_ctor_set(x_549, 0, x_197);
lean_ctor_set(x_549, 1, x_240);
x_550 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_550, 0, x_546);
lean_ctor_set(x_550, 1, x_548);
lean_ctor_set(x_550, 2, x_549);
lean_inc(x_202);
lean_inc(x_200);
lean_inc(x_204);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_199);
lean_inc(x_194);
lean_inc(x_198);
x_551 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_550, x_198, x_194, x_199, x_206, x_207, x_204, x_200, x_202, x_540);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_552 = lean_ctor_get(x_551, 1);
lean_inc(x_552);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 x_553 = x_551;
} else {
 lean_dec_ref(x_551);
 x_553 = lean_box(0);
}
x_554 = l_Int_Linear_Poly_mul(x_203, x_480);
lean_dec(x_480);
x_555 = lean_int_neg(x_196);
lean_dec(x_196);
x_556 = l_Int_Linear_Poly_mul(x_481, x_555);
lean_dec(x_555);
x_557 = l_Int_Linear_Poly_combine(x_554, x_556);
lean_inc(x_240);
if (lean_is_scalar(x_553)) {
 x_558 = lean_alloc_ctor(5, 2, 0);
} else {
 x_558 = x_553;
 lean_ctor_set_tag(x_558, 5);
}
lean_ctor_set(x_558, 0, x_197);
lean_ctor_set(x_558, 1, x_240);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 lean_ctor_release(x_240, 2);
 x_559 = x_240;
} else {
 lean_dec_ref(x_240);
 x_559 = lean_box(0);
}
if (lean_is_scalar(x_559)) {
 x_560 = lean_alloc_ctor(0, 3, 0);
} else {
 x_560 = x_559;
}
lean_ctor_set(x_560, 0, x_486);
lean_ctor_set(x_560, 1, x_557);
lean_ctor_set(x_560, 2, x_558);
x_1 = x_560;
x_2 = x_198;
x_3 = x_194;
x_4 = x_199;
x_5 = x_206;
x_6 = x_207;
x_7 = x_204;
x_8 = x_200;
x_9 = x_202;
x_10 = x_552;
goto _start;
}
else
{
lean_dec(x_486);
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_240);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_194);
return x_551;
}
}
}
}
}
}
else
{
uint8_t x_808; 
lean_free_object(x_8);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_808 = !lean_is_exclusive(x_187);
if (x_808 == 0)
{
lean_object* x_809; lean_object* x_810; 
x_809 = lean_ctor_get(x_187, 0);
lean_dec(x_809);
x_810 = lean_box(0);
lean_ctor_set(x_187, 0, x_810);
return x_187;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; 
x_811 = lean_ctor_get(x_187, 1);
lean_inc(x_811);
lean_dec(x_187);
x_812 = lean_box(0);
x_813 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_813, 0, x_812);
lean_ctor_set(x_813, 1, x_811);
return x_813;
}
}
}
else
{
lean_object* x_814; 
lean_free_object(x_8);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_814 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_178, x_10);
return x_814;
}
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; uint8_t x_826; lean_object* x_827; uint8_t x_828; lean_object* x_829; uint8_t x_830; 
x_815 = lean_ctor_get(x_8, 0);
x_816 = lean_ctor_get(x_8, 1);
x_817 = lean_ctor_get(x_8, 2);
x_818 = lean_ctor_get(x_8, 3);
x_819 = lean_ctor_get(x_8, 4);
x_820 = lean_ctor_get(x_8, 5);
x_821 = lean_ctor_get(x_8, 6);
x_822 = lean_ctor_get(x_8, 7);
x_823 = lean_ctor_get(x_8, 8);
x_824 = lean_ctor_get(x_8, 9);
x_825 = lean_ctor_get(x_8, 10);
x_826 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_827 = lean_ctor_get(x_8, 11);
x_828 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_829 = lean_ctor_get(x_8, 12);
lean_inc(x_829);
lean_inc(x_827);
lean_inc(x_825);
lean_inc(x_824);
lean_inc(x_823);
lean_inc(x_822);
lean_inc(x_821);
lean_inc(x_820);
lean_inc(x_819);
lean_inc(x_818);
lean_inc(x_817);
lean_inc(x_816);
lean_inc(x_815);
lean_dec(x_8);
x_830 = lean_nat_dec_eq(x_818, x_819);
if (x_830 == 0)
{
lean_object* x_831; lean_object* x_832; uint8_t x_833; 
x_831 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_832 = lean_ctor_get(x_831, 0);
lean_inc(x_832);
x_833 = lean_unbox(x_832);
lean_dec(x_832);
if (x_833 == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; uint8_t x_1055; 
x_834 = lean_ctor_get(x_831, 1);
lean_inc(x_834);
lean_dec(x_831);
x_835 = lean_unsigned_to_nat(1u);
x_836 = lean_nat_add(x_818, x_835);
lean_dec(x_818);
x_837 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_837, 0, x_815);
lean_ctor_set(x_837, 1, x_816);
lean_ctor_set(x_837, 2, x_817);
lean_ctor_set(x_837, 3, x_836);
lean_ctor_set(x_837, 4, x_819);
lean_ctor_set(x_837, 5, x_820);
lean_ctor_set(x_837, 6, x_821);
lean_ctor_set(x_837, 7, x_822);
lean_ctor_set(x_837, 8, x_823);
lean_ctor_set(x_837, 9, x_824);
lean_ctor_set(x_837, 10, x_825);
lean_ctor_set(x_837, 11, x_827);
lean_ctor_set(x_837, 12, x_829);
lean_ctor_set_uint8(x_837, sizeof(void*)*13, x_826);
lean_ctor_set_uint8(x_837, sizeof(void*)*13 + 1, x_828);
x_958 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_959 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_958, x_837, x_834);
x_960 = lean_ctor_get(x_959, 0);
lean_inc(x_960);
x_961 = lean_ctor_get(x_959, 1);
lean_inc(x_961);
if (lean_is_exclusive(x_959)) {
 lean_ctor_release(x_959, 0);
 lean_ctor_release(x_959, 1);
 x_962 = x_959;
} else {
 lean_dec_ref(x_959);
 x_962 = lean_box(0);
}
x_963 = lean_box(0);
x_1055 = lean_unbox(x_960);
lean_dec(x_960);
if (x_1055 == 0)
{
lean_dec(x_962);
x_988 = x_2;
x_989 = x_3;
x_990 = x_4;
x_991 = x_5;
x_992 = x_6;
x_993 = x_7;
x_994 = x_837;
x_995 = x_9;
x_996 = x_961;
goto block_1054;
}
else
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
lean_inc(x_1);
x_1056 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_961);
x_1057 = lean_ctor_get(x_1056, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1056, 1);
lean_inc(x_1058);
if (lean_is_exclusive(x_1056)) {
 lean_ctor_release(x_1056, 0);
 lean_ctor_release(x_1056, 1);
 x_1059 = x_1056;
} else {
 lean_dec_ref(x_1056);
 x_1059 = lean_box(0);
}
x_1060 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1059)) {
 x_1061 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1061 = x_1059;
 lean_ctor_set_tag(x_1061, 7);
}
lean_ctor_set(x_1061, 0, x_1060);
lean_ctor_set(x_1061, 1, x_1057);
if (lean_is_scalar(x_962)) {
 x_1062 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1062 = x_962;
 lean_ctor_set_tag(x_1062, 7);
}
lean_ctor_set(x_1062, 0, x_1061);
lean_ctor_set(x_1062, 1, x_1060);
x_1063 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_958, x_1062, x_6, x_7, x_837, x_9, x_1058);
x_1064 = lean_ctor_get(x_1063, 1);
lean_inc(x_1064);
lean_dec(x_1063);
x_988 = x_2;
x_989 = x_3;
x_990 = x_4;
x_991 = x_5;
x_992 = x_6;
x_993 = x_7;
x_994 = x_837;
x_995 = x_9;
x_996 = x_1064;
goto block_1054;
}
block_957:
{
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; uint8_t x_857; 
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_848);
lean_dec(x_844);
lean_dec(x_841);
lean_dec(x_839);
x_854 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_855 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_854, x_845, x_838);
x_856 = lean_ctor_get(x_855, 0);
lean_inc(x_856);
x_857 = lean_unbox(x_856);
lean_dec(x_856);
if (x_857 == 0)
{
lean_object* x_858; 
x_858 = lean_ctor_get(x_855, 1);
lean_inc(x_858);
lean_dec(x_855);
x_11 = x_846;
x_12 = x_840;
x_13 = x_842;
x_14 = x_843;
x_15 = x_852;
x_16 = x_849;
x_17 = x_845;
x_18 = x_847;
x_19 = x_858;
goto block_148;
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_859 = lean_ctor_get(x_855, 1);
lean_inc(x_859);
if (lean_is_exclusive(x_855)) {
 lean_ctor_release(x_855, 0);
 lean_ctor_release(x_855, 1);
 x_860 = x_855;
} else {
 lean_dec_ref(x_855);
 x_860 = lean_box(0);
}
lean_inc(x_842);
x_861 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_842, x_843, x_859);
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
x_863 = lean_ctor_get(x_861, 1);
lean_inc(x_863);
if (lean_is_exclusive(x_861)) {
 lean_ctor_release(x_861, 0);
 lean_ctor_release(x_861, 1);
 x_864 = x_861;
} else {
 lean_dec_ref(x_861);
 x_864 = lean_box(0);
}
x_865 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_864)) {
 x_866 = lean_alloc_ctor(7, 2, 0);
} else {
 x_866 = x_864;
 lean_ctor_set_tag(x_866, 7);
}
lean_ctor_set(x_866, 0, x_865);
lean_ctor_set(x_866, 1, x_862);
if (lean_is_scalar(x_860)) {
 x_867 = lean_alloc_ctor(7, 2, 0);
} else {
 x_867 = x_860;
 lean_ctor_set_tag(x_867, 7);
}
lean_ctor_set(x_867, 0, x_866);
lean_ctor_set(x_867, 1, x_865);
x_868 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_854, x_867, x_852, x_849, x_845, x_847, x_863);
x_869 = lean_ctor_get(x_868, 1);
lean_inc(x_869);
lean_dec(x_868);
x_11 = x_846;
x_12 = x_840;
x_13 = x_842;
x_14 = x_843;
x_15 = x_852;
x_16 = x_849;
x_17 = x_845;
x_18 = x_847;
x_19 = x_869;
goto block_148;
}
}
else
{
lean_object* x_870; lean_object* x_871; 
lean_dec(x_846);
x_870 = lean_ctor_get(x_853, 0);
lean_inc(x_870);
lean_dec(x_853);
x_871 = lean_ctor_get(x_870, 1);
lean_inc(x_871);
if (lean_obj_tag(x_871) == 0)
{
lean_object* x_872; 
lean_dec(x_871);
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_848);
lean_dec(x_844);
lean_dec(x_842);
lean_dec(x_841);
lean_dec(x_840);
lean_dec(x_839);
x_872 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_870, x_843, x_852, x_849, x_845, x_847, x_838);
lean_dec(x_847);
lean_dec(x_845);
lean_dec(x_849);
lean_dec(x_852);
lean_dec(x_843);
return x_872;
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; uint8_t x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; uint8_t x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; 
x_873 = lean_ctor_get(x_870, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_871, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_871, 2);
lean_inc(x_875);
if (lean_is_exclusive(x_871)) {
 lean_ctor_release(x_871, 0);
 lean_ctor_release(x_871, 1);
 lean_ctor_release(x_871, 2);
 x_876 = x_871;
} else {
 lean_dec_ref(x_871);
 x_876 = lean_box(0);
}
x_877 = lean_int_mul(x_841, x_873);
x_878 = lean_int_mul(x_874, x_850);
x_879 = l_Lean_Meta_Grind_Arith_gcdExt(x_877, x_878);
lean_dec(x_878);
lean_dec(x_877);
x_880 = lean_ctor_get(x_879, 1);
lean_inc(x_880);
x_881 = lean_ctor_get(x_879, 0);
lean_inc(x_881);
lean_dec(x_879);
x_882 = lean_ctor_get(x_880, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_880, 1);
lean_inc(x_883);
lean_dec(x_880);
x_884 = lean_st_ref_take(x_843, x_838);
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_885, 14);
lean_inc(x_886);
x_887 = lean_ctor_get(x_886, 1);
lean_inc(x_887);
x_888 = lean_ctor_get(x_884, 1);
lean_inc(x_888);
lean_dec(x_884);
x_889 = lean_ctor_get(x_885, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_885, 1);
lean_inc(x_890);
x_891 = lean_ctor_get(x_885, 2);
lean_inc(x_891);
x_892 = lean_ctor_get(x_885, 3);
lean_inc(x_892);
x_893 = lean_ctor_get(x_885, 4);
lean_inc(x_893);
x_894 = lean_ctor_get(x_885, 5);
lean_inc(x_894);
x_895 = lean_ctor_get(x_885, 6);
lean_inc(x_895);
x_896 = lean_ctor_get(x_885, 7);
lean_inc(x_896);
x_897 = lean_ctor_get_uint8(x_885, sizeof(void*)*16);
x_898 = lean_ctor_get(x_885, 8);
lean_inc(x_898);
x_899 = lean_ctor_get(x_885, 9);
lean_inc(x_899);
x_900 = lean_ctor_get(x_885, 10);
lean_inc(x_900);
x_901 = lean_ctor_get(x_885, 11);
lean_inc(x_901);
x_902 = lean_ctor_get(x_885, 12);
lean_inc(x_902);
x_903 = lean_ctor_get(x_885, 13);
lean_inc(x_903);
x_904 = lean_ctor_get(x_885, 15);
lean_inc(x_904);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 lean_ctor_release(x_885, 1);
 lean_ctor_release(x_885, 2);
 lean_ctor_release(x_885, 3);
 lean_ctor_release(x_885, 4);
 lean_ctor_release(x_885, 5);
 lean_ctor_release(x_885, 6);
 lean_ctor_release(x_885, 7);
 lean_ctor_release(x_885, 8);
 lean_ctor_release(x_885, 9);
 lean_ctor_release(x_885, 10);
 lean_ctor_release(x_885, 11);
 lean_ctor_release(x_885, 12);
 lean_ctor_release(x_885, 13);
 lean_ctor_release(x_885, 14);
 lean_ctor_release(x_885, 15);
 x_905 = x_885;
} else {
 lean_dec_ref(x_885);
 x_905 = lean_box(0);
}
x_906 = lean_ctor_get(x_886, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_886, 2);
lean_inc(x_907);
x_908 = lean_ctor_get(x_886, 3);
lean_inc(x_908);
if (lean_is_exclusive(x_886)) {
 lean_ctor_release(x_886, 0);
 lean_ctor_release(x_886, 1);
 lean_ctor_release(x_886, 2);
 lean_ctor_release(x_886, 3);
 x_909 = x_886;
} else {
 lean_dec_ref(x_886);
 x_909 = lean_box(0);
}
x_910 = lean_ctor_get(x_887, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_887, 1);
lean_inc(x_911);
x_912 = lean_ctor_get(x_887, 2);
lean_inc(x_912);
x_913 = lean_ctor_get(x_887, 3);
lean_inc(x_913);
x_914 = lean_ctor_get(x_887, 4);
lean_inc(x_914);
x_915 = lean_ctor_get(x_887, 5);
lean_inc(x_915);
x_916 = lean_ctor_get(x_887, 6);
lean_inc(x_916);
x_917 = lean_ctor_get(x_887, 7);
lean_inc(x_917);
x_918 = lean_ctor_get(x_887, 8);
lean_inc(x_918);
x_919 = lean_ctor_get(x_887, 9);
lean_inc(x_919);
x_920 = lean_ctor_get(x_887, 10);
lean_inc(x_920);
x_921 = lean_ctor_get(x_887, 11);
lean_inc(x_921);
x_922 = lean_ctor_get(x_887, 12);
lean_inc(x_922);
x_923 = lean_ctor_get(x_887, 13);
lean_inc(x_923);
x_924 = lean_ctor_get_uint8(x_887, sizeof(void*)*17);
x_925 = lean_ctor_get(x_887, 14);
lean_inc(x_925);
x_926 = lean_ctor_get(x_887, 15);
lean_inc(x_926);
x_927 = lean_ctor_get(x_887, 16);
lean_inc(x_927);
if (lean_is_exclusive(x_887)) {
 lean_ctor_release(x_887, 0);
 lean_ctor_release(x_887, 1);
 lean_ctor_release(x_887, 2);
 lean_ctor_release(x_887, 3);
 lean_ctor_release(x_887, 4);
 lean_ctor_release(x_887, 5);
 lean_ctor_release(x_887, 6);
 lean_ctor_release(x_887, 7);
 lean_ctor_release(x_887, 8);
 lean_ctor_release(x_887, 9);
 lean_ctor_release(x_887, 10);
 lean_ctor_release(x_887, 11);
 lean_ctor_release(x_887, 12);
 lean_ctor_release(x_887, 13);
 lean_ctor_release(x_887, 14);
 lean_ctor_release(x_887, 15);
 lean_ctor_release(x_887, 16);
 x_928 = x_887;
} else {
 lean_dec_ref(x_887);
 x_928 = lean_box(0);
}
x_929 = lean_box(0);
x_930 = l_Lean_PersistentArray_set___redArg(x_915, x_840, x_929);
if (lean_is_scalar(x_928)) {
 x_931 = lean_alloc_ctor(0, 17, 1);
} else {
 x_931 = x_928;
}
lean_ctor_set(x_931, 0, x_910);
lean_ctor_set(x_931, 1, x_911);
lean_ctor_set(x_931, 2, x_912);
lean_ctor_set(x_931, 3, x_913);
lean_ctor_set(x_931, 4, x_914);
lean_ctor_set(x_931, 5, x_930);
lean_ctor_set(x_931, 6, x_916);
lean_ctor_set(x_931, 7, x_917);
lean_ctor_set(x_931, 8, x_918);
lean_ctor_set(x_931, 9, x_919);
lean_ctor_set(x_931, 10, x_920);
lean_ctor_set(x_931, 11, x_921);
lean_ctor_set(x_931, 12, x_922);
lean_ctor_set(x_931, 13, x_923);
lean_ctor_set(x_931, 14, x_925);
lean_ctor_set(x_931, 15, x_926);
lean_ctor_set(x_931, 16, x_927);
lean_ctor_set_uint8(x_931, sizeof(void*)*17, x_924);
if (lean_is_scalar(x_909)) {
 x_932 = lean_alloc_ctor(0, 4, 0);
} else {
 x_932 = x_909;
}
lean_ctor_set(x_932, 0, x_906);
lean_ctor_set(x_932, 1, x_931);
lean_ctor_set(x_932, 2, x_907);
lean_ctor_set(x_932, 3, x_908);
if (lean_is_scalar(x_905)) {
 x_933 = lean_alloc_ctor(0, 16, 1);
} else {
 x_933 = x_905;
}
lean_ctor_set(x_933, 0, x_889);
lean_ctor_set(x_933, 1, x_890);
lean_ctor_set(x_933, 2, x_891);
lean_ctor_set(x_933, 3, x_892);
lean_ctor_set(x_933, 4, x_893);
lean_ctor_set(x_933, 5, x_894);
lean_ctor_set(x_933, 6, x_895);
lean_ctor_set(x_933, 7, x_896);
lean_ctor_set(x_933, 8, x_898);
lean_ctor_set(x_933, 9, x_899);
lean_ctor_set(x_933, 10, x_900);
lean_ctor_set(x_933, 11, x_901);
lean_ctor_set(x_933, 12, x_902);
lean_ctor_set(x_933, 13, x_903);
lean_ctor_set(x_933, 14, x_932);
lean_ctor_set(x_933, 15, x_904);
lean_ctor_set_uint8(x_933, sizeof(void*)*16, x_897);
x_934 = lean_st_ref_set(x_843, x_933, x_888);
x_935 = lean_ctor_get(x_934, 1);
lean_inc(x_935);
if (lean_is_exclusive(x_934)) {
 lean_ctor_release(x_934, 0);
 lean_ctor_release(x_934, 1);
 x_936 = x_934;
} else {
 lean_dec_ref(x_934);
 x_936 = lean_box(0);
}
x_937 = lean_int_mul(x_882, x_873);
lean_dec(x_882);
lean_inc(x_848);
x_938 = l_Int_Linear_Poly_mul(x_848, x_937);
lean_dec(x_937);
x_939 = lean_int_mul(x_883, x_850);
lean_dec(x_883);
lean_inc(x_875);
x_940 = l_Int_Linear_Poly_mul(x_875, x_939);
lean_dec(x_939);
x_941 = lean_int_mul(x_850, x_873);
lean_dec(x_873);
lean_dec(x_850);
x_942 = l_Int_Linear_Poly_combine(x_938, x_940);
lean_inc(x_881);
if (lean_is_scalar(x_876)) {
 x_943 = lean_alloc_ctor(1, 3, 0);
} else {
 x_943 = x_876;
}
lean_ctor_set(x_943, 0, x_881);
lean_ctor_set(x_943, 1, x_840);
lean_ctor_set(x_943, 2, x_942);
lean_inc(x_870);
lean_inc(x_842);
if (lean_is_scalar(x_936)) {
 x_944 = lean_alloc_ctor(4, 2, 0);
} else {
 x_944 = x_936;
 lean_ctor_set_tag(x_944, 4);
}
lean_ctor_set(x_944, 0, x_842);
lean_ctor_set(x_944, 1, x_870);
x_945 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_945, 0, x_941);
lean_ctor_set(x_945, 1, x_943);
lean_ctor_set(x_945, 2, x_944);
lean_inc(x_847);
lean_inc(x_845);
lean_inc(x_849);
lean_inc(x_852);
lean_inc(x_851);
lean_inc(x_844);
lean_inc(x_839);
lean_inc(x_843);
x_946 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_945, x_843, x_839, x_844, x_851, x_852, x_849, x_845, x_847, x_935);
if (lean_obj_tag(x_946) == 0)
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; 
x_947 = lean_ctor_get(x_946, 1);
lean_inc(x_947);
if (lean_is_exclusive(x_946)) {
 lean_ctor_release(x_946, 0);
 lean_ctor_release(x_946, 1);
 x_948 = x_946;
} else {
 lean_dec_ref(x_946);
 x_948 = lean_box(0);
}
x_949 = l_Int_Linear_Poly_mul(x_848, x_874);
lean_dec(x_874);
x_950 = lean_int_neg(x_841);
lean_dec(x_841);
x_951 = l_Int_Linear_Poly_mul(x_875, x_950);
lean_dec(x_950);
x_952 = l_Int_Linear_Poly_combine(x_949, x_951);
lean_inc(x_870);
if (lean_is_scalar(x_948)) {
 x_953 = lean_alloc_ctor(5, 2, 0);
} else {
 x_953 = x_948;
 lean_ctor_set_tag(x_953, 5);
}
lean_ctor_set(x_953, 0, x_842);
lean_ctor_set(x_953, 1, x_870);
if (lean_is_exclusive(x_870)) {
 lean_ctor_release(x_870, 0);
 lean_ctor_release(x_870, 1);
 lean_ctor_release(x_870, 2);
 x_954 = x_870;
} else {
 lean_dec_ref(x_870);
 x_954 = lean_box(0);
}
if (lean_is_scalar(x_954)) {
 x_955 = lean_alloc_ctor(0, 3, 0);
} else {
 x_955 = x_954;
}
lean_ctor_set(x_955, 0, x_881);
lean_ctor_set(x_955, 1, x_952);
lean_ctor_set(x_955, 2, x_953);
x_1 = x_955;
x_2 = x_843;
x_3 = x_839;
x_4 = x_844;
x_5 = x_851;
x_6 = x_852;
x_7 = x_849;
x_8 = x_845;
x_9 = x_847;
x_10 = x_947;
goto _start;
}
else
{
lean_dec(x_881);
lean_dec(x_875);
lean_dec(x_874);
lean_dec(x_870);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_849);
lean_dec(x_848);
lean_dec(x_847);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_dec(x_842);
lean_dec(x_841);
lean_dec(x_839);
return x_946;
}
}
}
}
block_987:
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; uint8_t x_984; 
x_979 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_970, x_978);
x_980 = lean_ctor_get(x_979, 0);
lean_inc(x_980);
x_981 = lean_ctor_get(x_980, 5);
lean_inc(x_981);
lean_dec(x_980);
x_982 = lean_ctor_get(x_979, 1);
lean_inc(x_982);
lean_dec(x_979);
x_983 = lean_ctor_get(x_981, 2);
lean_inc(x_983);
x_984 = lean_nat_dec_lt(x_966, x_983);
lean_dec(x_983);
if (x_984 == 0)
{
lean_object* x_985; 
lean_dec(x_981);
x_985 = l_outOfBounds___redArg(x_963);
x_838 = x_982;
x_839 = x_971;
x_840 = x_966;
x_841 = x_967;
x_842 = x_969;
x_843 = x_970;
x_844 = x_972;
x_845 = x_976;
x_846 = x_964;
x_847 = x_977;
x_848 = x_965;
x_849 = x_975;
x_850 = x_968;
x_851 = x_973;
x_852 = x_974;
x_853 = x_985;
goto block_957;
}
else
{
lean_object* x_986; 
x_986 = l_Lean_PersistentArray_get_x21___redArg(x_963, x_981, x_966);
x_838 = x_982;
x_839 = x_971;
x_840 = x_966;
x_841 = x_967;
x_842 = x_969;
x_843 = x_970;
x_844 = x_972;
x_845 = x_976;
x_846 = x_964;
x_847 = x_977;
x_848 = x_965;
x_849 = x_975;
x_850 = x_968;
x_851 = x_973;
x_852 = x_974;
x_853 = x_986;
goto block_957;
}
}
block_1054:
{
lean_object* x_997; lean_object* x_998; 
x_997 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_994);
x_998 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_997, x_988, x_992, x_993, x_994, x_995, x_996);
if (lean_obj_tag(x_998) == 0)
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; uint8_t x_1003; 
x_999 = lean_ctor_get(x_998, 0);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_998, 1);
lean_inc(x_1000);
lean_dec(x_998);
x_1001 = lean_ctor_get(x_999, 0);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_999, 1);
lean_inc(x_1002);
lean_inc(x_1001);
x_1003 = l_Int_Linear_Poly_isUnsatDvd(x_1001, x_1002);
if (x_1003 == 0)
{
uint8_t x_1004; 
x_1004 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_999);
if (x_1004 == 0)
{
if (lean_obj_tag(x_1002) == 0)
{
lean_object* x_1005; 
lean_dec(x_1002);
lean_dec(x_1001);
lean_dec(x_991);
lean_dec(x_990);
lean_dec(x_989);
x_1005 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_999, x_988, x_992, x_993, x_994, x_995, x_1000);
lean_dec(x_995);
lean_dec(x_994);
lean_dec(x_993);
lean_dec(x_992);
lean_dec(x_988);
return x_1005;
}
else
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; uint8_t x_1013; uint8_t x_1014; uint8_t x_1015; 
x_1006 = lean_ctor_get(x_1002, 0);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_1002, 1);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_1002, 2);
lean_inc(x_1008);
lean_inc(x_999);
x_1009 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_999, x_988, x_1000);
x_1010 = lean_ctor_get(x_1009, 0);
lean_inc(x_1010);
x_1011 = lean_ctor_get(x_1009, 1);
lean_inc(x_1011);
lean_dec(x_1009);
x_1012 = lean_box(0);
x_1013 = lean_unbox(x_1010);
lean_dec(x_1010);
x_1014 = lean_unbox(x_1012);
x_1015 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_1013, x_1014);
if (x_1015 == 0)
{
x_964 = x_1002;
x_965 = x_1008;
x_966 = x_1007;
x_967 = x_1006;
x_968 = x_1001;
x_969 = x_999;
x_970 = x_988;
x_971 = x_989;
x_972 = x_990;
x_973 = x_991;
x_974 = x_992;
x_975 = x_993;
x_976 = x_994;
x_977 = x_995;
x_978 = x_1011;
goto block_987;
}
else
{
lean_object* x_1016; lean_object* x_1017; 
x_1016 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_1007, x_988, x_1011);
x_1017 = lean_ctor_get(x_1016, 1);
lean_inc(x_1017);
lean_dec(x_1016);
x_964 = x_1002;
x_965 = x_1008;
x_966 = x_1007;
x_967 = x_1006;
x_968 = x_1001;
x_969 = x_999;
x_970 = x_988;
x_971 = x_989;
x_972 = x_990;
x_973 = x_991;
x_974 = x_992;
x_975 = x_993;
x_976 = x_994;
x_977 = x_995;
x_978 = x_1017;
goto block_987;
}
}
}
else
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; uint8_t x_1021; 
lean_dec(x_1002);
lean_dec(x_1001);
lean_dec(x_991);
lean_dec(x_990);
lean_dec(x_989);
x_1018 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_1019 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1018, x_994, x_1000);
x_1020 = lean_ctor_get(x_1019, 0);
lean_inc(x_1020);
x_1021 = lean_unbox(x_1020);
lean_dec(x_1020);
if (x_1021 == 0)
{
lean_object* x_1022; 
lean_dec(x_999);
lean_dec(x_995);
lean_dec(x_994);
lean_dec(x_993);
lean_dec(x_992);
lean_dec(x_988);
x_1022 = lean_ctor_get(x_1019, 1);
lean_inc(x_1022);
lean_dec(x_1019);
x_168 = x_1022;
goto block_171;
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
x_1023 = lean_ctor_get(x_1019, 1);
lean_inc(x_1023);
if (lean_is_exclusive(x_1019)) {
 lean_ctor_release(x_1019, 0);
 lean_ctor_release(x_1019, 1);
 x_1024 = x_1019;
} else {
 lean_dec_ref(x_1019);
 x_1024 = lean_box(0);
}
x_1025 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_999, x_988, x_1023);
lean_dec(x_988);
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1025, 1);
lean_inc(x_1027);
if (lean_is_exclusive(x_1025)) {
 lean_ctor_release(x_1025, 0);
 lean_ctor_release(x_1025, 1);
 x_1028 = x_1025;
} else {
 lean_dec_ref(x_1025);
 x_1028 = lean_box(0);
}
x_1029 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1028)) {
 x_1030 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1030 = x_1028;
 lean_ctor_set_tag(x_1030, 7);
}
lean_ctor_set(x_1030, 0, x_1029);
lean_ctor_set(x_1030, 1, x_1026);
if (lean_is_scalar(x_1024)) {
 x_1031 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1031 = x_1024;
 lean_ctor_set_tag(x_1031, 7);
}
lean_ctor_set(x_1031, 0, x_1030);
lean_ctor_set(x_1031, 1, x_1029);
x_1032 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1018, x_1031, x_992, x_993, x_994, x_995, x_1027);
lean_dec(x_995);
lean_dec(x_994);
lean_dec(x_993);
lean_dec(x_992);
x_1033 = lean_ctor_get(x_1032, 1);
lean_inc(x_1033);
lean_dec(x_1032);
x_168 = x_1033;
goto block_171;
}
}
}
else
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; uint8_t x_1037; 
lean_dec(x_1002);
lean_dec(x_1001);
x_1034 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_1035 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1034, x_994, x_1000);
x_1036 = lean_ctor_get(x_1035, 0);
lean_inc(x_1036);
x_1037 = lean_unbox(x_1036);
lean_dec(x_1036);
if (x_1037 == 0)
{
lean_object* x_1038; 
x_1038 = lean_ctor_get(x_1035, 1);
lean_inc(x_1038);
lean_dec(x_1035);
x_149 = x_999;
x_150 = x_988;
x_151 = x_989;
x_152 = x_990;
x_153 = x_991;
x_154 = x_992;
x_155 = x_993;
x_156 = x_994;
x_157 = x_995;
x_158 = x_1038;
goto block_167;
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
lean_inc(x_999);
x_1041 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_999, x_988, x_1039);
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
x_1048 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1034, x_1047, x_992, x_993, x_994, x_995, x_1043);
x_1049 = lean_ctor_get(x_1048, 1);
lean_inc(x_1049);
lean_dec(x_1048);
x_149 = x_999;
x_150 = x_988;
x_151 = x_989;
x_152 = x_990;
x_153 = x_991;
x_154 = x_992;
x_155 = x_993;
x_156 = x_994;
x_157 = x_995;
x_158 = x_1049;
goto block_167;
}
}
}
else
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
lean_dec(x_995);
lean_dec(x_994);
lean_dec(x_993);
lean_dec(x_992);
lean_dec(x_991);
lean_dec(x_990);
lean_dec(x_989);
lean_dec(x_988);
x_1050 = lean_ctor_get(x_998, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_998, 1);
lean_inc(x_1051);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 x_1052 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1052 = lean_box(0);
}
if (lean_is_scalar(x_1052)) {
 x_1053 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1053 = x_1052;
}
lean_ctor_set(x_1053, 0, x_1050);
lean_ctor_set(x_1053, 1, x_1051);
return x_1053;
}
}
}
else
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
lean_dec(x_829);
lean_dec(x_827);
lean_dec(x_825);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_818);
lean_dec(x_817);
lean_dec(x_816);
lean_dec(x_815);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1065 = lean_ctor_get(x_831, 1);
lean_inc(x_1065);
if (lean_is_exclusive(x_831)) {
 lean_ctor_release(x_831, 0);
 lean_ctor_release(x_831, 1);
 x_1066 = x_831;
} else {
 lean_dec_ref(x_831);
 x_1066 = lean_box(0);
}
x_1067 = lean_box(0);
if (lean_is_scalar(x_1066)) {
 x_1068 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1068 = x_1066;
}
lean_ctor_set(x_1068, 0, x_1067);
lean_ctor_set(x_1068, 1, x_1065);
return x_1068;
}
}
else
{
lean_object* x_1069; 
lean_dec(x_829);
lean_dec(x_827);
lean_dec(x_825);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_819);
lean_dec(x_818);
lean_dec(x_817);
lean_dec(x_816);
lean_dec(x_815);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1069 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_820, x_10);
return x_1069;
}
}
block_148:
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
x_32 = lean_ctor_get(x_25, 5);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_13);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
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
x_56 = lean_ctor_get_uint8(x_25, sizeof(void*)*17);
x_57 = lean_ctor_get(x_25, 14);
x_58 = lean_ctor_get(x_25, 15);
x_59 = lean_ctor_get(x_25, 16);
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
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_13);
x_61 = l_Lean_PersistentArray_set___redArg(x_47, x_12, x_60);
lean_dec(x_12);
x_62 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_43);
lean_ctor_set(x_62, 2, x_44);
lean_ctor_set(x_62, 3, x_45);
lean_ctor_set(x_62, 4, x_46);
lean_ctor_set(x_62, 5, x_61);
lean_ctor_set(x_62, 6, x_48);
lean_ctor_set(x_62, 7, x_49);
lean_ctor_set(x_62, 8, x_50);
lean_ctor_set(x_62, 9, x_51);
lean_ctor_set(x_62, 10, x_52);
lean_ctor_set(x_62, 11, x_53);
lean_ctor_set(x_62, 12, x_54);
lean_ctor_set(x_62, 13, x_55);
lean_ctor_set(x_62, 14, x_57);
lean_ctor_set(x_62, 15, x_58);
lean_ctor_set(x_62, 16, x_59);
lean_ctor_set_uint8(x_62, sizeof(void*)*17, x_56);
lean_ctor_set(x_24, 1, x_62);
x_63 = lean_st_ref_set(x_14, x_23, x_26);
lean_dec(x_14);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_68 = lean_ctor_get(x_24, 0);
x_69 = lean_ctor_get(x_24, 2);
x_70 = lean_ctor_get(x_24, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_24);
x_71 = lean_ctor_get(x_25, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_25, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_25, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_25, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_25, 4);
lean_inc(x_75);
x_76 = lean_ctor_get(x_25, 5);
lean_inc(x_76);
x_77 = lean_ctor_get(x_25, 6);
lean_inc(x_77);
x_78 = lean_ctor_get(x_25, 7);
lean_inc(x_78);
x_79 = lean_ctor_get(x_25, 8);
lean_inc(x_79);
x_80 = lean_ctor_get(x_25, 9);
lean_inc(x_80);
x_81 = lean_ctor_get(x_25, 10);
lean_inc(x_81);
x_82 = lean_ctor_get(x_25, 11);
lean_inc(x_82);
x_83 = lean_ctor_get(x_25, 12);
lean_inc(x_83);
x_84 = lean_ctor_get(x_25, 13);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_25, sizeof(void*)*17);
x_86 = lean_ctor_get(x_25, 14);
lean_inc(x_86);
x_87 = lean_ctor_get(x_25, 15);
lean_inc(x_87);
x_88 = lean_ctor_get(x_25, 16);
lean_inc(x_88);
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
 x_89 = x_25;
} else {
 lean_dec_ref(x_25);
 x_89 = lean_box(0);
}
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_13);
x_91 = l_Lean_PersistentArray_set___redArg(x_76, x_12, x_90);
lean_dec(x_12);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(0, 17, 1);
} else {
 x_92 = x_89;
}
lean_ctor_set(x_92, 0, x_71);
lean_ctor_set(x_92, 1, x_72);
lean_ctor_set(x_92, 2, x_73);
lean_ctor_set(x_92, 3, x_74);
lean_ctor_set(x_92, 4, x_75);
lean_ctor_set(x_92, 5, x_91);
lean_ctor_set(x_92, 6, x_77);
lean_ctor_set(x_92, 7, x_78);
lean_ctor_set(x_92, 8, x_79);
lean_ctor_set(x_92, 9, x_80);
lean_ctor_set(x_92, 10, x_81);
lean_ctor_set(x_92, 11, x_82);
lean_ctor_set(x_92, 12, x_83);
lean_ctor_set(x_92, 13, x_84);
lean_ctor_set(x_92, 14, x_86);
lean_ctor_set(x_92, 15, x_87);
lean_ctor_set(x_92, 16, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*17, x_85);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_68);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_69);
lean_ctor_set(x_93, 3, x_70);
lean_ctor_set(x_23, 14, x_93);
x_94 = lean_st_ref_set(x_14, x_23, x_26);
lean_dec(x_14);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
x_97 = lean_box(0);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_99 = lean_ctor_get(x_23, 0);
x_100 = lean_ctor_get(x_23, 1);
x_101 = lean_ctor_get(x_23, 2);
x_102 = lean_ctor_get(x_23, 3);
x_103 = lean_ctor_get(x_23, 4);
x_104 = lean_ctor_get(x_23, 5);
x_105 = lean_ctor_get(x_23, 6);
x_106 = lean_ctor_get(x_23, 7);
x_107 = lean_ctor_get_uint8(x_23, sizeof(void*)*16);
x_108 = lean_ctor_get(x_23, 8);
x_109 = lean_ctor_get(x_23, 9);
x_110 = lean_ctor_get(x_23, 10);
x_111 = lean_ctor_get(x_23, 11);
x_112 = lean_ctor_get(x_23, 12);
x_113 = lean_ctor_get(x_23, 13);
x_114 = lean_ctor_get(x_23, 15);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_23);
x_115 = lean_ctor_get(x_24, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_24, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_24, 3);
lean_inc(x_117);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 x_118 = x_24;
} else {
 lean_dec_ref(x_24);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_25, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_25, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_25, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_25, 3);
lean_inc(x_122);
x_123 = lean_ctor_get(x_25, 4);
lean_inc(x_123);
x_124 = lean_ctor_get(x_25, 5);
lean_inc(x_124);
x_125 = lean_ctor_get(x_25, 6);
lean_inc(x_125);
x_126 = lean_ctor_get(x_25, 7);
lean_inc(x_126);
x_127 = lean_ctor_get(x_25, 8);
lean_inc(x_127);
x_128 = lean_ctor_get(x_25, 9);
lean_inc(x_128);
x_129 = lean_ctor_get(x_25, 10);
lean_inc(x_129);
x_130 = lean_ctor_get(x_25, 11);
lean_inc(x_130);
x_131 = lean_ctor_get(x_25, 12);
lean_inc(x_131);
x_132 = lean_ctor_get(x_25, 13);
lean_inc(x_132);
x_133 = lean_ctor_get_uint8(x_25, sizeof(void*)*17);
x_134 = lean_ctor_get(x_25, 14);
lean_inc(x_134);
x_135 = lean_ctor_get(x_25, 15);
lean_inc(x_135);
x_136 = lean_ctor_get(x_25, 16);
lean_inc(x_136);
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
 x_137 = x_25;
} else {
 lean_dec_ref(x_25);
 x_137 = lean_box(0);
}
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_13);
x_139 = l_Lean_PersistentArray_set___redArg(x_124, x_12, x_138);
lean_dec(x_12);
if (lean_is_scalar(x_137)) {
 x_140 = lean_alloc_ctor(0, 17, 1);
} else {
 x_140 = x_137;
}
lean_ctor_set(x_140, 0, x_119);
lean_ctor_set(x_140, 1, x_120);
lean_ctor_set(x_140, 2, x_121);
lean_ctor_set(x_140, 3, x_122);
lean_ctor_set(x_140, 4, x_123);
lean_ctor_set(x_140, 5, x_139);
lean_ctor_set(x_140, 6, x_125);
lean_ctor_set(x_140, 7, x_126);
lean_ctor_set(x_140, 8, x_127);
lean_ctor_set(x_140, 9, x_128);
lean_ctor_set(x_140, 10, x_129);
lean_ctor_set(x_140, 11, x_130);
lean_ctor_set(x_140, 12, x_131);
lean_ctor_set(x_140, 13, x_132);
lean_ctor_set(x_140, 14, x_134);
lean_ctor_set(x_140, 15, x_135);
lean_ctor_set(x_140, 16, x_136);
lean_ctor_set_uint8(x_140, sizeof(void*)*17, x_133);
if (lean_is_scalar(x_118)) {
 x_141 = lean_alloc_ctor(0, 4, 0);
} else {
 x_141 = x_118;
}
lean_ctor_set(x_141, 0, x_115);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_116);
lean_ctor_set(x_141, 3, x_117);
x_142 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_142, 0, x_99);
lean_ctor_set(x_142, 1, x_100);
lean_ctor_set(x_142, 2, x_101);
lean_ctor_set(x_142, 3, x_102);
lean_ctor_set(x_142, 4, x_103);
lean_ctor_set(x_142, 5, x_104);
lean_ctor_set(x_142, 6, x_105);
lean_ctor_set(x_142, 7, x_106);
lean_ctor_set(x_142, 8, x_108);
lean_ctor_set(x_142, 9, x_109);
lean_ctor_set(x_142, 10, x_110);
lean_ctor_set(x_142, 11, x_111);
lean_ctor_set(x_142, 12, x_112);
lean_ctor_set(x_142, 13, x_113);
lean_ctor_set(x_142, 14, x_141);
lean_ctor_set(x_142, 15, x_114);
lean_ctor_set_uint8(x_142, sizeof(void*)*16, x_107);
x_143 = lean_st_ref_set(x_14, x_142, x_26);
lean_dec(x_14);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
x_146 = lean_box(0);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
return x_147;
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
block_167:
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_149);
x_160 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_159, x_150, x_151, x_152, x_153, x_154, x_155, x_156, x_157, x_158);
if (lean_obj_tag(x_160) == 0)
{
uint8_t x_161; 
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_160, 0);
lean_dec(x_162);
x_163 = lean_box(0);
lean_ctor_set(x_160, 0, x_163);
return x_160;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
lean_dec(x_160);
x_165 = lean_box(0);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
return x_160;
}
}
block_171:
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
return x_170;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
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
x_26 = lean_box(0);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_getForeignVars___redArg(x_26, x_2, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_22);
x_30 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_28, x_22, x_5, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_33 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_31, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_1);
x_36 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_34);
lean_dec(x_22);
lean_dec(x_21);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
lean_inc(x_1);
x_40 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_40, 0, x_45);
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_57; uint8_t x_58; 
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_dec(x_40);
lean_inc(x_1);
x_50 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_57 = l_Lean_Expr_cleanupAnnotations(x_51);
x_58 = l_Lean_Expr_isApp(x_57);
if (x_58 == 0)
{
lean_dec(x_57);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_56;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
x_60 = l_Lean_Expr_appFnCleanup___redArg(x_57);
x_61 = l_Lean_Expr_isApp(x_60);
if (x_61 == 0)
{
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_56;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
x_63 = l_Lean_Expr_appFnCleanup___redArg(x_60);
x_64 = l_Lean_Expr_isApp(x_63);
if (x_64 == 0)
{
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_56;
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = l_Lean_Expr_appFnCleanup___redArg(x_63);
x_66 = l_Lean_Expr_isApp(x_65);
if (x_66 == 0)
{
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_56;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_Expr_appFnCleanup___redArg(x_65);
x_68 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_69 = l_Lean_Expr_isConstOf(x_67, x_68);
lean_dec(x_67);
if (x_69 == 0)
{
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_56;
}
else
{
lean_object* x_70; 
lean_dec(x_53);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_70 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_74 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_71);
x_75 = l_Lean_mkApp3(x_73, x_62, x_59, x_74);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Lean_Meta_Grind_pushNewFact(x_75, x_76, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_72);
return x_77;
}
else
{
uint8_t x_78; 
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_70);
if (x_78 == 0)
{
return x_70;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_70, 0);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_70);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
}
}
block_56:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_40);
if (x_82 == 0)
{
return x_40;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_40, 0);
x_84 = lean_ctor_get(x_40, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_40);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_36, 1);
lean_inc(x_86);
lean_dec(x_36);
x_87 = l_Int_Linear_Expr_norm(x_34);
lean_inc(x_21);
x_88 = lean_nat_to_int(x_21);
x_89 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_21);
lean_ctor_set(x_89, 2, x_22);
lean_ctor_set(x_89, 3, x_34);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_87);
lean_ctor_set(x_90, 2, x_89);
x_91 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_90, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_86);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_dec(x_34);
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
x_92 = !lean_is_exclusive(x_36);
if (x_92 == 0)
{
return x_36;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_36, 0);
x_94 = lean_ctor_get(x_36, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_36);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
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
x_96 = !lean_is_exclusive(x_33);
if (x_96 == 0)
{
return x_33;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_33, 0);
x_98 = lean_ctor_get(x_33, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_33);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_11);
if (x_100 == 0)
{
return x_11;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_11, 0);
x_102 = lean_ctor_get(x_11, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_11);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2669_(lean_object* x_1) {
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
if (builtin) {res = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2669_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

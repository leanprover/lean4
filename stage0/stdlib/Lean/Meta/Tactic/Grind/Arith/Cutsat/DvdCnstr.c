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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_171; uint8_t x_175; 
x_175 = !lean_is_exclusive(x_8);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_176 = lean_ctor_get(x_8, 0);
x_177 = lean_ctor_get(x_8, 1);
x_178 = lean_ctor_get(x_8, 2);
x_179 = lean_ctor_get(x_8, 3);
x_180 = lean_ctor_get(x_8, 4);
x_181 = lean_ctor_get(x_8, 5);
x_182 = lean_ctor_get(x_8, 6);
x_183 = lean_ctor_get(x_8, 7);
x_184 = lean_ctor_get(x_8, 8);
x_185 = lean_ctor_get(x_8, 9);
x_186 = lean_ctor_get(x_8, 10);
x_187 = lean_ctor_get(x_8, 11);
x_188 = lean_ctor_get(x_8, 12);
x_189 = lean_nat_dec_eq(x_179, x_180);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_190 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_unbox(x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_570; lean_object* x_571; uint8_t x_572; 
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_dec(x_190);
x_194 = lean_unsigned_to_nat(1u);
x_195 = lean_nat_add(x_179, x_194);
lean_dec(x_179);
lean_ctor_set(x_8, 3, x_195);
x_570 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_571 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_570, x_8, x_193);
x_572 = !lean_is_exclusive(x_571);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; uint8_t x_697; 
x_573 = lean_ctor_get(x_571, 0);
x_574 = lean_ctor_get(x_571, 1);
x_575 = lean_box(0);
x_697 = lean_unbox(x_573);
lean_dec(x_573);
if (x_697 == 0)
{
lean_free_object(x_571);
x_600 = x_2;
x_601 = x_3;
x_602 = x_4;
x_603 = x_5;
x_604 = x_6;
x_605 = x_7;
x_606 = x_8;
x_607 = x_9;
x_608 = x_574;
goto block_696;
}
else
{
lean_object* x_698; uint8_t x_699; 
lean_inc(x_1);
x_698 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_574);
x_699 = !lean_is_exclusive(x_698);
if (x_699 == 0)
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_700 = lean_ctor_get(x_698, 0);
x_701 = lean_ctor_get(x_698, 1);
x_702 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_698, 7);
lean_ctor_set(x_698, 1, x_700);
lean_ctor_set(x_698, 0, x_702);
lean_ctor_set_tag(x_571, 7);
lean_ctor_set(x_571, 1, x_702);
lean_ctor_set(x_571, 0, x_698);
x_703 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_570, x_571, x_6, x_7, x_8, x_9, x_701);
x_704 = lean_ctor_get(x_703, 1);
lean_inc(x_704);
lean_dec(x_703);
x_600 = x_2;
x_601 = x_3;
x_602 = x_4;
x_603 = x_5;
x_604 = x_6;
x_605 = x_7;
x_606 = x_8;
x_607 = x_9;
x_608 = x_704;
goto block_696;
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; 
x_705 = lean_ctor_get(x_698, 0);
x_706 = lean_ctor_get(x_698, 1);
lean_inc(x_706);
lean_inc(x_705);
lean_dec(x_698);
x_707 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_708 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_708, 0, x_707);
lean_ctor_set(x_708, 1, x_705);
lean_ctor_set_tag(x_571, 7);
lean_ctor_set(x_571, 1, x_707);
lean_ctor_set(x_571, 0, x_708);
x_709 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_570, x_571, x_6, x_7, x_8, x_9, x_706);
x_710 = lean_ctor_get(x_709, 1);
lean_inc(x_710);
lean_dec(x_709);
x_600 = x_2;
x_601 = x_3;
x_602 = x_4;
x_603 = x_5;
x_604 = x_6;
x_605 = x_7;
x_606 = x_8;
x_607 = x_9;
x_608 = x_710;
goto block_696;
}
}
block_599:
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; uint8_t x_596; 
x_591 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_582, x_590);
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_592, 5);
lean_inc(x_593);
lean_dec(x_592);
x_594 = lean_ctor_get(x_591, 1);
lean_inc(x_594);
lean_dec(x_591);
x_595 = lean_ctor_get(x_593, 2);
lean_inc(x_595);
x_596 = lean_nat_dec_lt(x_576, x_595);
lean_dec(x_595);
if (x_596 == 0)
{
lean_object* x_597; 
lean_dec(x_593);
x_597 = l_outOfBounds___redArg(x_575);
x_196 = x_588;
x_197 = x_582;
x_198 = x_578;
x_199 = x_586;
x_200 = x_579;
x_201 = x_587;
x_202 = x_581;
x_203 = x_585;
x_204 = x_584;
x_205 = x_576;
x_206 = x_577;
x_207 = x_580;
x_208 = x_583;
x_209 = x_594;
x_210 = x_589;
x_211 = x_597;
goto block_569;
}
else
{
lean_object* x_598; 
x_598 = l_Lean_PersistentArray_get_x21___redArg(x_575, x_593, x_576);
x_196 = x_588;
x_197 = x_582;
x_198 = x_578;
x_199 = x_586;
x_200 = x_579;
x_201 = x_587;
x_202 = x_581;
x_203 = x_585;
x_204 = x_584;
x_205 = x_576;
x_206 = x_577;
x_207 = x_580;
x_208 = x_583;
x_209 = x_594;
x_210 = x_589;
x_211 = x_598;
goto block_569;
}
}
block_696:
{
lean_object* x_609; lean_object* x_610; 
x_609 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_606);
x_610 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_609, x_600, x_604, x_605, x_606, x_607, x_608);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; 
x_611 = lean_ctor_get(x_610, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_610, 1);
lean_inc(x_612);
lean_dec(x_610);
x_613 = lean_ctor_get(x_611, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_611, 1);
lean_inc(x_614);
lean_inc(x_613);
x_615 = l_Int_Linear_Poly_isUnsatDvd(x_613, x_614);
if (x_615 == 0)
{
uint8_t x_616; 
x_616 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_611);
if (x_616 == 0)
{
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_617; 
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_603);
lean_dec(x_602);
lean_dec(x_601);
x_617 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_611, x_600, x_604, x_605, x_606, x_607, x_612);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_600);
return x_617;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; uint8_t x_625; uint8_t x_626; uint8_t x_627; 
x_618 = lean_ctor_get(x_614, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_614, 1);
lean_inc(x_619);
x_620 = lean_ctor_get(x_614, 2);
lean_inc(x_620);
lean_inc(x_611);
x_621 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_611, x_600, x_612);
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec(x_621);
x_624 = lean_box(0);
x_625 = lean_unbox(x_622);
lean_dec(x_622);
x_626 = lean_unbox(x_624);
x_627 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_625, x_626);
if (x_627 == 0)
{
x_576 = x_619;
x_577 = x_611;
x_578 = x_618;
x_579 = x_613;
x_580 = x_620;
x_581 = x_614;
x_582 = x_600;
x_583 = x_601;
x_584 = x_602;
x_585 = x_603;
x_586 = x_604;
x_587 = x_605;
x_588 = x_606;
x_589 = x_607;
x_590 = x_623;
goto block_599;
}
else
{
lean_object* x_628; lean_object* x_629; 
x_628 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_619, x_600, x_623);
x_629 = lean_ctor_get(x_628, 1);
lean_inc(x_629);
lean_dec(x_628);
x_576 = x_619;
x_577 = x_611;
x_578 = x_618;
x_579 = x_613;
x_580 = x_620;
x_581 = x_614;
x_582 = x_600;
x_583 = x_601;
x_584 = x_602;
x_585 = x_603;
x_586 = x_604;
x_587 = x_605;
x_588 = x_606;
x_589 = x_607;
x_590 = x_629;
goto block_599;
}
}
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; uint8_t x_633; 
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_603);
lean_dec(x_602);
lean_dec(x_601);
x_630 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_631 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_630, x_606, x_612);
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_unbox(x_632);
lean_dec(x_632);
if (x_633 == 0)
{
lean_object* x_634; 
lean_dec(x_611);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_600);
x_634 = lean_ctor_get(x_631, 1);
lean_inc(x_634);
lean_dec(x_631);
x_171 = x_634;
goto block_174;
}
else
{
uint8_t x_635; 
x_635 = !lean_is_exclusive(x_631);
if (x_635 == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; uint8_t x_639; 
x_636 = lean_ctor_get(x_631, 1);
x_637 = lean_ctor_get(x_631, 0);
lean_dec(x_637);
x_638 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_611, x_600, x_636);
lean_dec(x_600);
x_639 = !lean_is_exclusive(x_638);
if (x_639 == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_640 = lean_ctor_get(x_638, 0);
x_641 = lean_ctor_get(x_638, 1);
x_642 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_638, 7);
lean_ctor_set(x_638, 1, x_640);
lean_ctor_set(x_638, 0, x_642);
lean_ctor_set_tag(x_631, 7);
lean_ctor_set(x_631, 1, x_642);
lean_ctor_set(x_631, 0, x_638);
x_643 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_630, x_631, x_604, x_605, x_606, x_607, x_641);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
x_644 = lean_ctor_get(x_643, 1);
lean_inc(x_644);
lean_dec(x_643);
x_171 = x_644;
goto block_174;
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_645 = lean_ctor_get(x_638, 0);
x_646 = lean_ctor_get(x_638, 1);
lean_inc(x_646);
lean_inc(x_645);
lean_dec(x_638);
x_647 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_648 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_648, 0, x_647);
lean_ctor_set(x_648, 1, x_645);
lean_ctor_set_tag(x_631, 7);
lean_ctor_set(x_631, 1, x_647);
lean_ctor_set(x_631, 0, x_648);
x_649 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_630, x_631, x_604, x_605, x_606, x_607, x_646);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
x_650 = lean_ctor_get(x_649, 1);
lean_inc(x_650);
lean_dec(x_649);
x_171 = x_650;
goto block_174;
}
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_651 = lean_ctor_get(x_631, 1);
lean_inc(x_651);
lean_dec(x_631);
x_652 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_611, x_600, x_651);
lean_dec(x_600);
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_652)) {
 lean_ctor_release(x_652, 0);
 lean_ctor_release(x_652, 1);
 x_655 = x_652;
} else {
 lean_dec_ref(x_652);
 x_655 = lean_box(0);
}
x_656 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_655)) {
 x_657 = lean_alloc_ctor(7, 2, 0);
} else {
 x_657 = x_655;
 lean_ctor_set_tag(x_657, 7);
}
lean_ctor_set(x_657, 0, x_656);
lean_ctor_set(x_657, 1, x_653);
x_658 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_658, 0, x_657);
lean_ctor_set(x_658, 1, x_656);
x_659 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_630, x_658, x_604, x_605, x_606, x_607, x_654);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
x_660 = lean_ctor_get(x_659, 1);
lean_inc(x_660);
lean_dec(x_659);
x_171 = x_660;
goto block_174;
}
}
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; uint8_t x_664; 
lean_dec(x_614);
lean_dec(x_613);
x_661 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_662 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_661, x_606, x_612);
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
x_664 = lean_unbox(x_663);
lean_dec(x_663);
if (x_664 == 0)
{
lean_object* x_665; 
x_665 = lean_ctor_get(x_662, 1);
lean_inc(x_665);
lean_dec(x_662);
x_152 = x_611;
x_153 = x_600;
x_154 = x_601;
x_155 = x_602;
x_156 = x_603;
x_157 = x_604;
x_158 = x_605;
x_159 = x_606;
x_160 = x_607;
x_161 = x_665;
goto block_170;
}
else
{
uint8_t x_666; 
x_666 = !lean_is_exclusive(x_662);
if (x_666 == 0)
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; uint8_t x_670; 
x_667 = lean_ctor_get(x_662, 1);
x_668 = lean_ctor_get(x_662, 0);
lean_dec(x_668);
lean_inc(x_611);
x_669 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_611, x_600, x_667);
x_670 = !lean_is_exclusive(x_669);
if (x_670 == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_671 = lean_ctor_get(x_669, 0);
x_672 = lean_ctor_get(x_669, 1);
x_673 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_669, 7);
lean_ctor_set(x_669, 1, x_671);
lean_ctor_set(x_669, 0, x_673);
lean_ctor_set_tag(x_662, 7);
lean_ctor_set(x_662, 1, x_673);
lean_ctor_set(x_662, 0, x_669);
x_674 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_661, x_662, x_604, x_605, x_606, x_607, x_672);
x_675 = lean_ctor_get(x_674, 1);
lean_inc(x_675);
lean_dec(x_674);
x_152 = x_611;
x_153 = x_600;
x_154 = x_601;
x_155 = x_602;
x_156 = x_603;
x_157 = x_604;
x_158 = x_605;
x_159 = x_606;
x_160 = x_607;
x_161 = x_675;
goto block_170;
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_676 = lean_ctor_get(x_669, 0);
x_677 = lean_ctor_get(x_669, 1);
lean_inc(x_677);
lean_inc(x_676);
lean_dec(x_669);
x_678 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_679 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_679, 0, x_678);
lean_ctor_set(x_679, 1, x_676);
lean_ctor_set_tag(x_662, 7);
lean_ctor_set(x_662, 1, x_678);
lean_ctor_set(x_662, 0, x_679);
x_680 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_661, x_662, x_604, x_605, x_606, x_607, x_677);
x_681 = lean_ctor_get(x_680, 1);
lean_inc(x_681);
lean_dec(x_680);
x_152 = x_611;
x_153 = x_600;
x_154 = x_601;
x_155 = x_602;
x_156 = x_603;
x_157 = x_604;
x_158 = x_605;
x_159 = x_606;
x_160 = x_607;
x_161 = x_681;
goto block_170;
}
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_682 = lean_ctor_get(x_662, 1);
lean_inc(x_682);
lean_dec(x_662);
lean_inc(x_611);
x_683 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_611, x_600, x_682);
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_683, 1);
lean_inc(x_685);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 lean_ctor_release(x_683, 1);
 x_686 = x_683;
} else {
 lean_dec_ref(x_683);
 x_686 = lean_box(0);
}
x_687 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_686)) {
 x_688 = lean_alloc_ctor(7, 2, 0);
} else {
 x_688 = x_686;
 lean_ctor_set_tag(x_688, 7);
}
lean_ctor_set(x_688, 0, x_687);
lean_ctor_set(x_688, 1, x_684);
x_689 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_687);
x_690 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_661, x_689, x_604, x_605, x_606, x_607, x_685);
x_691 = lean_ctor_get(x_690, 1);
lean_inc(x_691);
lean_dec(x_690);
x_152 = x_611;
x_153 = x_600;
x_154 = x_601;
x_155 = x_602;
x_156 = x_603;
x_157 = x_604;
x_158 = x_605;
x_159 = x_606;
x_160 = x_607;
x_161 = x_691;
goto block_170;
}
}
}
}
else
{
uint8_t x_692; 
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_600);
x_692 = !lean_is_exclusive(x_610);
if (x_692 == 0)
{
return x_610;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_693 = lean_ctor_get(x_610, 0);
x_694 = lean_ctor_get(x_610, 1);
lean_inc(x_694);
lean_inc(x_693);
lean_dec(x_610);
x_695 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_695, 0, x_693);
lean_ctor_set(x_695, 1, x_694);
return x_695;
}
}
}
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; uint8_t x_805; 
x_711 = lean_ctor_get(x_571, 0);
x_712 = lean_ctor_get(x_571, 1);
lean_inc(x_712);
lean_inc(x_711);
lean_dec(x_571);
x_713 = lean_box(0);
x_805 = lean_unbox(x_711);
lean_dec(x_711);
if (x_805 == 0)
{
x_738 = x_2;
x_739 = x_3;
x_740 = x_4;
x_741 = x_5;
x_742 = x_6;
x_743 = x_7;
x_744 = x_8;
x_745 = x_9;
x_746 = x_712;
goto block_804;
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
lean_inc(x_1);
x_806 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_712);
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_806, 1);
lean_inc(x_808);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 lean_ctor_release(x_806, 1);
 x_809 = x_806;
} else {
 lean_dec_ref(x_806);
 x_809 = lean_box(0);
}
x_810 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_809)) {
 x_811 = lean_alloc_ctor(7, 2, 0);
} else {
 x_811 = x_809;
 lean_ctor_set_tag(x_811, 7);
}
lean_ctor_set(x_811, 0, x_810);
lean_ctor_set(x_811, 1, x_807);
x_812 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_812, 0, x_811);
lean_ctor_set(x_812, 1, x_810);
x_813 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_570, x_812, x_6, x_7, x_8, x_9, x_808);
x_814 = lean_ctor_get(x_813, 1);
lean_inc(x_814);
lean_dec(x_813);
x_738 = x_2;
x_739 = x_3;
x_740 = x_4;
x_741 = x_5;
x_742 = x_6;
x_743 = x_7;
x_744 = x_8;
x_745 = x_9;
x_746 = x_814;
goto block_804;
}
block_737:
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; uint8_t x_734; 
x_729 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_720, x_728);
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_730, 5);
lean_inc(x_731);
lean_dec(x_730);
x_732 = lean_ctor_get(x_729, 1);
lean_inc(x_732);
lean_dec(x_729);
x_733 = lean_ctor_get(x_731, 2);
lean_inc(x_733);
x_734 = lean_nat_dec_lt(x_714, x_733);
lean_dec(x_733);
if (x_734 == 0)
{
lean_object* x_735; 
lean_dec(x_731);
x_735 = l_outOfBounds___redArg(x_713);
x_196 = x_726;
x_197 = x_720;
x_198 = x_716;
x_199 = x_724;
x_200 = x_717;
x_201 = x_725;
x_202 = x_719;
x_203 = x_723;
x_204 = x_722;
x_205 = x_714;
x_206 = x_715;
x_207 = x_718;
x_208 = x_721;
x_209 = x_732;
x_210 = x_727;
x_211 = x_735;
goto block_569;
}
else
{
lean_object* x_736; 
x_736 = l_Lean_PersistentArray_get_x21___redArg(x_713, x_731, x_714);
x_196 = x_726;
x_197 = x_720;
x_198 = x_716;
x_199 = x_724;
x_200 = x_717;
x_201 = x_725;
x_202 = x_719;
x_203 = x_723;
x_204 = x_722;
x_205 = x_714;
x_206 = x_715;
x_207 = x_718;
x_208 = x_721;
x_209 = x_732;
x_210 = x_727;
x_211 = x_736;
goto block_569;
}
}
block_804:
{
lean_object* x_747; lean_object* x_748; 
x_747 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_744);
x_748 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_747, x_738, x_742, x_743, x_744, x_745, x_746);
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; uint8_t x_753; 
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_748, 1);
lean_inc(x_750);
lean_dec(x_748);
x_751 = lean_ctor_get(x_749, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_749, 1);
lean_inc(x_752);
lean_inc(x_751);
x_753 = l_Int_Linear_Poly_isUnsatDvd(x_751, x_752);
if (x_753 == 0)
{
uint8_t x_754; 
x_754 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_749);
if (x_754 == 0)
{
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_755; 
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_741);
lean_dec(x_740);
lean_dec(x_739);
x_755 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_749, x_738, x_742, x_743, x_744, x_745, x_750);
lean_dec(x_745);
lean_dec(x_744);
lean_dec(x_743);
lean_dec(x_742);
lean_dec(x_738);
return x_755;
}
else
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; uint8_t x_763; uint8_t x_764; uint8_t x_765; 
x_756 = lean_ctor_get(x_752, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_752, 1);
lean_inc(x_757);
x_758 = lean_ctor_get(x_752, 2);
lean_inc(x_758);
lean_inc(x_749);
x_759 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_749, x_738, x_750);
x_760 = lean_ctor_get(x_759, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_759, 1);
lean_inc(x_761);
lean_dec(x_759);
x_762 = lean_box(0);
x_763 = lean_unbox(x_760);
lean_dec(x_760);
x_764 = lean_unbox(x_762);
x_765 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_763, x_764);
if (x_765 == 0)
{
x_714 = x_757;
x_715 = x_749;
x_716 = x_756;
x_717 = x_751;
x_718 = x_758;
x_719 = x_752;
x_720 = x_738;
x_721 = x_739;
x_722 = x_740;
x_723 = x_741;
x_724 = x_742;
x_725 = x_743;
x_726 = x_744;
x_727 = x_745;
x_728 = x_761;
goto block_737;
}
else
{
lean_object* x_766; lean_object* x_767; 
x_766 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_757, x_738, x_761);
x_767 = lean_ctor_get(x_766, 1);
lean_inc(x_767);
lean_dec(x_766);
x_714 = x_757;
x_715 = x_749;
x_716 = x_756;
x_717 = x_751;
x_718 = x_758;
x_719 = x_752;
x_720 = x_738;
x_721 = x_739;
x_722 = x_740;
x_723 = x_741;
x_724 = x_742;
x_725 = x_743;
x_726 = x_744;
x_727 = x_745;
x_728 = x_767;
goto block_737;
}
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; uint8_t x_771; 
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_741);
lean_dec(x_740);
lean_dec(x_739);
x_768 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_769 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_768, x_744, x_750);
x_770 = lean_ctor_get(x_769, 0);
lean_inc(x_770);
x_771 = lean_unbox(x_770);
lean_dec(x_770);
if (x_771 == 0)
{
lean_object* x_772; 
lean_dec(x_749);
lean_dec(x_745);
lean_dec(x_744);
lean_dec(x_743);
lean_dec(x_742);
lean_dec(x_738);
x_772 = lean_ctor_get(x_769, 1);
lean_inc(x_772);
lean_dec(x_769);
x_171 = x_772;
goto block_174;
}
else
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_773 = lean_ctor_get(x_769, 1);
lean_inc(x_773);
if (lean_is_exclusive(x_769)) {
 lean_ctor_release(x_769, 0);
 lean_ctor_release(x_769, 1);
 x_774 = x_769;
} else {
 lean_dec_ref(x_769);
 x_774 = lean_box(0);
}
x_775 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_749, x_738, x_773);
lean_dec(x_738);
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_778 = x_775;
} else {
 lean_dec_ref(x_775);
 x_778 = lean_box(0);
}
x_779 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_778)) {
 x_780 = lean_alloc_ctor(7, 2, 0);
} else {
 x_780 = x_778;
 lean_ctor_set_tag(x_780, 7);
}
lean_ctor_set(x_780, 0, x_779);
lean_ctor_set(x_780, 1, x_776);
if (lean_is_scalar(x_774)) {
 x_781 = lean_alloc_ctor(7, 2, 0);
} else {
 x_781 = x_774;
 lean_ctor_set_tag(x_781, 7);
}
lean_ctor_set(x_781, 0, x_780);
lean_ctor_set(x_781, 1, x_779);
x_782 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_768, x_781, x_742, x_743, x_744, x_745, x_777);
lean_dec(x_745);
lean_dec(x_744);
lean_dec(x_743);
lean_dec(x_742);
x_783 = lean_ctor_get(x_782, 1);
lean_inc(x_783);
lean_dec(x_782);
x_171 = x_783;
goto block_174;
}
}
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; uint8_t x_787; 
lean_dec(x_752);
lean_dec(x_751);
x_784 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_785 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_784, x_744, x_750);
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
x_787 = lean_unbox(x_786);
lean_dec(x_786);
if (x_787 == 0)
{
lean_object* x_788; 
x_788 = lean_ctor_get(x_785, 1);
lean_inc(x_788);
lean_dec(x_785);
x_152 = x_749;
x_153 = x_738;
x_154 = x_739;
x_155 = x_740;
x_156 = x_741;
x_157 = x_742;
x_158 = x_743;
x_159 = x_744;
x_160 = x_745;
x_161 = x_788;
goto block_170;
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_789 = lean_ctor_get(x_785, 1);
lean_inc(x_789);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_790 = x_785;
} else {
 lean_dec_ref(x_785);
 x_790 = lean_box(0);
}
lean_inc(x_749);
x_791 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_749, x_738, x_789);
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_791, 1);
lean_inc(x_793);
if (lean_is_exclusive(x_791)) {
 lean_ctor_release(x_791, 0);
 lean_ctor_release(x_791, 1);
 x_794 = x_791;
} else {
 lean_dec_ref(x_791);
 x_794 = lean_box(0);
}
x_795 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_794)) {
 x_796 = lean_alloc_ctor(7, 2, 0);
} else {
 x_796 = x_794;
 lean_ctor_set_tag(x_796, 7);
}
lean_ctor_set(x_796, 0, x_795);
lean_ctor_set(x_796, 1, x_792);
if (lean_is_scalar(x_790)) {
 x_797 = lean_alloc_ctor(7, 2, 0);
} else {
 x_797 = x_790;
 lean_ctor_set_tag(x_797, 7);
}
lean_ctor_set(x_797, 0, x_796);
lean_ctor_set(x_797, 1, x_795);
x_798 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_784, x_797, x_742, x_743, x_744, x_745, x_793);
x_799 = lean_ctor_get(x_798, 1);
lean_inc(x_799);
lean_dec(x_798);
x_152 = x_749;
x_153 = x_738;
x_154 = x_739;
x_155 = x_740;
x_156 = x_741;
x_157 = x_742;
x_158 = x_743;
x_159 = x_744;
x_160 = x_745;
x_161 = x_799;
goto block_170;
}
}
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; 
lean_dec(x_745);
lean_dec(x_744);
lean_dec(x_743);
lean_dec(x_742);
lean_dec(x_741);
lean_dec(x_740);
lean_dec(x_739);
lean_dec(x_738);
x_800 = lean_ctor_get(x_748, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_748, 1);
lean_inc(x_801);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_802 = x_748;
} else {
 lean_dec_ref(x_748);
 x_802 = lean_box(0);
}
if (lean_is_scalar(x_802)) {
 x_803 = lean_alloc_ctor(1, 2, 0);
} else {
 x_803 = x_802;
}
lean_ctor_set(x_803, 0, x_800);
lean_ctor_set(x_803, 1, x_801);
return x_803;
}
}
}
block_569:
{
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_200);
lean_dec(x_198);
x_212 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_213 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_212, x_196, x_209);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_unbox(x_214);
lean_dec(x_214);
if (x_215 == 0)
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_213, 1);
lean_inc(x_216);
lean_dec(x_213);
x_11 = x_205;
x_12 = x_206;
x_13 = x_202;
x_14 = x_197;
x_15 = x_199;
x_16 = x_201;
x_17 = x_196;
x_18 = x_210;
x_19 = x_216;
goto block_151;
}
else
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_213);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_218 = lean_ctor_get(x_213, 1);
x_219 = lean_ctor_get(x_213, 0);
lean_dec(x_219);
lean_inc(x_206);
x_220 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_206, x_197, x_218);
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_222 = lean_ctor_get(x_220, 0);
x_223 = lean_ctor_get(x_220, 1);
x_224 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_220, 7);
lean_ctor_set(x_220, 1, x_222);
lean_ctor_set(x_220, 0, x_224);
lean_ctor_set_tag(x_213, 7);
lean_ctor_set(x_213, 1, x_224);
lean_ctor_set(x_213, 0, x_220);
x_225 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_212, x_213, x_199, x_201, x_196, x_210, x_223);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_11 = x_205;
x_12 = x_206;
x_13 = x_202;
x_14 = x_197;
x_15 = x_199;
x_16 = x_201;
x_17 = x_196;
x_18 = x_210;
x_19 = x_226;
goto block_151;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_227 = lean_ctor_get(x_220, 0);
x_228 = lean_ctor_get(x_220, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_220);
x_229 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_227);
lean_ctor_set_tag(x_213, 7);
lean_ctor_set(x_213, 1, x_229);
lean_ctor_set(x_213, 0, x_230);
x_231 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_212, x_213, x_199, x_201, x_196, x_210, x_228);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_11 = x_205;
x_12 = x_206;
x_13 = x_202;
x_14 = x_197;
x_15 = x_199;
x_16 = x_201;
x_17 = x_196;
x_18 = x_210;
x_19 = x_232;
goto block_151;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_233 = lean_ctor_get(x_213, 1);
lean_inc(x_233);
lean_dec(x_213);
lean_inc(x_206);
x_234 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_206, x_197, x_233);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_237 = x_234;
} else {
 lean_dec_ref(x_234);
 x_237 = lean_box(0);
}
x_238 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_237)) {
 x_239 = lean_alloc_ctor(7, 2, 0);
} else {
 x_239 = x_237;
 lean_ctor_set_tag(x_239, 7);
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_235);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_238);
x_241 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_212, x_240, x_199, x_201, x_196, x_210, x_236);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
x_11 = x_205;
x_12 = x_206;
x_13 = x_202;
x_14 = x_197;
x_15 = x_199;
x_16 = x_201;
x_17 = x_196;
x_18 = x_210;
x_19 = x_242;
goto block_151;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_202);
x_243 = lean_ctor_get(x_211, 0);
lean_inc(x_243);
lean_dec(x_211);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; 
lean_dec(x_244);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_200);
lean_dec(x_198);
x_245 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_243, x_197, x_199, x_201, x_196, x_210, x_209);
lean_dec(x_210);
lean_dec(x_196);
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_197);
return x_245;
}
else
{
lean_object* x_246; uint8_t x_247; 
x_246 = lean_ctor_get(x_243, 0);
lean_inc(x_246);
x_247 = !lean_is_exclusive(x_244);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_248 = lean_ctor_get(x_244, 0);
x_249 = lean_ctor_get(x_244, 2);
x_250 = lean_ctor_get(x_244, 1);
lean_dec(x_250);
x_251 = lean_int_mul(x_198, x_246);
x_252 = lean_int_mul(x_248, x_200);
x_253 = l_Lean_Meta_Grind_Arith_gcdExt(x_251, x_252);
lean_dec(x_252);
lean_dec(x_251);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 0);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_ctor_get(x_254, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_dec(x_254);
x_258 = lean_st_ref_take(x_197, x_209);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_259, 14);
lean_inc(x_260);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_258, 1);
lean_inc(x_262);
lean_dec(x_258);
x_263 = !lean_is_exclusive(x_259);
if (x_263 == 0)
{
lean_object* x_264; uint8_t x_265; 
x_264 = lean_ctor_get(x_259, 14);
lean_dec(x_264);
x_265 = !lean_is_exclusive(x_260);
if (x_265 == 0)
{
lean_object* x_266; uint8_t x_267; 
x_266 = lean_ctor_get(x_260, 1);
lean_dec(x_266);
x_267 = !lean_is_exclusive(x_261);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_268 = lean_ctor_get(x_261, 5);
x_269 = lean_box(0);
x_270 = l_Lean_PersistentArray_set___redArg(x_268, x_205, x_269);
lean_ctor_set(x_261, 5, x_270);
x_271 = lean_st_ref_set(x_197, x_259, x_262);
x_272 = !lean_is_exclusive(x_271);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_273 = lean_ctor_get(x_271, 1);
x_274 = lean_ctor_get(x_271, 0);
lean_dec(x_274);
x_275 = lean_int_mul(x_256, x_246);
lean_dec(x_256);
lean_inc(x_207);
x_276 = l_Int_Linear_Poly_mul(x_207, x_275);
lean_dec(x_275);
x_277 = lean_int_mul(x_257, x_200);
lean_dec(x_257);
lean_inc(x_249);
x_278 = l_Int_Linear_Poly_mul(x_249, x_277);
lean_dec(x_277);
x_279 = lean_int_mul(x_200, x_246);
lean_dec(x_246);
lean_dec(x_200);
x_280 = l_Int_Linear_Poly_combine(x_276, x_278);
lean_inc(x_255);
lean_ctor_set(x_244, 2, x_280);
lean_ctor_set(x_244, 1, x_205);
lean_ctor_set(x_244, 0, x_255);
lean_inc(x_243);
lean_inc(x_206);
lean_ctor_set_tag(x_271, 4);
lean_ctor_set(x_271, 1, x_243);
lean_ctor_set(x_271, 0, x_206);
x_281 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_244);
lean_ctor_set(x_281, 2, x_271);
lean_inc(x_210);
lean_inc(x_196);
lean_inc(x_201);
lean_inc(x_199);
lean_inc(x_203);
lean_inc(x_204);
lean_inc(x_208);
lean_inc(x_197);
x_282 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_281, x_197, x_208, x_204, x_203, x_199, x_201, x_196, x_210, x_273);
if (lean_obj_tag(x_282) == 0)
{
uint8_t x_283; 
x_283 = !lean_is_exclusive(x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_284 = lean_ctor_get(x_282, 1);
x_285 = lean_ctor_get(x_282, 0);
lean_dec(x_285);
x_286 = l_Int_Linear_Poly_mul(x_207, x_248);
lean_dec(x_248);
x_287 = lean_int_neg(x_198);
lean_dec(x_198);
x_288 = l_Int_Linear_Poly_mul(x_249, x_287);
lean_dec(x_287);
x_289 = l_Int_Linear_Poly_combine(x_286, x_288);
lean_inc(x_243);
lean_ctor_set_tag(x_282, 5);
lean_ctor_set(x_282, 1, x_243);
lean_ctor_set(x_282, 0, x_206);
x_290 = !lean_is_exclusive(x_243);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_243, 2);
lean_dec(x_291);
x_292 = lean_ctor_get(x_243, 1);
lean_dec(x_292);
x_293 = lean_ctor_get(x_243, 0);
lean_dec(x_293);
lean_ctor_set(x_243, 2, x_282);
lean_ctor_set(x_243, 1, x_289);
lean_ctor_set(x_243, 0, x_255);
x_1 = x_243;
x_2 = x_197;
x_3 = x_208;
x_4 = x_204;
x_5 = x_203;
x_6 = x_199;
x_7 = x_201;
x_8 = x_196;
x_9 = x_210;
x_10 = x_284;
goto _start;
}
else
{
lean_object* x_295; 
lean_dec(x_243);
x_295 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_295, 0, x_255);
lean_ctor_set(x_295, 1, x_289);
lean_ctor_set(x_295, 2, x_282);
x_1 = x_295;
x_2 = x_197;
x_3 = x_208;
x_4 = x_204;
x_5 = x_203;
x_6 = x_199;
x_7 = x_201;
x_8 = x_196;
x_9 = x_210;
x_10 = x_284;
goto _start;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_297 = lean_ctor_get(x_282, 1);
lean_inc(x_297);
lean_dec(x_282);
x_298 = l_Int_Linear_Poly_mul(x_207, x_248);
lean_dec(x_248);
x_299 = lean_int_neg(x_198);
lean_dec(x_198);
x_300 = l_Int_Linear_Poly_mul(x_249, x_299);
lean_dec(x_299);
x_301 = l_Int_Linear_Poly_combine(x_298, x_300);
lean_inc(x_243);
x_302 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_302, 0, x_206);
lean_ctor_set(x_302, 1, x_243);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 lean_ctor_release(x_243, 2);
 x_303 = x_243;
} else {
 lean_dec_ref(x_243);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(0, 3, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_255);
lean_ctor_set(x_304, 1, x_301);
lean_ctor_set(x_304, 2, x_302);
x_1 = x_304;
x_2 = x_197;
x_3 = x_208;
x_4 = x_204;
x_5 = x_203;
x_6 = x_199;
x_7 = x_201;
x_8 = x_196;
x_9 = x_210;
x_10 = x_297;
goto _start;
}
}
else
{
lean_dec(x_255);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_243);
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
return x_282;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_306 = lean_ctor_get(x_271, 1);
lean_inc(x_306);
lean_dec(x_271);
x_307 = lean_int_mul(x_256, x_246);
lean_dec(x_256);
lean_inc(x_207);
x_308 = l_Int_Linear_Poly_mul(x_207, x_307);
lean_dec(x_307);
x_309 = lean_int_mul(x_257, x_200);
lean_dec(x_257);
lean_inc(x_249);
x_310 = l_Int_Linear_Poly_mul(x_249, x_309);
lean_dec(x_309);
x_311 = lean_int_mul(x_200, x_246);
lean_dec(x_246);
lean_dec(x_200);
x_312 = l_Int_Linear_Poly_combine(x_308, x_310);
lean_inc(x_255);
lean_ctor_set(x_244, 2, x_312);
lean_ctor_set(x_244, 1, x_205);
lean_ctor_set(x_244, 0, x_255);
lean_inc(x_243);
lean_inc(x_206);
x_313 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_313, 0, x_206);
lean_ctor_set(x_313, 1, x_243);
x_314 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_244);
lean_ctor_set(x_314, 2, x_313);
lean_inc(x_210);
lean_inc(x_196);
lean_inc(x_201);
lean_inc(x_199);
lean_inc(x_203);
lean_inc(x_204);
lean_inc(x_208);
lean_inc(x_197);
x_315 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_314, x_197, x_208, x_204, x_203, x_199, x_201, x_196, x_210, x_306);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_317 = x_315;
} else {
 lean_dec_ref(x_315);
 x_317 = lean_box(0);
}
x_318 = l_Int_Linear_Poly_mul(x_207, x_248);
lean_dec(x_248);
x_319 = lean_int_neg(x_198);
lean_dec(x_198);
x_320 = l_Int_Linear_Poly_mul(x_249, x_319);
lean_dec(x_319);
x_321 = l_Int_Linear_Poly_combine(x_318, x_320);
lean_inc(x_243);
if (lean_is_scalar(x_317)) {
 x_322 = lean_alloc_ctor(5, 2, 0);
} else {
 x_322 = x_317;
 lean_ctor_set_tag(x_322, 5);
}
lean_ctor_set(x_322, 0, x_206);
lean_ctor_set(x_322, 1, x_243);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 lean_ctor_release(x_243, 2);
 x_323 = x_243;
} else {
 lean_dec_ref(x_243);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(0, 3, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_255);
lean_ctor_set(x_324, 1, x_321);
lean_ctor_set(x_324, 2, x_322);
x_1 = x_324;
x_2 = x_197;
x_3 = x_208;
x_4 = x_204;
x_5 = x_203;
x_6 = x_199;
x_7 = x_201;
x_8 = x_196;
x_9 = x_210;
x_10 = x_316;
goto _start;
}
else
{
lean_dec(x_255);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_243);
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
return x_315;
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_326 = lean_ctor_get(x_261, 0);
x_327 = lean_ctor_get(x_261, 1);
x_328 = lean_ctor_get(x_261, 2);
x_329 = lean_ctor_get(x_261, 3);
x_330 = lean_ctor_get(x_261, 4);
x_331 = lean_ctor_get(x_261, 5);
x_332 = lean_ctor_get(x_261, 6);
x_333 = lean_ctor_get(x_261, 7);
x_334 = lean_ctor_get(x_261, 8);
x_335 = lean_ctor_get(x_261, 9);
x_336 = lean_ctor_get(x_261, 10);
x_337 = lean_ctor_get(x_261, 11);
x_338 = lean_ctor_get(x_261, 12);
x_339 = lean_ctor_get(x_261, 13);
x_340 = lean_ctor_get_uint8(x_261, sizeof(void*)*18);
x_341 = lean_ctor_get(x_261, 14);
x_342 = lean_ctor_get(x_261, 15);
x_343 = lean_ctor_get(x_261, 16);
x_344 = lean_ctor_get(x_261, 17);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_inc(x_341);
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
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_261);
x_345 = lean_box(0);
x_346 = l_Lean_PersistentArray_set___redArg(x_331, x_205, x_345);
x_347 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_347, 0, x_326);
lean_ctor_set(x_347, 1, x_327);
lean_ctor_set(x_347, 2, x_328);
lean_ctor_set(x_347, 3, x_329);
lean_ctor_set(x_347, 4, x_330);
lean_ctor_set(x_347, 5, x_346);
lean_ctor_set(x_347, 6, x_332);
lean_ctor_set(x_347, 7, x_333);
lean_ctor_set(x_347, 8, x_334);
lean_ctor_set(x_347, 9, x_335);
lean_ctor_set(x_347, 10, x_336);
lean_ctor_set(x_347, 11, x_337);
lean_ctor_set(x_347, 12, x_338);
lean_ctor_set(x_347, 13, x_339);
lean_ctor_set(x_347, 14, x_341);
lean_ctor_set(x_347, 15, x_342);
lean_ctor_set(x_347, 16, x_343);
lean_ctor_set(x_347, 17, x_344);
lean_ctor_set_uint8(x_347, sizeof(void*)*18, x_340);
lean_ctor_set(x_260, 1, x_347);
x_348 = lean_st_ref_set(x_197, x_259, x_262);
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_350 = x_348;
} else {
 lean_dec_ref(x_348);
 x_350 = lean_box(0);
}
x_351 = lean_int_mul(x_256, x_246);
lean_dec(x_256);
lean_inc(x_207);
x_352 = l_Int_Linear_Poly_mul(x_207, x_351);
lean_dec(x_351);
x_353 = lean_int_mul(x_257, x_200);
lean_dec(x_257);
lean_inc(x_249);
x_354 = l_Int_Linear_Poly_mul(x_249, x_353);
lean_dec(x_353);
x_355 = lean_int_mul(x_200, x_246);
lean_dec(x_246);
lean_dec(x_200);
x_356 = l_Int_Linear_Poly_combine(x_352, x_354);
lean_inc(x_255);
lean_ctor_set(x_244, 2, x_356);
lean_ctor_set(x_244, 1, x_205);
lean_ctor_set(x_244, 0, x_255);
lean_inc(x_243);
lean_inc(x_206);
if (lean_is_scalar(x_350)) {
 x_357 = lean_alloc_ctor(4, 2, 0);
} else {
 x_357 = x_350;
 lean_ctor_set_tag(x_357, 4);
}
lean_ctor_set(x_357, 0, x_206);
lean_ctor_set(x_357, 1, x_243);
x_358 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_358, 0, x_355);
lean_ctor_set(x_358, 1, x_244);
lean_ctor_set(x_358, 2, x_357);
lean_inc(x_210);
lean_inc(x_196);
lean_inc(x_201);
lean_inc(x_199);
lean_inc(x_203);
lean_inc(x_204);
lean_inc(x_208);
lean_inc(x_197);
x_359 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_358, x_197, x_208, x_204, x_203, x_199, x_201, x_196, x_210, x_349);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_361 = x_359;
} else {
 lean_dec_ref(x_359);
 x_361 = lean_box(0);
}
x_362 = l_Int_Linear_Poly_mul(x_207, x_248);
lean_dec(x_248);
x_363 = lean_int_neg(x_198);
lean_dec(x_198);
x_364 = l_Int_Linear_Poly_mul(x_249, x_363);
lean_dec(x_363);
x_365 = l_Int_Linear_Poly_combine(x_362, x_364);
lean_inc(x_243);
if (lean_is_scalar(x_361)) {
 x_366 = lean_alloc_ctor(5, 2, 0);
} else {
 x_366 = x_361;
 lean_ctor_set_tag(x_366, 5);
}
lean_ctor_set(x_366, 0, x_206);
lean_ctor_set(x_366, 1, x_243);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 lean_ctor_release(x_243, 2);
 x_367 = x_243;
} else {
 lean_dec_ref(x_243);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(0, 3, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_255);
lean_ctor_set(x_368, 1, x_365);
lean_ctor_set(x_368, 2, x_366);
x_1 = x_368;
x_2 = x_197;
x_3 = x_208;
x_4 = x_204;
x_5 = x_203;
x_6 = x_199;
x_7 = x_201;
x_8 = x_196;
x_9 = x_210;
x_10 = x_360;
goto _start;
}
else
{
lean_dec(x_255);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_243);
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
return x_359;
}
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_370 = lean_ctor_get(x_260, 0);
x_371 = lean_ctor_get(x_260, 2);
x_372 = lean_ctor_get(x_260, 3);
lean_inc(x_372);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_260);
x_373 = lean_ctor_get(x_261, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_261, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_261, 2);
lean_inc(x_375);
x_376 = lean_ctor_get(x_261, 3);
lean_inc(x_376);
x_377 = lean_ctor_get(x_261, 4);
lean_inc(x_377);
x_378 = lean_ctor_get(x_261, 5);
lean_inc(x_378);
x_379 = lean_ctor_get(x_261, 6);
lean_inc(x_379);
x_380 = lean_ctor_get(x_261, 7);
lean_inc(x_380);
x_381 = lean_ctor_get(x_261, 8);
lean_inc(x_381);
x_382 = lean_ctor_get(x_261, 9);
lean_inc(x_382);
x_383 = lean_ctor_get(x_261, 10);
lean_inc(x_383);
x_384 = lean_ctor_get(x_261, 11);
lean_inc(x_384);
x_385 = lean_ctor_get(x_261, 12);
lean_inc(x_385);
x_386 = lean_ctor_get(x_261, 13);
lean_inc(x_386);
x_387 = lean_ctor_get_uint8(x_261, sizeof(void*)*18);
x_388 = lean_ctor_get(x_261, 14);
lean_inc(x_388);
x_389 = lean_ctor_get(x_261, 15);
lean_inc(x_389);
x_390 = lean_ctor_get(x_261, 16);
lean_inc(x_390);
x_391 = lean_ctor_get(x_261, 17);
lean_inc(x_391);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 lean_ctor_release(x_261, 4);
 lean_ctor_release(x_261, 5);
 lean_ctor_release(x_261, 6);
 lean_ctor_release(x_261, 7);
 lean_ctor_release(x_261, 8);
 lean_ctor_release(x_261, 9);
 lean_ctor_release(x_261, 10);
 lean_ctor_release(x_261, 11);
 lean_ctor_release(x_261, 12);
 lean_ctor_release(x_261, 13);
 lean_ctor_release(x_261, 14);
 lean_ctor_release(x_261, 15);
 lean_ctor_release(x_261, 16);
 lean_ctor_release(x_261, 17);
 x_392 = x_261;
} else {
 lean_dec_ref(x_261);
 x_392 = lean_box(0);
}
x_393 = lean_box(0);
x_394 = l_Lean_PersistentArray_set___redArg(x_378, x_205, x_393);
if (lean_is_scalar(x_392)) {
 x_395 = lean_alloc_ctor(0, 18, 1);
} else {
 x_395 = x_392;
}
lean_ctor_set(x_395, 0, x_373);
lean_ctor_set(x_395, 1, x_374);
lean_ctor_set(x_395, 2, x_375);
lean_ctor_set(x_395, 3, x_376);
lean_ctor_set(x_395, 4, x_377);
lean_ctor_set(x_395, 5, x_394);
lean_ctor_set(x_395, 6, x_379);
lean_ctor_set(x_395, 7, x_380);
lean_ctor_set(x_395, 8, x_381);
lean_ctor_set(x_395, 9, x_382);
lean_ctor_set(x_395, 10, x_383);
lean_ctor_set(x_395, 11, x_384);
lean_ctor_set(x_395, 12, x_385);
lean_ctor_set(x_395, 13, x_386);
lean_ctor_set(x_395, 14, x_388);
lean_ctor_set(x_395, 15, x_389);
lean_ctor_set(x_395, 16, x_390);
lean_ctor_set(x_395, 17, x_391);
lean_ctor_set_uint8(x_395, sizeof(void*)*18, x_387);
x_396 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_396, 0, x_370);
lean_ctor_set(x_396, 1, x_395);
lean_ctor_set(x_396, 2, x_371);
lean_ctor_set(x_396, 3, x_372);
lean_ctor_set(x_259, 14, x_396);
x_397 = lean_st_ref_set(x_197, x_259, x_262);
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_399 = x_397;
} else {
 lean_dec_ref(x_397);
 x_399 = lean_box(0);
}
x_400 = lean_int_mul(x_256, x_246);
lean_dec(x_256);
lean_inc(x_207);
x_401 = l_Int_Linear_Poly_mul(x_207, x_400);
lean_dec(x_400);
x_402 = lean_int_mul(x_257, x_200);
lean_dec(x_257);
lean_inc(x_249);
x_403 = l_Int_Linear_Poly_mul(x_249, x_402);
lean_dec(x_402);
x_404 = lean_int_mul(x_200, x_246);
lean_dec(x_246);
lean_dec(x_200);
x_405 = l_Int_Linear_Poly_combine(x_401, x_403);
lean_inc(x_255);
lean_ctor_set(x_244, 2, x_405);
lean_ctor_set(x_244, 1, x_205);
lean_ctor_set(x_244, 0, x_255);
lean_inc(x_243);
lean_inc(x_206);
if (lean_is_scalar(x_399)) {
 x_406 = lean_alloc_ctor(4, 2, 0);
} else {
 x_406 = x_399;
 lean_ctor_set_tag(x_406, 4);
}
lean_ctor_set(x_406, 0, x_206);
lean_ctor_set(x_406, 1, x_243);
x_407 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_407, 0, x_404);
lean_ctor_set(x_407, 1, x_244);
lean_ctor_set(x_407, 2, x_406);
lean_inc(x_210);
lean_inc(x_196);
lean_inc(x_201);
lean_inc(x_199);
lean_inc(x_203);
lean_inc(x_204);
lean_inc(x_208);
lean_inc(x_197);
x_408 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_407, x_197, x_208, x_204, x_203, x_199, x_201, x_196, x_210, x_398);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_409 = lean_ctor_get(x_408, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_410 = x_408;
} else {
 lean_dec_ref(x_408);
 x_410 = lean_box(0);
}
x_411 = l_Int_Linear_Poly_mul(x_207, x_248);
lean_dec(x_248);
x_412 = lean_int_neg(x_198);
lean_dec(x_198);
x_413 = l_Int_Linear_Poly_mul(x_249, x_412);
lean_dec(x_412);
x_414 = l_Int_Linear_Poly_combine(x_411, x_413);
lean_inc(x_243);
if (lean_is_scalar(x_410)) {
 x_415 = lean_alloc_ctor(5, 2, 0);
} else {
 x_415 = x_410;
 lean_ctor_set_tag(x_415, 5);
}
lean_ctor_set(x_415, 0, x_206);
lean_ctor_set(x_415, 1, x_243);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 lean_ctor_release(x_243, 2);
 x_416 = x_243;
} else {
 lean_dec_ref(x_243);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(0, 3, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_255);
lean_ctor_set(x_417, 1, x_414);
lean_ctor_set(x_417, 2, x_415);
x_1 = x_417;
x_2 = x_197;
x_3 = x_208;
x_4 = x_204;
x_5 = x_203;
x_6 = x_199;
x_7 = x_201;
x_8 = x_196;
x_9 = x_210;
x_10 = x_409;
goto _start;
}
else
{
lean_dec(x_255);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_243);
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
return x_408;
}
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_419 = lean_ctor_get(x_259, 0);
x_420 = lean_ctor_get(x_259, 1);
x_421 = lean_ctor_get(x_259, 2);
x_422 = lean_ctor_get(x_259, 3);
x_423 = lean_ctor_get(x_259, 4);
x_424 = lean_ctor_get(x_259, 5);
x_425 = lean_ctor_get(x_259, 6);
x_426 = lean_ctor_get(x_259, 7);
x_427 = lean_ctor_get_uint8(x_259, sizeof(void*)*16);
x_428 = lean_ctor_get(x_259, 8);
x_429 = lean_ctor_get(x_259, 9);
x_430 = lean_ctor_get(x_259, 10);
x_431 = lean_ctor_get(x_259, 11);
x_432 = lean_ctor_get(x_259, 12);
x_433 = lean_ctor_get(x_259, 13);
x_434 = lean_ctor_get(x_259, 15);
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_428);
lean_inc(x_426);
lean_inc(x_425);
lean_inc(x_424);
lean_inc(x_423);
lean_inc(x_422);
lean_inc(x_421);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_259);
x_435 = lean_ctor_get(x_260, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_260, 2);
lean_inc(x_436);
x_437 = lean_ctor_get(x_260, 3);
lean_inc(x_437);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 lean_ctor_release(x_260, 3);
 x_438 = x_260;
} else {
 lean_dec_ref(x_260);
 x_438 = lean_box(0);
}
x_439 = lean_ctor_get(x_261, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_261, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_261, 2);
lean_inc(x_441);
x_442 = lean_ctor_get(x_261, 3);
lean_inc(x_442);
x_443 = lean_ctor_get(x_261, 4);
lean_inc(x_443);
x_444 = lean_ctor_get(x_261, 5);
lean_inc(x_444);
x_445 = lean_ctor_get(x_261, 6);
lean_inc(x_445);
x_446 = lean_ctor_get(x_261, 7);
lean_inc(x_446);
x_447 = lean_ctor_get(x_261, 8);
lean_inc(x_447);
x_448 = lean_ctor_get(x_261, 9);
lean_inc(x_448);
x_449 = lean_ctor_get(x_261, 10);
lean_inc(x_449);
x_450 = lean_ctor_get(x_261, 11);
lean_inc(x_450);
x_451 = lean_ctor_get(x_261, 12);
lean_inc(x_451);
x_452 = lean_ctor_get(x_261, 13);
lean_inc(x_452);
x_453 = lean_ctor_get_uint8(x_261, sizeof(void*)*18);
x_454 = lean_ctor_get(x_261, 14);
lean_inc(x_454);
x_455 = lean_ctor_get(x_261, 15);
lean_inc(x_455);
x_456 = lean_ctor_get(x_261, 16);
lean_inc(x_456);
x_457 = lean_ctor_get(x_261, 17);
lean_inc(x_457);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 lean_ctor_release(x_261, 4);
 lean_ctor_release(x_261, 5);
 lean_ctor_release(x_261, 6);
 lean_ctor_release(x_261, 7);
 lean_ctor_release(x_261, 8);
 lean_ctor_release(x_261, 9);
 lean_ctor_release(x_261, 10);
 lean_ctor_release(x_261, 11);
 lean_ctor_release(x_261, 12);
 lean_ctor_release(x_261, 13);
 lean_ctor_release(x_261, 14);
 lean_ctor_release(x_261, 15);
 lean_ctor_release(x_261, 16);
 lean_ctor_release(x_261, 17);
 x_458 = x_261;
} else {
 lean_dec_ref(x_261);
 x_458 = lean_box(0);
}
x_459 = lean_box(0);
x_460 = l_Lean_PersistentArray_set___redArg(x_444, x_205, x_459);
if (lean_is_scalar(x_458)) {
 x_461 = lean_alloc_ctor(0, 18, 1);
} else {
 x_461 = x_458;
}
lean_ctor_set(x_461, 0, x_439);
lean_ctor_set(x_461, 1, x_440);
lean_ctor_set(x_461, 2, x_441);
lean_ctor_set(x_461, 3, x_442);
lean_ctor_set(x_461, 4, x_443);
lean_ctor_set(x_461, 5, x_460);
lean_ctor_set(x_461, 6, x_445);
lean_ctor_set(x_461, 7, x_446);
lean_ctor_set(x_461, 8, x_447);
lean_ctor_set(x_461, 9, x_448);
lean_ctor_set(x_461, 10, x_449);
lean_ctor_set(x_461, 11, x_450);
lean_ctor_set(x_461, 12, x_451);
lean_ctor_set(x_461, 13, x_452);
lean_ctor_set(x_461, 14, x_454);
lean_ctor_set(x_461, 15, x_455);
lean_ctor_set(x_461, 16, x_456);
lean_ctor_set(x_461, 17, x_457);
lean_ctor_set_uint8(x_461, sizeof(void*)*18, x_453);
if (lean_is_scalar(x_438)) {
 x_462 = lean_alloc_ctor(0, 4, 0);
} else {
 x_462 = x_438;
}
lean_ctor_set(x_462, 0, x_435);
lean_ctor_set(x_462, 1, x_461);
lean_ctor_set(x_462, 2, x_436);
lean_ctor_set(x_462, 3, x_437);
x_463 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_463, 0, x_419);
lean_ctor_set(x_463, 1, x_420);
lean_ctor_set(x_463, 2, x_421);
lean_ctor_set(x_463, 3, x_422);
lean_ctor_set(x_463, 4, x_423);
lean_ctor_set(x_463, 5, x_424);
lean_ctor_set(x_463, 6, x_425);
lean_ctor_set(x_463, 7, x_426);
lean_ctor_set(x_463, 8, x_428);
lean_ctor_set(x_463, 9, x_429);
lean_ctor_set(x_463, 10, x_430);
lean_ctor_set(x_463, 11, x_431);
lean_ctor_set(x_463, 12, x_432);
lean_ctor_set(x_463, 13, x_433);
lean_ctor_set(x_463, 14, x_462);
lean_ctor_set(x_463, 15, x_434);
lean_ctor_set_uint8(x_463, sizeof(void*)*16, x_427);
x_464 = lean_st_ref_set(x_197, x_463, x_262);
x_465 = lean_ctor_get(x_464, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_466 = x_464;
} else {
 lean_dec_ref(x_464);
 x_466 = lean_box(0);
}
x_467 = lean_int_mul(x_256, x_246);
lean_dec(x_256);
lean_inc(x_207);
x_468 = l_Int_Linear_Poly_mul(x_207, x_467);
lean_dec(x_467);
x_469 = lean_int_mul(x_257, x_200);
lean_dec(x_257);
lean_inc(x_249);
x_470 = l_Int_Linear_Poly_mul(x_249, x_469);
lean_dec(x_469);
x_471 = lean_int_mul(x_200, x_246);
lean_dec(x_246);
lean_dec(x_200);
x_472 = l_Int_Linear_Poly_combine(x_468, x_470);
lean_inc(x_255);
lean_ctor_set(x_244, 2, x_472);
lean_ctor_set(x_244, 1, x_205);
lean_ctor_set(x_244, 0, x_255);
lean_inc(x_243);
lean_inc(x_206);
if (lean_is_scalar(x_466)) {
 x_473 = lean_alloc_ctor(4, 2, 0);
} else {
 x_473 = x_466;
 lean_ctor_set_tag(x_473, 4);
}
lean_ctor_set(x_473, 0, x_206);
lean_ctor_set(x_473, 1, x_243);
x_474 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_244);
lean_ctor_set(x_474, 2, x_473);
lean_inc(x_210);
lean_inc(x_196);
lean_inc(x_201);
lean_inc(x_199);
lean_inc(x_203);
lean_inc(x_204);
lean_inc(x_208);
lean_inc(x_197);
x_475 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_474, x_197, x_208, x_204, x_203, x_199, x_201, x_196, x_210, x_465);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_476 = lean_ctor_get(x_475, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 x_477 = x_475;
} else {
 lean_dec_ref(x_475);
 x_477 = lean_box(0);
}
x_478 = l_Int_Linear_Poly_mul(x_207, x_248);
lean_dec(x_248);
x_479 = lean_int_neg(x_198);
lean_dec(x_198);
x_480 = l_Int_Linear_Poly_mul(x_249, x_479);
lean_dec(x_479);
x_481 = l_Int_Linear_Poly_combine(x_478, x_480);
lean_inc(x_243);
if (lean_is_scalar(x_477)) {
 x_482 = lean_alloc_ctor(5, 2, 0);
} else {
 x_482 = x_477;
 lean_ctor_set_tag(x_482, 5);
}
lean_ctor_set(x_482, 0, x_206);
lean_ctor_set(x_482, 1, x_243);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 lean_ctor_release(x_243, 2);
 x_483 = x_243;
} else {
 lean_dec_ref(x_243);
 x_483 = lean_box(0);
}
if (lean_is_scalar(x_483)) {
 x_484 = lean_alloc_ctor(0, 3, 0);
} else {
 x_484 = x_483;
}
lean_ctor_set(x_484, 0, x_255);
lean_ctor_set(x_484, 1, x_481);
lean_ctor_set(x_484, 2, x_482);
x_1 = x_484;
x_2 = x_197;
x_3 = x_208;
x_4 = x_204;
x_5 = x_203;
x_6 = x_199;
x_7 = x_201;
x_8 = x_196;
x_9 = x_210;
x_10 = x_476;
goto _start;
}
else
{
lean_dec(x_255);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_243);
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
return x_475;
}
}
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; uint8_t x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_486 = lean_ctor_get(x_244, 0);
x_487 = lean_ctor_get(x_244, 2);
lean_inc(x_487);
lean_inc(x_486);
lean_dec(x_244);
x_488 = lean_int_mul(x_198, x_246);
x_489 = lean_int_mul(x_486, x_200);
x_490 = l_Lean_Meta_Grind_Arith_gcdExt(x_488, x_489);
lean_dec(x_489);
lean_dec(x_488);
x_491 = lean_ctor_get(x_490, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 0);
lean_inc(x_492);
lean_dec(x_490);
x_493 = lean_ctor_get(x_491, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_491, 1);
lean_inc(x_494);
lean_dec(x_491);
x_495 = lean_st_ref_take(x_197, x_209);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_496, 14);
lean_inc(x_497);
x_498 = lean_ctor_get(x_497, 1);
lean_inc(x_498);
x_499 = lean_ctor_get(x_495, 1);
lean_inc(x_499);
lean_dec(x_495);
x_500 = lean_ctor_get(x_496, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_496, 1);
lean_inc(x_501);
x_502 = lean_ctor_get(x_496, 2);
lean_inc(x_502);
x_503 = lean_ctor_get(x_496, 3);
lean_inc(x_503);
x_504 = lean_ctor_get(x_496, 4);
lean_inc(x_504);
x_505 = lean_ctor_get(x_496, 5);
lean_inc(x_505);
x_506 = lean_ctor_get(x_496, 6);
lean_inc(x_506);
x_507 = lean_ctor_get(x_496, 7);
lean_inc(x_507);
x_508 = lean_ctor_get_uint8(x_496, sizeof(void*)*16);
x_509 = lean_ctor_get(x_496, 8);
lean_inc(x_509);
x_510 = lean_ctor_get(x_496, 9);
lean_inc(x_510);
x_511 = lean_ctor_get(x_496, 10);
lean_inc(x_511);
x_512 = lean_ctor_get(x_496, 11);
lean_inc(x_512);
x_513 = lean_ctor_get(x_496, 12);
lean_inc(x_513);
x_514 = lean_ctor_get(x_496, 13);
lean_inc(x_514);
x_515 = lean_ctor_get(x_496, 15);
lean_inc(x_515);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 lean_ctor_release(x_496, 2);
 lean_ctor_release(x_496, 3);
 lean_ctor_release(x_496, 4);
 lean_ctor_release(x_496, 5);
 lean_ctor_release(x_496, 6);
 lean_ctor_release(x_496, 7);
 lean_ctor_release(x_496, 8);
 lean_ctor_release(x_496, 9);
 lean_ctor_release(x_496, 10);
 lean_ctor_release(x_496, 11);
 lean_ctor_release(x_496, 12);
 lean_ctor_release(x_496, 13);
 lean_ctor_release(x_496, 14);
 lean_ctor_release(x_496, 15);
 x_516 = x_496;
} else {
 lean_dec_ref(x_496);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_497, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_497, 2);
lean_inc(x_518);
x_519 = lean_ctor_get(x_497, 3);
lean_inc(x_519);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 lean_ctor_release(x_497, 2);
 lean_ctor_release(x_497, 3);
 x_520 = x_497;
} else {
 lean_dec_ref(x_497);
 x_520 = lean_box(0);
}
x_521 = lean_ctor_get(x_498, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_498, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_498, 2);
lean_inc(x_523);
x_524 = lean_ctor_get(x_498, 3);
lean_inc(x_524);
x_525 = lean_ctor_get(x_498, 4);
lean_inc(x_525);
x_526 = lean_ctor_get(x_498, 5);
lean_inc(x_526);
x_527 = lean_ctor_get(x_498, 6);
lean_inc(x_527);
x_528 = lean_ctor_get(x_498, 7);
lean_inc(x_528);
x_529 = lean_ctor_get(x_498, 8);
lean_inc(x_529);
x_530 = lean_ctor_get(x_498, 9);
lean_inc(x_530);
x_531 = lean_ctor_get(x_498, 10);
lean_inc(x_531);
x_532 = lean_ctor_get(x_498, 11);
lean_inc(x_532);
x_533 = lean_ctor_get(x_498, 12);
lean_inc(x_533);
x_534 = lean_ctor_get(x_498, 13);
lean_inc(x_534);
x_535 = lean_ctor_get_uint8(x_498, sizeof(void*)*18);
x_536 = lean_ctor_get(x_498, 14);
lean_inc(x_536);
x_537 = lean_ctor_get(x_498, 15);
lean_inc(x_537);
x_538 = lean_ctor_get(x_498, 16);
lean_inc(x_538);
x_539 = lean_ctor_get(x_498, 17);
lean_inc(x_539);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 lean_ctor_release(x_498, 2);
 lean_ctor_release(x_498, 3);
 lean_ctor_release(x_498, 4);
 lean_ctor_release(x_498, 5);
 lean_ctor_release(x_498, 6);
 lean_ctor_release(x_498, 7);
 lean_ctor_release(x_498, 8);
 lean_ctor_release(x_498, 9);
 lean_ctor_release(x_498, 10);
 lean_ctor_release(x_498, 11);
 lean_ctor_release(x_498, 12);
 lean_ctor_release(x_498, 13);
 lean_ctor_release(x_498, 14);
 lean_ctor_release(x_498, 15);
 lean_ctor_release(x_498, 16);
 lean_ctor_release(x_498, 17);
 x_540 = x_498;
} else {
 lean_dec_ref(x_498);
 x_540 = lean_box(0);
}
x_541 = lean_box(0);
x_542 = l_Lean_PersistentArray_set___redArg(x_526, x_205, x_541);
if (lean_is_scalar(x_540)) {
 x_543 = lean_alloc_ctor(0, 18, 1);
} else {
 x_543 = x_540;
}
lean_ctor_set(x_543, 0, x_521);
lean_ctor_set(x_543, 1, x_522);
lean_ctor_set(x_543, 2, x_523);
lean_ctor_set(x_543, 3, x_524);
lean_ctor_set(x_543, 4, x_525);
lean_ctor_set(x_543, 5, x_542);
lean_ctor_set(x_543, 6, x_527);
lean_ctor_set(x_543, 7, x_528);
lean_ctor_set(x_543, 8, x_529);
lean_ctor_set(x_543, 9, x_530);
lean_ctor_set(x_543, 10, x_531);
lean_ctor_set(x_543, 11, x_532);
lean_ctor_set(x_543, 12, x_533);
lean_ctor_set(x_543, 13, x_534);
lean_ctor_set(x_543, 14, x_536);
lean_ctor_set(x_543, 15, x_537);
lean_ctor_set(x_543, 16, x_538);
lean_ctor_set(x_543, 17, x_539);
lean_ctor_set_uint8(x_543, sizeof(void*)*18, x_535);
if (lean_is_scalar(x_520)) {
 x_544 = lean_alloc_ctor(0, 4, 0);
} else {
 x_544 = x_520;
}
lean_ctor_set(x_544, 0, x_517);
lean_ctor_set(x_544, 1, x_543);
lean_ctor_set(x_544, 2, x_518);
lean_ctor_set(x_544, 3, x_519);
if (lean_is_scalar(x_516)) {
 x_545 = lean_alloc_ctor(0, 16, 1);
} else {
 x_545 = x_516;
}
lean_ctor_set(x_545, 0, x_500);
lean_ctor_set(x_545, 1, x_501);
lean_ctor_set(x_545, 2, x_502);
lean_ctor_set(x_545, 3, x_503);
lean_ctor_set(x_545, 4, x_504);
lean_ctor_set(x_545, 5, x_505);
lean_ctor_set(x_545, 6, x_506);
lean_ctor_set(x_545, 7, x_507);
lean_ctor_set(x_545, 8, x_509);
lean_ctor_set(x_545, 9, x_510);
lean_ctor_set(x_545, 10, x_511);
lean_ctor_set(x_545, 11, x_512);
lean_ctor_set(x_545, 12, x_513);
lean_ctor_set(x_545, 13, x_514);
lean_ctor_set(x_545, 14, x_544);
lean_ctor_set(x_545, 15, x_515);
lean_ctor_set_uint8(x_545, sizeof(void*)*16, x_508);
x_546 = lean_st_ref_set(x_197, x_545, x_499);
x_547 = lean_ctor_get(x_546, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_546)) {
 lean_ctor_release(x_546, 0);
 lean_ctor_release(x_546, 1);
 x_548 = x_546;
} else {
 lean_dec_ref(x_546);
 x_548 = lean_box(0);
}
x_549 = lean_int_mul(x_493, x_246);
lean_dec(x_493);
lean_inc(x_207);
x_550 = l_Int_Linear_Poly_mul(x_207, x_549);
lean_dec(x_549);
x_551 = lean_int_mul(x_494, x_200);
lean_dec(x_494);
lean_inc(x_487);
x_552 = l_Int_Linear_Poly_mul(x_487, x_551);
lean_dec(x_551);
x_553 = lean_int_mul(x_200, x_246);
lean_dec(x_246);
lean_dec(x_200);
x_554 = l_Int_Linear_Poly_combine(x_550, x_552);
lean_inc(x_492);
x_555 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_555, 0, x_492);
lean_ctor_set(x_555, 1, x_205);
lean_ctor_set(x_555, 2, x_554);
lean_inc(x_243);
lean_inc(x_206);
if (lean_is_scalar(x_548)) {
 x_556 = lean_alloc_ctor(4, 2, 0);
} else {
 x_556 = x_548;
 lean_ctor_set_tag(x_556, 4);
}
lean_ctor_set(x_556, 0, x_206);
lean_ctor_set(x_556, 1, x_243);
x_557 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_557, 0, x_553);
lean_ctor_set(x_557, 1, x_555);
lean_ctor_set(x_557, 2, x_556);
lean_inc(x_210);
lean_inc(x_196);
lean_inc(x_201);
lean_inc(x_199);
lean_inc(x_203);
lean_inc(x_204);
lean_inc(x_208);
lean_inc(x_197);
x_558 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_557, x_197, x_208, x_204, x_203, x_199, x_201, x_196, x_210, x_547);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_559 = lean_ctor_get(x_558, 1);
lean_inc(x_559);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 x_560 = x_558;
} else {
 lean_dec_ref(x_558);
 x_560 = lean_box(0);
}
x_561 = l_Int_Linear_Poly_mul(x_207, x_486);
lean_dec(x_486);
x_562 = lean_int_neg(x_198);
lean_dec(x_198);
x_563 = l_Int_Linear_Poly_mul(x_487, x_562);
lean_dec(x_562);
x_564 = l_Int_Linear_Poly_combine(x_561, x_563);
lean_inc(x_243);
if (lean_is_scalar(x_560)) {
 x_565 = lean_alloc_ctor(5, 2, 0);
} else {
 x_565 = x_560;
 lean_ctor_set_tag(x_565, 5);
}
lean_ctor_set(x_565, 0, x_206);
lean_ctor_set(x_565, 1, x_243);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 lean_ctor_release(x_243, 2);
 x_566 = x_243;
} else {
 lean_dec_ref(x_243);
 x_566 = lean_box(0);
}
if (lean_is_scalar(x_566)) {
 x_567 = lean_alloc_ctor(0, 3, 0);
} else {
 x_567 = x_566;
}
lean_ctor_set(x_567, 0, x_492);
lean_ctor_set(x_567, 1, x_564);
lean_ctor_set(x_567, 2, x_565);
x_1 = x_567;
x_2 = x_197;
x_3 = x_208;
x_4 = x_204;
x_5 = x_203;
x_6 = x_199;
x_7 = x_201;
x_8 = x_196;
x_9 = x_210;
x_10 = x_559;
goto _start;
}
else
{
lean_dec(x_492);
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_243);
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
return x_558;
}
}
}
}
}
}
else
{
uint8_t x_815; 
lean_free_object(x_8);
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
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_815 = !lean_is_exclusive(x_190);
if (x_815 == 0)
{
lean_object* x_816; lean_object* x_817; 
x_816 = lean_ctor_get(x_190, 0);
lean_dec(x_816);
x_817 = lean_box(0);
lean_ctor_set(x_190, 0, x_817);
return x_190;
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_818 = lean_ctor_get(x_190, 1);
lean_inc(x_818);
lean_dec(x_190);
x_819 = lean_box(0);
x_820 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_820, 0, x_819);
lean_ctor_set(x_820, 1, x_818);
return x_820;
}
}
}
else
{
lean_object* x_821; 
lean_free_object(x_8);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_821 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_181, x_10);
return x_821;
}
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; uint8_t x_833; lean_object* x_834; uint8_t x_835; lean_object* x_836; uint8_t x_837; 
x_822 = lean_ctor_get(x_8, 0);
x_823 = lean_ctor_get(x_8, 1);
x_824 = lean_ctor_get(x_8, 2);
x_825 = lean_ctor_get(x_8, 3);
x_826 = lean_ctor_get(x_8, 4);
x_827 = lean_ctor_get(x_8, 5);
x_828 = lean_ctor_get(x_8, 6);
x_829 = lean_ctor_get(x_8, 7);
x_830 = lean_ctor_get(x_8, 8);
x_831 = lean_ctor_get(x_8, 9);
x_832 = lean_ctor_get(x_8, 10);
x_833 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_834 = lean_ctor_get(x_8, 11);
x_835 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_836 = lean_ctor_get(x_8, 12);
lean_inc(x_836);
lean_inc(x_834);
lean_inc(x_832);
lean_inc(x_831);
lean_inc(x_830);
lean_inc(x_829);
lean_inc(x_828);
lean_inc(x_827);
lean_inc(x_826);
lean_inc(x_825);
lean_inc(x_824);
lean_inc(x_823);
lean_inc(x_822);
lean_dec(x_8);
x_837 = lean_nat_dec_eq(x_825, x_826);
if (x_837 == 0)
{
lean_object* x_838; lean_object* x_839; uint8_t x_840; 
x_838 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_839 = lean_ctor_get(x_838, 0);
lean_inc(x_839);
x_840 = lean_unbox(x_839);
lean_dec(x_839);
if (x_840 == 0)
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; uint8_t x_1063; 
x_841 = lean_ctor_get(x_838, 1);
lean_inc(x_841);
lean_dec(x_838);
x_842 = lean_unsigned_to_nat(1u);
x_843 = lean_nat_add(x_825, x_842);
lean_dec(x_825);
x_844 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_844, 0, x_822);
lean_ctor_set(x_844, 1, x_823);
lean_ctor_set(x_844, 2, x_824);
lean_ctor_set(x_844, 3, x_843);
lean_ctor_set(x_844, 4, x_826);
lean_ctor_set(x_844, 5, x_827);
lean_ctor_set(x_844, 6, x_828);
lean_ctor_set(x_844, 7, x_829);
lean_ctor_set(x_844, 8, x_830);
lean_ctor_set(x_844, 9, x_831);
lean_ctor_set(x_844, 10, x_832);
lean_ctor_set(x_844, 11, x_834);
lean_ctor_set(x_844, 12, x_836);
lean_ctor_set_uint8(x_844, sizeof(void*)*13, x_833);
lean_ctor_set_uint8(x_844, sizeof(void*)*13 + 1, x_835);
x_966 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_967 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_966, x_844, x_841);
x_968 = lean_ctor_get(x_967, 0);
lean_inc(x_968);
x_969 = lean_ctor_get(x_967, 1);
lean_inc(x_969);
if (lean_is_exclusive(x_967)) {
 lean_ctor_release(x_967, 0);
 lean_ctor_release(x_967, 1);
 x_970 = x_967;
} else {
 lean_dec_ref(x_967);
 x_970 = lean_box(0);
}
x_971 = lean_box(0);
x_1063 = lean_unbox(x_968);
lean_dec(x_968);
if (x_1063 == 0)
{
lean_dec(x_970);
x_996 = x_2;
x_997 = x_3;
x_998 = x_4;
x_999 = x_5;
x_1000 = x_6;
x_1001 = x_7;
x_1002 = x_844;
x_1003 = x_9;
x_1004 = x_969;
goto block_1062;
}
else
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
lean_inc(x_1);
x_1064 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_969);
x_1065 = lean_ctor_get(x_1064, 0);
lean_inc(x_1065);
x_1066 = lean_ctor_get(x_1064, 1);
lean_inc(x_1066);
if (lean_is_exclusive(x_1064)) {
 lean_ctor_release(x_1064, 0);
 lean_ctor_release(x_1064, 1);
 x_1067 = x_1064;
} else {
 lean_dec_ref(x_1064);
 x_1067 = lean_box(0);
}
x_1068 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1067)) {
 x_1069 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1069 = x_1067;
 lean_ctor_set_tag(x_1069, 7);
}
lean_ctor_set(x_1069, 0, x_1068);
lean_ctor_set(x_1069, 1, x_1065);
if (lean_is_scalar(x_970)) {
 x_1070 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1070 = x_970;
 lean_ctor_set_tag(x_1070, 7);
}
lean_ctor_set(x_1070, 0, x_1069);
lean_ctor_set(x_1070, 1, x_1068);
x_1071 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_966, x_1070, x_6, x_7, x_844, x_9, x_1066);
x_1072 = lean_ctor_get(x_1071, 1);
lean_inc(x_1072);
lean_dec(x_1071);
x_996 = x_2;
x_997 = x_3;
x_998 = x_4;
x_999 = x_5;
x_1000 = x_6;
x_1001 = x_7;
x_1002 = x_844;
x_1003 = x_9;
x_1004 = x_1072;
goto block_1062;
}
block_965:
{
if (lean_obj_tag(x_860) == 0)
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; uint8_t x_864; 
lean_dec(x_857);
lean_dec(x_856);
lean_dec(x_853);
lean_dec(x_852);
lean_dec(x_849);
lean_dec(x_847);
x_861 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_862 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_861, x_845, x_858);
x_863 = lean_ctor_get(x_862, 0);
lean_inc(x_863);
x_864 = lean_unbox(x_863);
lean_dec(x_863);
if (x_864 == 0)
{
lean_object* x_865; 
x_865 = lean_ctor_get(x_862, 1);
lean_inc(x_865);
lean_dec(x_862);
x_11 = x_854;
x_12 = x_855;
x_13 = x_851;
x_14 = x_846;
x_15 = x_848;
x_16 = x_850;
x_17 = x_845;
x_18 = x_859;
x_19 = x_865;
goto block_151;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
x_866 = lean_ctor_get(x_862, 1);
lean_inc(x_866);
if (lean_is_exclusive(x_862)) {
 lean_ctor_release(x_862, 0);
 lean_ctor_release(x_862, 1);
 x_867 = x_862;
} else {
 lean_dec_ref(x_862);
 x_867 = lean_box(0);
}
lean_inc(x_855);
x_868 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_855, x_846, x_866);
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_868, 1);
lean_inc(x_870);
if (lean_is_exclusive(x_868)) {
 lean_ctor_release(x_868, 0);
 lean_ctor_release(x_868, 1);
 x_871 = x_868;
} else {
 lean_dec_ref(x_868);
 x_871 = lean_box(0);
}
x_872 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_871)) {
 x_873 = lean_alloc_ctor(7, 2, 0);
} else {
 x_873 = x_871;
 lean_ctor_set_tag(x_873, 7);
}
lean_ctor_set(x_873, 0, x_872);
lean_ctor_set(x_873, 1, x_869);
if (lean_is_scalar(x_867)) {
 x_874 = lean_alloc_ctor(7, 2, 0);
} else {
 x_874 = x_867;
 lean_ctor_set_tag(x_874, 7);
}
lean_ctor_set(x_874, 0, x_873);
lean_ctor_set(x_874, 1, x_872);
x_875 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_861, x_874, x_848, x_850, x_845, x_859, x_870);
x_876 = lean_ctor_get(x_875, 1);
lean_inc(x_876);
lean_dec(x_875);
x_11 = x_854;
x_12 = x_855;
x_13 = x_851;
x_14 = x_846;
x_15 = x_848;
x_16 = x_850;
x_17 = x_845;
x_18 = x_859;
x_19 = x_876;
goto block_151;
}
}
else
{
lean_object* x_877; lean_object* x_878; 
lean_dec(x_851);
x_877 = lean_ctor_get(x_860, 0);
lean_inc(x_877);
lean_dec(x_860);
x_878 = lean_ctor_get(x_877, 1);
lean_inc(x_878);
if (lean_obj_tag(x_878) == 0)
{
lean_object* x_879; 
lean_dec(x_878);
lean_dec(x_857);
lean_dec(x_856);
lean_dec(x_855);
lean_dec(x_854);
lean_dec(x_853);
lean_dec(x_852);
lean_dec(x_849);
lean_dec(x_847);
x_879 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_877, x_846, x_848, x_850, x_845, x_859, x_858);
lean_dec(x_859);
lean_dec(x_845);
lean_dec(x_850);
lean_dec(x_848);
lean_dec(x_846);
return x_879;
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; uint8_t x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; uint8_t x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
x_880 = lean_ctor_get(x_877, 0);
lean_inc(x_880);
x_881 = lean_ctor_get(x_878, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_878, 2);
lean_inc(x_882);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 lean_ctor_release(x_878, 2);
 x_883 = x_878;
} else {
 lean_dec_ref(x_878);
 x_883 = lean_box(0);
}
x_884 = lean_int_mul(x_847, x_880);
x_885 = lean_int_mul(x_881, x_849);
x_886 = l_Lean_Meta_Grind_Arith_gcdExt(x_884, x_885);
lean_dec(x_885);
lean_dec(x_884);
x_887 = lean_ctor_get(x_886, 1);
lean_inc(x_887);
x_888 = lean_ctor_get(x_886, 0);
lean_inc(x_888);
lean_dec(x_886);
x_889 = lean_ctor_get(x_887, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_887, 1);
lean_inc(x_890);
lean_dec(x_887);
x_891 = lean_st_ref_take(x_846, x_858);
x_892 = lean_ctor_get(x_891, 0);
lean_inc(x_892);
x_893 = lean_ctor_get(x_892, 14);
lean_inc(x_893);
x_894 = lean_ctor_get(x_893, 1);
lean_inc(x_894);
x_895 = lean_ctor_get(x_891, 1);
lean_inc(x_895);
lean_dec(x_891);
x_896 = lean_ctor_get(x_892, 0);
lean_inc(x_896);
x_897 = lean_ctor_get(x_892, 1);
lean_inc(x_897);
x_898 = lean_ctor_get(x_892, 2);
lean_inc(x_898);
x_899 = lean_ctor_get(x_892, 3);
lean_inc(x_899);
x_900 = lean_ctor_get(x_892, 4);
lean_inc(x_900);
x_901 = lean_ctor_get(x_892, 5);
lean_inc(x_901);
x_902 = lean_ctor_get(x_892, 6);
lean_inc(x_902);
x_903 = lean_ctor_get(x_892, 7);
lean_inc(x_903);
x_904 = lean_ctor_get_uint8(x_892, sizeof(void*)*16);
x_905 = lean_ctor_get(x_892, 8);
lean_inc(x_905);
x_906 = lean_ctor_get(x_892, 9);
lean_inc(x_906);
x_907 = lean_ctor_get(x_892, 10);
lean_inc(x_907);
x_908 = lean_ctor_get(x_892, 11);
lean_inc(x_908);
x_909 = lean_ctor_get(x_892, 12);
lean_inc(x_909);
x_910 = lean_ctor_get(x_892, 13);
lean_inc(x_910);
x_911 = lean_ctor_get(x_892, 15);
lean_inc(x_911);
if (lean_is_exclusive(x_892)) {
 lean_ctor_release(x_892, 0);
 lean_ctor_release(x_892, 1);
 lean_ctor_release(x_892, 2);
 lean_ctor_release(x_892, 3);
 lean_ctor_release(x_892, 4);
 lean_ctor_release(x_892, 5);
 lean_ctor_release(x_892, 6);
 lean_ctor_release(x_892, 7);
 lean_ctor_release(x_892, 8);
 lean_ctor_release(x_892, 9);
 lean_ctor_release(x_892, 10);
 lean_ctor_release(x_892, 11);
 lean_ctor_release(x_892, 12);
 lean_ctor_release(x_892, 13);
 lean_ctor_release(x_892, 14);
 lean_ctor_release(x_892, 15);
 x_912 = x_892;
} else {
 lean_dec_ref(x_892);
 x_912 = lean_box(0);
}
x_913 = lean_ctor_get(x_893, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_893, 2);
lean_inc(x_914);
x_915 = lean_ctor_get(x_893, 3);
lean_inc(x_915);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 lean_ctor_release(x_893, 2);
 lean_ctor_release(x_893, 3);
 x_916 = x_893;
} else {
 lean_dec_ref(x_893);
 x_916 = lean_box(0);
}
x_917 = lean_ctor_get(x_894, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_894, 1);
lean_inc(x_918);
x_919 = lean_ctor_get(x_894, 2);
lean_inc(x_919);
x_920 = lean_ctor_get(x_894, 3);
lean_inc(x_920);
x_921 = lean_ctor_get(x_894, 4);
lean_inc(x_921);
x_922 = lean_ctor_get(x_894, 5);
lean_inc(x_922);
x_923 = lean_ctor_get(x_894, 6);
lean_inc(x_923);
x_924 = lean_ctor_get(x_894, 7);
lean_inc(x_924);
x_925 = lean_ctor_get(x_894, 8);
lean_inc(x_925);
x_926 = lean_ctor_get(x_894, 9);
lean_inc(x_926);
x_927 = lean_ctor_get(x_894, 10);
lean_inc(x_927);
x_928 = lean_ctor_get(x_894, 11);
lean_inc(x_928);
x_929 = lean_ctor_get(x_894, 12);
lean_inc(x_929);
x_930 = lean_ctor_get(x_894, 13);
lean_inc(x_930);
x_931 = lean_ctor_get_uint8(x_894, sizeof(void*)*18);
x_932 = lean_ctor_get(x_894, 14);
lean_inc(x_932);
x_933 = lean_ctor_get(x_894, 15);
lean_inc(x_933);
x_934 = lean_ctor_get(x_894, 16);
lean_inc(x_934);
x_935 = lean_ctor_get(x_894, 17);
lean_inc(x_935);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 lean_ctor_release(x_894, 1);
 lean_ctor_release(x_894, 2);
 lean_ctor_release(x_894, 3);
 lean_ctor_release(x_894, 4);
 lean_ctor_release(x_894, 5);
 lean_ctor_release(x_894, 6);
 lean_ctor_release(x_894, 7);
 lean_ctor_release(x_894, 8);
 lean_ctor_release(x_894, 9);
 lean_ctor_release(x_894, 10);
 lean_ctor_release(x_894, 11);
 lean_ctor_release(x_894, 12);
 lean_ctor_release(x_894, 13);
 lean_ctor_release(x_894, 14);
 lean_ctor_release(x_894, 15);
 lean_ctor_release(x_894, 16);
 lean_ctor_release(x_894, 17);
 x_936 = x_894;
} else {
 lean_dec_ref(x_894);
 x_936 = lean_box(0);
}
x_937 = lean_box(0);
x_938 = l_Lean_PersistentArray_set___redArg(x_922, x_854, x_937);
if (lean_is_scalar(x_936)) {
 x_939 = lean_alloc_ctor(0, 18, 1);
} else {
 x_939 = x_936;
}
lean_ctor_set(x_939, 0, x_917);
lean_ctor_set(x_939, 1, x_918);
lean_ctor_set(x_939, 2, x_919);
lean_ctor_set(x_939, 3, x_920);
lean_ctor_set(x_939, 4, x_921);
lean_ctor_set(x_939, 5, x_938);
lean_ctor_set(x_939, 6, x_923);
lean_ctor_set(x_939, 7, x_924);
lean_ctor_set(x_939, 8, x_925);
lean_ctor_set(x_939, 9, x_926);
lean_ctor_set(x_939, 10, x_927);
lean_ctor_set(x_939, 11, x_928);
lean_ctor_set(x_939, 12, x_929);
lean_ctor_set(x_939, 13, x_930);
lean_ctor_set(x_939, 14, x_932);
lean_ctor_set(x_939, 15, x_933);
lean_ctor_set(x_939, 16, x_934);
lean_ctor_set(x_939, 17, x_935);
lean_ctor_set_uint8(x_939, sizeof(void*)*18, x_931);
if (lean_is_scalar(x_916)) {
 x_940 = lean_alloc_ctor(0, 4, 0);
} else {
 x_940 = x_916;
}
lean_ctor_set(x_940, 0, x_913);
lean_ctor_set(x_940, 1, x_939);
lean_ctor_set(x_940, 2, x_914);
lean_ctor_set(x_940, 3, x_915);
if (lean_is_scalar(x_912)) {
 x_941 = lean_alloc_ctor(0, 16, 1);
} else {
 x_941 = x_912;
}
lean_ctor_set(x_941, 0, x_896);
lean_ctor_set(x_941, 1, x_897);
lean_ctor_set(x_941, 2, x_898);
lean_ctor_set(x_941, 3, x_899);
lean_ctor_set(x_941, 4, x_900);
lean_ctor_set(x_941, 5, x_901);
lean_ctor_set(x_941, 6, x_902);
lean_ctor_set(x_941, 7, x_903);
lean_ctor_set(x_941, 8, x_905);
lean_ctor_set(x_941, 9, x_906);
lean_ctor_set(x_941, 10, x_907);
lean_ctor_set(x_941, 11, x_908);
lean_ctor_set(x_941, 12, x_909);
lean_ctor_set(x_941, 13, x_910);
lean_ctor_set(x_941, 14, x_940);
lean_ctor_set(x_941, 15, x_911);
lean_ctor_set_uint8(x_941, sizeof(void*)*16, x_904);
x_942 = lean_st_ref_set(x_846, x_941, x_895);
x_943 = lean_ctor_get(x_942, 1);
lean_inc(x_943);
if (lean_is_exclusive(x_942)) {
 lean_ctor_release(x_942, 0);
 lean_ctor_release(x_942, 1);
 x_944 = x_942;
} else {
 lean_dec_ref(x_942);
 x_944 = lean_box(0);
}
x_945 = lean_int_mul(x_889, x_880);
lean_dec(x_889);
lean_inc(x_856);
x_946 = l_Int_Linear_Poly_mul(x_856, x_945);
lean_dec(x_945);
x_947 = lean_int_mul(x_890, x_849);
lean_dec(x_890);
lean_inc(x_882);
x_948 = l_Int_Linear_Poly_mul(x_882, x_947);
lean_dec(x_947);
x_949 = lean_int_mul(x_849, x_880);
lean_dec(x_880);
lean_dec(x_849);
x_950 = l_Int_Linear_Poly_combine(x_946, x_948);
lean_inc(x_888);
if (lean_is_scalar(x_883)) {
 x_951 = lean_alloc_ctor(1, 3, 0);
} else {
 x_951 = x_883;
}
lean_ctor_set(x_951, 0, x_888);
lean_ctor_set(x_951, 1, x_854);
lean_ctor_set(x_951, 2, x_950);
lean_inc(x_877);
lean_inc(x_855);
if (lean_is_scalar(x_944)) {
 x_952 = lean_alloc_ctor(4, 2, 0);
} else {
 x_952 = x_944;
 lean_ctor_set_tag(x_952, 4);
}
lean_ctor_set(x_952, 0, x_855);
lean_ctor_set(x_952, 1, x_877);
x_953 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_953, 0, x_949);
lean_ctor_set(x_953, 1, x_951);
lean_ctor_set(x_953, 2, x_952);
lean_inc(x_859);
lean_inc(x_845);
lean_inc(x_850);
lean_inc(x_848);
lean_inc(x_852);
lean_inc(x_853);
lean_inc(x_857);
lean_inc(x_846);
x_954 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_953, x_846, x_857, x_853, x_852, x_848, x_850, x_845, x_859, x_943);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; 
x_955 = lean_ctor_get(x_954, 1);
lean_inc(x_955);
if (lean_is_exclusive(x_954)) {
 lean_ctor_release(x_954, 0);
 lean_ctor_release(x_954, 1);
 x_956 = x_954;
} else {
 lean_dec_ref(x_954);
 x_956 = lean_box(0);
}
x_957 = l_Int_Linear_Poly_mul(x_856, x_881);
lean_dec(x_881);
x_958 = lean_int_neg(x_847);
lean_dec(x_847);
x_959 = l_Int_Linear_Poly_mul(x_882, x_958);
lean_dec(x_958);
x_960 = l_Int_Linear_Poly_combine(x_957, x_959);
lean_inc(x_877);
if (lean_is_scalar(x_956)) {
 x_961 = lean_alloc_ctor(5, 2, 0);
} else {
 x_961 = x_956;
 lean_ctor_set_tag(x_961, 5);
}
lean_ctor_set(x_961, 0, x_855);
lean_ctor_set(x_961, 1, x_877);
if (lean_is_exclusive(x_877)) {
 lean_ctor_release(x_877, 0);
 lean_ctor_release(x_877, 1);
 lean_ctor_release(x_877, 2);
 x_962 = x_877;
} else {
 lean_dec_ref(x_877);
 x_962 = lean_box(0);
}
if (lean_is_scalar(x_962)) {
 x_963 = lean_alloc_ctor(0, 3, 0);
} else {
 x_963 = x_962;
}
lean_ctor_set(x_963, 0, x_888);
lean_ctor_set(x_963, 1, x_960);
lean_ctor_set(x_963, 2, x_961);
x_1 = x_963;
x_2 = x_846;
x_3 = x_857;
x_4 = x_853;
x_5 = x_852;
x_6 = x_848;
x_7 = x_850;
x_8 = x_845;
x_9 = x_859;
x_10 = x_955;
goto _start;
}
else
{
lean_dec(x_888);
lean_dec(x_882);
lean_dec(x_881);
lean_dec(x_877);
lean_dec(x_859);
lean_dec(x_857);
lean_dec(x_856);
lean_dec(x_855);
lean_dec(x_853);
lean_dec(x_852);
lean_dec(x_850);
lean_dec(x_848);
lean_dec(x_847);
lean_dec(x_846);
lean_dec(x_845);
return x_954;
}
}
}
}
block_995:
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; uint8_t x_992; 
x_987 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_978, x_986);
x_988 = lean_ctor_get(x_987, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_988, 5);
lean_inc(x_989);
lean_dec(x_988);
x_990 = lean_ctor_get(x_987, 1);
lean_inc(x_990);
lean_dec(x_987);
x_991 = lean_ctor_get(x_989, 2);
lean_inc(x_991);
x_992 = lean_nat_dec_lt(x_972, x_991);
lean_dec(x_991);
if (x_992 == 0)
{
lean_object* x_993; 
lean_dec(x_989);
x_993 = l_outOfBounds___redArg(x_971);
x_845 = x_984;
x_846 = x_978;
x_847 = x_974;
x_848 = x_982;
x_849 = x_975;
x_850 = x_983;
x_851 = x_977;
x_852 = x_981;
x_853 = x_980;
x_854 = x_972;
x_855 = x_973;
x_856 = x_976;
x_857 = x_979;
x_858 = x_990;
x_859 = x_985;
x_860 = x_993;
goto block_965;
}
else
{
lean_object* x_994; 
x_994 = l_Lean_PersistentArray_get_x21___redArg(x_971, x_989, x_972);
x_845 = x_984;
x_846 = x_978;
x_847 = x_974;
x_848 = x_982;
x_849 = x_975;
x_850 = x_983;
x_851 = x_977;
x_852 = x_981;
x_853 = x_980;
x_854 = x_972;
x_855 = x_973;
x_856 = x_976;
x_857 = x_979;
x_858 = x_990;
x_859 = x_985;
x_860 = x_994;
goto block_965;
}
}
block_1062:
{
lean_object* x_1005; lean_object* x_1006; 
x_1005 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_1002);
x_1006 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___redArg(x_1005, x_996, x_1000, x_1001, x_1002, x_1003, x_1004);
if (lean_obj_tag(x_1006) == 0)
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; uint8_t x_1011; 
x_1007 = lean_ctor_get(x_1006, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_1006, 1);
lean_inc(x_1008);
lean_dec(x_1006);
x_1009 = lean_ctor_get(x_1007, 0);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_1007, 1);
lean_inc(x_1010);
lean_inc(x_1009);
x_1011 = l_Int_Linear_Poly_isUnsatDvd(x_1009, x_1010);
if (x_1011 == 0)
{
uint8_t x_1012; 
x_1012 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_1007);
if (x_1012 == 0)
{
if (lean_obj_tag(x_1010) == 0)
{
lean_object* x_1013; 
lean_dec(x_1010);
lean_dec(x_1009);
lean_dec(x_999);
lean_dec(x_998);
lean_dec(x_997);
x_1013 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_1007, x_996, x_1000, x_1001, x_1002, x_1003, x_1008);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1001);
lean_dec(x_1000);
lean_dec(x_996);
return x_1013;
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; uint8_t x_1021; uint8_t x_1022; uint8_t x_1023; 
x_1014 = lean_ctor_get(x_1010, 0);
lean_inc(x_1014);
x_1015 = lean_ctor_get(x_1010, 1);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_1010, 2);
lean_inc(x_1016);
lean_inc(x_1007);
x_1017 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_1007, x_996, x_1008);
x_1018 = lean_ctor_get(x_1017, 0);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_1017, 1);
lean_inc(x_1019);
lean_dec(x_1017);
x_1020 = lean_box(0);
x_1021 = lean_unbox(x_1018);
lean_dec(x_1018);
x_1022 = lean_unbox(x_1020);
x_1023 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_1021, x_1022);
if (x_1023 == 0)
{
x_972 = x_1015;
x_973 = x_1007;
x_974 = x_1014;
x_975 = x_1009;
x_976 = x_1016;
x_977 = x_1010;
x_978 = x_996;
x_979 = x_997;
x_980 = x_998;
x_981 = x_999;
x_982 = x_1000;
x_983 = x_1001;
x_984 = x_1002;
x_985 = x_1003;
x_986 = x_1019;
goto block_995;
}
else
{
lean_object* x_1024; lean_object* x_1025; 
x_1024 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_1015, x_996, x_1019);
x_1025 = lean_ctor_get(x_1024, 1);
lean_inc(x_1025);
lean_dec(x_1024);
x_972 = x_1015;
x_973 = x_1007;
x_974 = x_1014;
x_975 = x_1009;
x_976 = x_1016;
x_977 = x_1010;
x_978 = x_996;
x_979 = x_997;
x_980 = x_998;
x_981 = x_999;
x_982 = x_1000;
x_983 = x_1001;
x_984 = x_1002;
x_985 = x_1003;
x_986 = x_1025;
goto block_995;
}
}
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; uint8_t x_1029; 
lean_dec(x_1010);
lean_dec(x_1009);
lean_dec(x_999);
lean_dec(x_998);
lean_dec(x_997);
x_1026 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_1027 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1026, x_1002, x_1008);
x_1028 = lean_ctor_get(x_1027, 0);
lean_inc(x_1028);
x_1029 = lean_unbox(x_1028);
lean_dec(x_1028);
if (x_1029 == 0)
{
lean_object* x_1030; 
lean_dec(x_1007);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1001);
lean_dec(x_1000);
lean_dec(x_996);
x_1030 = lean_ctor_get(x_1027, 1);
lean_inc(x_1030);
lean_dec(x_1027);
x_171 = x_1030;
goto block_174;
}
else
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1031 = lean_ctor_get(x_1027, 1);
lean_inc(x_1031);
if (lean_is_exclusive(x_1027)) {
 lean_ctor_release(x_1027, 0);
 lean_ctor_release(x_1027, 1);
 x_1032 = x_1027;
} else {
 lean_dec_ref(x_1027);
 x_1032 = lean_box(0);
}
x_1033 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1007, x_996, x_1031);
lean_dec(x_996);
x_1034 = lean_ctor_get(x_1033, 0);
lean_inc(x_1034);
x_1035 = lean_ctor_get(x_1033, 1);
lean_inc(x_1035);
if (lean_is_exclusive(x_1033)) {
 lean_ctor_release(x_1033, 0);
 lean_ctor_release(x_1033, 1);
 x_1036 = x_1033;
} else {
 lean_dec_ref(x_1033);
 x_1036 = lean_box(0);
}
x_1037 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1036)) {
 x_1038 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1038 = x_1036;
 lean_ctor_set_tag(x_1038, 7);
}
lean_ctor_set(x_1038, 0, x_1037);
lean_ctor_set(x_1038, 1, x_1034);
if (lean_is_scalar(x_1032)) {
 x_1039 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1039 = x_1032;
 lean_ctor_set_tag(x_1039, 7);
}
lean_ctor_set(x_1039, 0, x_1038);
lean_ctor_set(x_1039, 1, x_1037);
x_1040 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1026, x_1039, x_1000, x_1001, x_1002, x_1003, x_1035);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1001);
lean_dec(x_1000);
x_1041 = lean_ctor_get(x_1040, 1);
lean_inc(x_1041);
lean_dec(x_1040);
x_171 = x_1041;
goto block_174;
}
}
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; uint8_t x_1045; 
lean_dec(x_1010);
lean_dec(x_1009);
x_1042 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_1043 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1042, x_1002, x_1008);
x_1044 = lean_ctor_get(x_1043, 0);
lean_inc(x_1044);
x_1045 = lean_unbox(x_1044);
lean_dec(x_1044);
if (x_1045 == 0)
{
lean_object* x_1046; 
x_1046 = lean_ctor_get(x_1043, 1);
lean_inc(x_1046);
lean_dec(x_1043);
x_152 = x_1007;
x_153 = x_996;
x_154 = x_997;
x_155 = x_998;
x_156 = x_999;
x_157 = x_1000;
x_158 = x_1001;
x_159 = x_1002;
x_160 = x_1003;
x_161 = x_1046;
goto block_170;
}
else
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; 
x_1047 = lean_ctor_get(x_1043, 1);
lean_inc(x_1047);
if (lean_is_exclusive(x_1043)) {
 lean_ctor_release(x_1043, 0);
 lean_ctor_release(x_1043, 1);
 x_1048 = x_1043;
} else {
 lean_dec_ref(x_1043);
 x_1048 = lean_box(0);
}
lean_inc(x_1007);
x_1049 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1007, x_996, x_1047);
x_1050 = lean_ctor_get(x_1049, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1049, 1);
lean_inc(x_1051);
if (lean_is_exclusive(x_1049)) {
 lean_ctor_release(x_1049, 0);
 lean_ctor_release(x_1049, 1);
 x_1052 = x_1049;
} else {
 lean_dec_ref(x_1049);
 x_1052 = lean_box(0);
}
x_1053 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1052)) {
 x_1054 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1054 = x_1052;
 lean_ctor_set_tag(x_1054, 7);
}
lean_ctor_set(x_1054, 0, x_1053);
lean_ctor_set(x_1054, 1, x_1050);
if (lean_is_scalar(x_1048)) {
 x_1055 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1055 = x_1048;
 lean_ctor_set_tag(x_1055, 7);
}
lean_ctor_set(x_1055, 0, x_1054);
lean_ctor_set(x_1055, 1, x_1053);
x_1056 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1042, x_1055, x_1000, x_1001, x_1002, x_1003, x_1051);
x_1057 = lean_ctor_get(x_1056, 1);
lean_inc(x_1057);
lean_dec(x_1056);
x_152 = x_1007;
x_153 = x_996;
x_154 = x_997;
x_155 = x_998;
x_156 = x_999;
x_157 = x_1000;
x_158 = x_1001;
x_159 = x_1002;
x_160 = x_1003;
x_161 = x_1057;
goto block_170;
}
}
}
else
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; 
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1001);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_998);
lean_dec(x_997);
lean_dec(x_996);
x_1058 = lean_ctor_get(x_1006, 0);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1006, 1);
lean_inc(x_1059);
if (lean_is_exclusive(x_1006)) {
 lean_ctor_release(x_1006, 0);
 lean_ctor_release(x_1006, 1);
 x_1060 = x_1006;
} else {
 lean_dec_ref(x_1006);
 x_1060 = lean_box(0);
}
if (lean_is_scalar(x_1060)) {
 x_1061 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1061 = x_1060;
}
lean_ctor_set(x_1061, 0, x_1058);
lean_ctor_set(x_1061, 1, x_1059);
return x_1061;
}
}
}
else
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
lean_dec(x_836);
lean_dec(x_834);
lean_dec(x_832);
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_828);
lean_dec(x_827);
lean_dec(x_826);
lean_dec(x_825);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1073 = lean_ctor_get(x_838, 1);
lean_inc(x_1073);
if (lean_is_exclusive(x_838)) {
 lean_ctor_release(x_838, 0);
 lean_ctor_release(x_838, 1);
 x_1074 = x_838;
} else {
 lean_dec_ref(x_838);
 x_1074 = lean_box(0);
}
x_1075 = lean_box(0);
if (lean_is_scalar(x_1074)) {
 x_1076 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1076 = x_1074;
}
lean_ctor_set(x_1076, 0, x_1075);
lean_ctor_set(x_1076, 1, x_1073);
return x_1076;
}
}
else
{
lean_object* x_1077; 
lean_dec(x_836);
lean_dec(x_834);
lean_dec(x_832);
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_828);
lean_dec(x_826);
lean_dec(x_825);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1077 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_827, x_10);
return x_1077;
}
}
block_151:
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
lean_ctor_set(x_33, 0, x_12);
x_34 = l_Lean_PersistentArray_set___redArg(x_32, x_11, x_33);
lean_dec(x_11);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
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
x_56 = lean_ctor_get_uint8(x_25, sizeof(void*)*18);
x_57 = lean_ctor_get(x_25, 14);
x_58 = lean_ctor_get(x_25, 15);
x_59 = lean_ctor_get(x_25, 16);
x_60 = lean_ctor_get(x_25, 17);
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
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_12);
x_62 = l_Lean_PersistentArray_set___redArg(x_47, x_11, x_61);
lean_dec(x_11);
x_63 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_63, 0, x_42);
lean_ctor_set(x_63, 1, x_43);
lean_ctor_set(x_63, 2, x_44);
lean_ctor_set(x_63, 3, x_45);
lean_ctor_set(x_63, 4, x_46);
lean_ctor_set(x_63, 5, x_62);
lean_ctor_set(x_63, 6, x_48);
lean_ctor_set(x_63, 7, x_49);
lean_ctor_set(x_63, 8, x_50);
lean_ctor_set(x_63, 9, x_51);
lean_ctor_set(x_63, 10, x_52);
lean_ctor_set(x_63, 11, x_53);
lean_ctor_set(x_63, 12, x_54);
lean_ctor_set(x_63, 13, x_55);
lean_ctor_set(x_63, 14, x_57);
lean_ctor_set(x_63, 15, x_58);
lean_ctor_set(x_63, 16, x_59);
lean_ctor_set(x_63, 17, x_60);
lean_ctor_set_uint8(x_63, sizeof(void*)*18, x_56);
lean_ctor_set(x_24, 1, x_63);
x_64 = lean_st_ref_set(x_14, x_23, x_26);
lean_dec(x_14);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_69 = lean_ctor_get(x_24, 0);
x_70 = lean_ctor_get(x_24, 2);
x_71 = lean_ctor_get(x_24, 3);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_24);
x_72 = lean_ctor_get(x_25, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_25, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_25, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_25, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_25, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_25, 5);
lean_inc(x_77);
x_78 = lean_ctor_get(x_25, 6);
lean_inc(x_78);
x_79 = lean_ctor_get(x_25, 7);
lean_inc(x_79);
x_80 = lean_ctor_get(x_25, 8);
lean_inc(x_80);
x_81 = lean_ctor_get(x_25, 9);
lean_inc(x_81);
x_82 = lean_ctor_get(x_25, 10);
lean_inc(x_82);
x_83 = lean_ctor_get(x_25, 11);
lean_inc(x_83);
x_84 = lean_ctor_get(x_25, 12);
lean_inc(x_84);
x_85 = lean_ctor_get(x_25, 13);
lean_inc(x_85);
x_86 = lean_ctor_get_uint8(x_25, sizeof(void*)*18);
x_87 = lean_ctor_get(x_25, 14);
lean_inc(x_87);
x_88 = lean_ctor_get(x_25, 15);
lean_inc(x_88);
x_89 = lean_ctor_get(x_25, 16);
lean_inc(x_89);
x_90 = lean_ctor_get(x_25, 17);
lean_inc(x_90);
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
 x_91 = x_25;
} else {
 lean_dec_ref(x_25);
 x_91 = lean_box(0);
}
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_12);
x_93 = l_Lean_PersistentArray_set___redArg(x_77, x_11, x_92);
lean_dec(x_11);
if (lean_is_scalar(x_91)) {
 x_94 = lean_alloc_ctor(0, 18, 1);
} else {
 x_94 = x_91;
}
lean_ctor_set(x_94, 0, x_72);
lean_ctor_set(x_94, 1, x_73);
lean_ctor_set(x_94, 2, x_74);
lean_ctor_set(x_94, 3, x_75);
lean_ctor_set(x_94, 4, x_76);
lean_ctor_set(x_94, 5, x_93);
lean_ctor_set(x_94, 6, x_78);
lean_ctor_set(x_94, 7, x_79);
lean_ctor_set(x_94, 8, x_80);
lean_ctor_set(x_94, 9, x_81);
lean_ctor_set(x_94, 10, x_82);
lean_ctor_set(x_94, 11, x_83);
lean_ctor_set(x_94, 12, x_84);
lean_ctor_set(x_94, 13, x_85);
lean_ctor_set(x_94, 14, x_87);
lean_ctor_set(x_94, 15, x_88);
lean_ctor_set(x_94, 16, x_89);
lean_ctor_set(x_94, 17, x_90);
lean_ctor_set_uint8(x_94, sizeof(void*)*18, x_86);
x_95 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_95, 0, x_69);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_70);
lean_ctor_set(x_95, 3, x_71);
lean_ctor_set(x_23, 14, x_95);
x_96 = lean_st_ref_set(x_14, x_23, x_26);
lean_dec(x_14);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
x_99 = lean_box(0);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_101 = lean_ctor_get(x_23, 0);
x_102 = lean_ctor_get(x_23, 1);
x_103 = lean_ctor_get(x_23, 2);
x_104 = lean_ctor_get(x_23, 3);
x_105 = lean_ctor_get(x_23, 4);
x_106 = lean_ctor_get(x_23, 5);
x_107 = lean_ctor_get(x_23, 6);
x_108 = lean_ctor_get(x_23, 7);
x_109 = lean_ctor_get_uint8(x_23, sizeof(void*)*16);
x_110 = lean_ctor_get(x_23, 8);
x_111 = lean_ctor_get(x_23, 9);
x_112 = lean_ctor_get(x_23, 10);
x_113 = lean_ctor_get(x_23, 11);
x_114 = lean_ctor_get(x_23, 12);
x_115 = lean_ctor_get(x_23, 13);
x_116 = lean_ctor_get(x_23, 15);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_23);
x_117 = lean_ctor_get(x_24, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_24, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_24, 3);
lean_inc(x_119);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 x_120 = x_24;
} else {
 lean_dec_ref(x_24);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_25, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_25, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_25, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_25, 3);
lean_inc(x_124);
x_125 = lean_ctor_get(x_25, 4);
lean_inc(x_125);
x_126 = lean_ctor_get(x_25, 5);
lean_inc(x_126);
x_127 = lean_ctor_get(x_25, 6);
lean_inc(x_127);
x_128 = lean_ctor_get(x_25, 7);
lean_inc(x_128);
x_129 = lean_ctor_get(x_25, 8);
lean_inc(x_129);
x_130 = lean_ctor_get(x_25, 9);
lean_inc(x_130);
x_131 = lean_ctor_get(x_25, 10);
lean_inc(x_131);
x_132 = lean_ctor_get(x_25, 11);
lean_inc(x_132);
x_133 = lean_ctor_get(x_25, 12);
lean_inc(x_133);
x_134 = lean_ctor_get(x_25, 13);
lean_inc(x_134);
x_135 = lean_ctor_get_uint8(x_25, sizeof(void*)*18);
x_136 = lean_ctor_get(x_25, 14);
lean_inc(x_136);
x_137 = lean_ctor_get(x_25, 15);
lean_inc(x_137);
x_138 = lean_ctor_get(x_25, 16);
lean_inc(x_138);
x_139 = lean_ctor_get(x_25, 17);
lean_inc(x_139);
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
 x_140 = x_25;
} else {
 lean_dec_ref(x_25);
 x_140 = lean_box(0);
}
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_12);
x_142 = l_Lean_PersistentArray_set___redArg(x_126, x_11, x_141);
lean_dec(x_11);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 18, 1);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_121);
lean_ctor_set(x_143, 1, x_122);
lean_ctor_set(x_143, 2, x_123);
lean_ctor_set(x_143, 3, x_124);
lean_ctor_set(x_143, 4, x_125);
lean_ctor_set(x_143, 5, x_142);
lean_ctor_set(x_143, 6, x_127);
lean_ctor_set(x_143, 7, x_128);
lean_ctor_set(x_143, 8, x_129);
lean_ctor_set(x_143, 9, x_130);
lean_ctor_set(x_143, 10, x_131);
lean_ctor_set(x_143, 11, x_132);
lean_ctor_set(x_143, 12, x_133);
lean_ctor_set(x_143, 13, x_134);
lean_ctor_set(x_143, 14, x_136);
lean_ctor_set(x_143, 15, x_137);
lean_ctor_set(x_143, 16, x_138);
lean_ctor_set(x_143, 17, x_139);
lean_ctor_set_uint8(x_143, sizeof(void*)*18, x_135);
if (lean_is_scalar(x_120)) {
 x_144 = lean_alloc_ctor(0, 4, 0);
} else {
 x_144 = x_120;
}
lean_ctor_set(x_144, 0, x_117);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_144, 2, x_118);
lean_ctor_set(x_144, 3, x_119);
x_145 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_145, 0, x_101);
lean_ctor_set(x_145, 1, x_102);
lean_ctor_set(x_145, 2, x_103);
lean_ctor_set(x_145, 3, x_104);
lean_ctor_set(x_145, 4, x_105);
lean_ctor_set(x_145, 5, x_106);
lean_ctor_set(x_145, 6, x_107);
lean_ctor_set(x_145, 7, x_108);
lean_ctor_set(x_145, 8, x_110);
lean_ctor_set(x_145, 9, x_111);
lean_ctor_set(x_145, 10, x_112);
lean_ctor_set(x_145, 11, x_113);
lean_ctor_set(x_145, 12, x_114);
lean_ctor_set(x_145, 13, x_115);
lean_ctor_set(x_145, 14, x_144);
lean_ctor_set(x_145, 15, x_116);
lean_ctor_set_uint8(x_145, sizeof(void*)*16, x_109);
x_146 = lean_st_ref_set(x_14, x_145, x_26);
lean_dec(x_14);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
x_149 = lean_box(0);
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_148;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_147);
return x_150;
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
block_170:
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_152);
x_163 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_162, x_153, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161);
if (lean_obj_tag(x_163) == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_163, 0);
lean_dec(x_165);
x_166 = lean_box(0);
lean_ctor_set(x_163, 0, x_166);
return x_163;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_163, 1);
lean_inc(x_167);
lean_dec(x_163);
x_168 = lean_box(0);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
return x_163;
}
}
block_174:
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_box(0);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
return x_173;
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

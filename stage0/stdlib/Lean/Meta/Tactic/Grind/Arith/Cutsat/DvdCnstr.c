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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__5;
lean_object* l_Lean_Meta_isInstDvdInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__3;
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__6;
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
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2962_(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstDvdNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__2;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5;
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_19);
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
lean_inc_ref(x_3);
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_3, x_6, x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc_ref(x_5);
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
lean_dec_ref(x_51);
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
lean_dec_ref(x_62);
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
lean_inc_ref(x_5);
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
lean_dec_ref(x_78);
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
lean_inc_ref(x_3);
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
lean_inc_ref(x_5);
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
lean_dec_ref(x_99);
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
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_26);
x_27 = l_Int_Linear_Poly_findVarToSubst___redArg(x_26, x_2, x_10);
lean_dec_ref(x_26);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
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
x_43 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg(x_42, x_38, x_35, x_37, x_1, x_2, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_37);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_1 = x_44;
x_10 = x_45;
goto _start;
}
}
else
{
lean_object* x_47; 
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
x_47 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_17, x_10);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; uint8_t x_63; 
x_48 = lean_ctor_get(x_8, 0);
x_49 = lean_ctor_get(x_8, 1);
x_50 = lean_ctor_get(x_8, 2);
x_51 = lean_ctor_get(x_8, 3);
x_52 = lean_ctor_get(x_8, 4);
x_53 = lean_ctor_get(x_8, 5);
x_54 = lean_ctor_get(x_8, 6);
x_55 = lean_ctor_get(x_8, 7);
x_56 = lean_ctor_get(x_8, 8);
x_57 = lean_ctor_get(x_8, 9);
x_58 = lean_ctor_get(x_8, 10);
x_59 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_60 = lean_ctor_get(x_8, 11);
x_61 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_62 = lean_ctor_get(x_8, 12);
lean_inc(x_62);
lean_inc(x_60);
lean_inc(x_58);
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
lean_dec(x_8);
x_63 = lean_nat_dec_eq(x_51, x_52);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_64);
x_65 = l_Int_Linear_Poly_findVarToSubst___redArg(x_64, x_2, x_10);
lean_dec_ref(x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_62);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
lean_dec_ref(x_66);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_dec_ref(x_65);
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_ctor_get(x_72, 0);
lean_inc_ref(x_76);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_51, x_77);
lean_dec(x_51);
x_79 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_79, 0, x_48);
lean_ctor_set(x_79, 1, x_49);
lean_ctor_set(x_79, 2, x_50);
lean_ctor_set(x_79, 3, x_78);
lean_ctor_set(x_79, 4, x_52);
lean_ctor_set(x_79, 5, x_53);
lean_ctor_set(x_79, 6, x_54);
lean_ctor_set(x_79, 7, x_55);
lean_ctor_set(x_79, 8, x_56);
lean_ctor_set(x_79, 9, x_57);
lean_ctor_set(x_79, 10, x_58);
lean_ctor_set(x_79, 11, x_60);
lean_ctor_set(x_79, 12, x_62);
lean_ctor_set_uint8(x_79, sizeof(void*)*13, x_59);
lean_ctor_set_uint8(x_79, sizeof(void*)*13 + 1, x_61);
x_80 = l_Int_Linear_Poly_coeff(x_76, x_75);
lean_dec_ref(x_76);
x_81 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg(x_80, x_75, x_72, x_74, x_1, x_2, x_6, x_7, x_79, x_9, x_73);
lean_dec(x_74);
lean_dec(x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_1 = x_82;
x_8 = x_79;
x_10 = x_83;
goto _start;
}
}
else
{
lean_object* x_85; 
lean_dec_ref(x_62);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_1);
x_85 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_53, x_10);
return x_85;
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
lean_dec_ref(x_202);
x_206 = lean_unsigned_to_nat(1u);
x_207 = lean_nat_add(x_191, x_206);
lean_dec(x_191);
lean_ctor_set(x_8, 3, x_207);
x_598 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_599 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_598, x_8, x_205);
x_600 = !lean_is_exclusive(x_599);
if (x_600 == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; uint8_t x_724; 
x_601 = lean_ctor_get(x_599, 0);
x_602 = lean_ctor_get(x_599, 1);
x_603 = lean_box(0);
x_724 = lean_unbox(x_601);
lean_dec(x_601);
if (x_724 == 0)
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
goto block_723;
}
else
{
lean_object* x_725; uint8_t x_726; 
lean_inc_ref(x_1);
x_725 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_602);
x_726 = !lean_is_exclusive(x_725);
if (x_726 == 0)
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_727 = lean_ctor_get(x_725, 0);
x_728 = lean_ctor_get(x_725, 1);
x_729 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_725, 7);
lean_ctor_set(x_725, 1, x_727);
lean_ctor_set(x_725, 0, x_729);
lean_ctor_set_tag(x_599, 7);
lean_ctor_set(x_599, 1, x_729);
lean_ctor_set(x_599, 0, x_725);
x_730 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_598, x_599, x_6, x_7, x_8, x_9, x_728);
x_731 = lean_ctor_get(x_730, 1);
lean_inc(x_731);
lean_dec_ref(x_730);
x_628 = x_2;
x_629 = x_3;
x_630 = x_4;
x_631 = x_5;
x_632 = x_6;
x_633 = x_7;
x_634 = x_8;
x_635 = x_9;
x_636 = x_731;
goto block_723;
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_732 = lean_ctor_get(x_725, 0);
x_733 = lean_ctor_get(x_725, 1);
lean_inc(x_733);
lean_inc(x_732);
lean_dec(x_725);
x_734 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_735 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_732);
lean_ctor_set_tag(x_599, 7);
lean_ctor_set(x_599, 1, x_734);
lean_ctor_set(x_599, 0, x_735);
x_736 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_598, x_599, x_6, x_7, x_8, x_9, x_733);
x_737 = lean_ctor_get(x_736, 1);
lean_inc(x_737);
lean_dec_ref(x_736);
x_628 = x_2;
x_629 = x_3;
x_630 = x_4;
x_631 = x_5;
x_632 = x_6;
x_633 = x_7;
x_634 = x_8;
x_635 = x_9;
x_636 = x_737;
goto block_723;
}
}
block_627:
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; 
x_619 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_610, x_618);
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_620, 6);
lean_inc_ref(x_621);
lean_dec(x_620);
x_622 = lean_ctor_get(x_619, 1);
lean_inc(x_622);
lean_dec_ref(x_619);
x_623 = lean_ctor_get(x_621, 2);
lean_inc(x_623);
x_624 = lean_nat_dec_lt(x_609, x_623);
lean_dec(x_623);
if (x_624 == 0)
{
lean_object* x_625; 
lean_dec_ref(x_621);
x_625 = l_outOfBounds___redArg(x_603);
x_208 = x_604;
x_209 = x_615;
x_210 = x_606;
x_211 = x_614;
x_212 = x_607;
x_213 = x_611;
x_214 = x_613;
x_215 = x_612;
x_216 = x_617;
x_217 = x_609;
x_218 = x_610;
x_219 = x_616;
x_220 = x_605;
x_221 = x_622;
x_222 = x_608;
x_223 = x_625;
goto block_597;
}
else
{
lean_object* x_626; 
x_626 = l_Lean_PersistentArray_get_x21___redArg(x_603, x_621, x_609);
x_208 = x_604;
x_209 = x_615;
x_210 = x_606;
x_211 = x_614;
x_212 = x_607;
x_213 = x_611;
x_214 = x_613;
x_215 = x_612;
x_216 = x_617;
x_217 = x_609;
x_218 = x_610;
x_219 = x_616;
x_220 = x_605;
x_221 = x_622;
x_222 = x_608;
x_223 = x_626;
goto block_597;
}
}
block_723:
{
lean_object* x_637; lean_object* x_638; 
x_637 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_634);
x_638 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_637, x_628, x_629, x_630, x_631, x_632, x_633, x_634, x_635, x_636);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; uint8_t x_643; 
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_638, 1);
lean_inc(x_640);
lean_dec_ref(x_638);
x_641 = lean_ctor_get(x_639, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_639, 1);
lean_inc_ref(x_642);
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
lean_dec_ref(x_642);
lean_dec(x_641);
lean_dec(x_631);
lean_dec_ref(x_630);
lean_dec(x_629);
x_645 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_639, x_628, x_632, x_633, x_634, x_635, x_640);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_632);
lean_dec(x_628);
return x_645;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; uint8_t x_652; uint8_t x_653; uint8_t x_654; 
x_646 = lean_ctor_get(x_642, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_642, 1);
lean_inc(x_647);
x_648 = lean_ctor_get(x_642, 2);
lean_inc_ref(x_648);
lean_inc(x_639);
x_649 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_639, x_628, x_640);
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_649, 1);
lean_inc(x_651);
lean_dec_ref(x_649);
x_652 = 0;
x_653 = lean_unbox(x_650);
lean_dec(x_650);
x_654 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_653, x_652);
if (x_654 == 0)
{
x_604 = x_642;
x_605 = x_646;
x_606 = x_641;
x_607 = x_648;
x_608 = x_639;
x_609 = x_647;
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
lean_object* x_655; lean_object* x_656; 
x_655 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_647, x_628, x_651);
x_656 = lean_ctor_get(x_655, 1);
lean_inc(x_656);
lean_dec_ref(x_655);
x_604 = x_642;
x_605 = x_646;
x_606 = x_641;
x_607 = x_648;
x_608 = x_639;
x_609 = x_647;
x_610 = x_628;
x_611 = x_629;
x_612 = x_630;
x_613 = x_631;
x_614 = x_632;
x_615 = x_633;
x_616 = x_634;
x_617 = x_635;
x_618 = x_656;
goto block_627;
}
}
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; uint8_t x_660; 
lean_dec_ref(x_642);
lean_dec(x_641);
lean_dec(x_631);
lean_dec_ref(x_630);
lean_dec(x_629);
x_657 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_658 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_657, x_634, x_640);
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
x_660 = lean_unbox(x_659);
lean_dec(x_659);
if (x_660 == 0)
{
lean_object* x_661; 
lean_dec(x_639);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_632);
lean_dec(x_628);
x_661 = lean_ctor_get(x_658, 1);
lean_inc(x_661);
lean_dec_ref(x_658);
x_183 = x_661;
goto block_186;
}
else
{
uint8_t x_662; 
x_662 = !lean_is_exclusive(x_658);
if (x_662 == 0)
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; uint8_t x_666; 
x_663 = lean_ctor_get(x_658, 1);
x_664 = lean_ctor_get(x_658, 0);
lean_dec(x_664);
x_665 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_639, x_628, x_663);
lean_dec(x_628);
x_666 = !lean_is_exclusive(x_665);
if (x_666 == 0)
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_667 = lean_ctor_get(x_665, 0);
x_668 = lean_ctor_get(x_665, 1);
x_669 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_665, 7);
lean_ctor_set(x_665, 1, x_667);
lean_ctor_set(x_665, 0, x_669);
lean_ctor_set_tag(x_658, 7);
lean_ctor_set(x_658, 1, x_669);
lean_ctor_set(x_658, 0, x_665);
x_670 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_657, x_658, x_632, x_633, x_634, x_635, x_668);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_632);
x_671 = lean_ctor_get(x_670, 1);
lean_inc(x_671);
lean_dec_ref(x_670);
x_183 = x_671;
goto block_186;
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_672 = lean_ctor_get(x_665, 0);
x_673 = lean_ctor_get(x_665, 1);
lean_inc(x_673);
lean_inc(x_672);
lean_dec(x_665);
x_674 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_675 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_675, 0, x_674);
lean_ctor_set(x_675, 1, x_672);
lean_ctor_set_tag(x_658, 7);
lean_ctor_set(x_658, 1, x_674);
lean_ctor_set(x_658, 0, x_675);
x_676 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_657, x_658, x_632, x_633, x_634, x_635, x_673);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_632);
x_677 = lean_ctor_get(x_676, 1);
lean_inc(x_677);
lean_dec_ref(x_676);
x_183 = x_677;
goto block_186;
}
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_678 = lean_ctor_get(x_658, 1);
lean_inc(x_678);
lean_dec(x_658);
x_679 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_639, x_628, x_678);
lean_dec(x_628);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_679, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 x_682 = x_679;
} else {
 lean_dec_ref(x_679);
 x_682 = lean_box(0);
}
x_683 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_682)) {
 x_684 = lean_alloc_ctor(7, 2, 0);
} else {
 x_684 = x_682;
 lean_ctor_set_tag(x_684, 7);
}
lean_ctor_set(x_684, 0, x_683);
lean_ctor_set(x_684, 1, x_680);
x_685 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_685, 0, x_684);
lean_ctor_set(x_685, 1, x_683);
x_686 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_657, x_685, x_632, x_633, x_634, x_635, x_681);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_632);
x_687 = lean_ctor_get(x_686, 1);
lean_inc(x_687);
lean_dec_ref(x_686);
x_183 = x_687;
goto block_186;
}
}
}
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; uint8_t x_691; 
lean_dec_ref(x_642);
lean_dec(x_641);
x_688 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_689 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_688, x_634, x_640);
x_690 = lean_ctor_get(x_689, 0);
lean_inc(x_690);
x_691 = lean_unbox(x_690);
lean_dec(x_690);
if (x_691 == 0)
{
lean_object* x_692; 
x_692 = lean_ctor_get(x_689, 1);
lean_inc(x_692);
lean_dec_ref(x_689);
x_164 = x_639;
x_165 = x_628;
x_166 = x_629;
x_167 = x_630;
x_168 = x_631;
x_169 = x_632;
x_170 = x_633;
x_171 = x_634;
x_172 = x_635;
x_173 = x_692;
goto block_182;
}
else
{
uint8_t x_693; 
x_693 = !lean_is_exclusive(x_689);
if (x_693 == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; uint8_t x_697; 
x_694 = lean_ctor_get(x_689, 1);
x_695 = lean_ctor_get(x_689, 0);
lean_dec(x_695);
lean_inc(x_639);
x_696 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_639, x_628, x_694);
x_697 = !lean_is_exclusive(x_696);
if (x_697 == 0)
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_698 = lean_ctor_get(x_696, 0);
x_699 = lean_ctor_get(x_696, 1);
x_700 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
lean_ctor_set_tag(x_696, 7);
lean_ctor_set(x_696, 1, x_698);
lean_ctor_set(x_696, 0, x_700);
lean_ctor_set_tag(x_689, 7);
lean_ctor_set(x_689, 1, x_700);
lean_ctor_set(x_689, 0, x_696);
x_701 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_688, x_689, x_632, x_633, x_634, x_635, x_699);
x_702 = lean_ctor_get(x_701, 1);
lean_inc(x_702);
lean_dec_ref(x_701);
x_164 = x_639;
x_165 = x_628;
x_166 = x_629;
x_167 = x_630;
x_168 = x_631;
x_169 = x_632;
x_170 = x_633;
x_171 = x_634;
x_172 = x_635;
x_173 = x_702;
goto block_182;
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_703 = lean_ctor_get(x_696, 0);
x_704 = lean_ctor_get(x_696, 1);
lean_inc(x_704);
lean_inc(x_703);
lean_dec(x_696);
x_705 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_706 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_703);
lean_ctor_set_tag(x_689, 7);
lean_ctor_set(x_689, 1, x_705);
lean_ctor_set(x_689, 0, x_706);
x_707 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_688, x_689, x_632, x_633, x_634, x_635, x_704);
x_708 = lean_ctor_get(x_707, 1);
lean_inc(x_708);
lean_dec_ref(x_707);
x_164 = x_639;
x_165 = x_628;
x_166 = x_629;
x_167 = x_630;
x_168 = x_631;
x_169 = x_632;
x_170 = x_633;
x_171 = x_634;
x_172 = x_635;
x_173 = x_708;
goto block_182;
}
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_709 = lean_ctor_get(x_689, 1);
lean_inc(x_709);
lean_dec(x_689);
lean_inc(x_639);
x_710 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_639, x_628, x_709);
x_711 = lean_ctor_get(x_710, 0);
lean_inc(x_711);
x_712 = lean_ctor_get(x_710, 1);
lean_inc(x_712);
if (lean_is_exclusive(x_710)) {
 lean_ctor_release(x_710, 0);
 lean_ctor_release(x_710, 1);
 x_713 = x_710;
} else {
 lean_dec_ref(x_710);
 x_713 = lean_box(0);
}
x_714 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_713)) {
 x_715 = lean_alloc_ctor(7, 2, 0);
} else {
 x_715 = x_713;
 lean_ctor_set_tag(x_715, 7);
}
lean_ctor_set(x_715, 0, x_714);
lean_ctor_set(x_715, 1, x_711);
x_716 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_716, 0, x_715);
lean_ctor_set(x_716, 1, x_714);
x_717 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_688, x_716, x_632, x_633, x_634, x_635, x_712);
x_718 = lean_ctor_get(x_717, 1);
lean_inc(x_718);
lean_dec_ref(x_717);
x_164 = x_639;
x_165 = x_628;
x_166 = x_629;
x_167 = x_630;
x_168 = x_631;
x_169 = x_632;
x_170 = x_633;
x_171 = x_634;
x_172 = x_635;
x_173 = x_718;
goto block_182;
}
}
}
}
else
{
uint8_t x_719; 
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_632);
lean_dec(x_631);
lean_dec_ref(x_630);
lean_dec(x_629);
lean_dec(x_628);
x_719 = !lean_is_exclusive(x_638);
if (x_719 == 0)
{
return x_638;
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_720 = lean_ctor_get(x_638, 0);
x_721 = lean_ctor_get(x_638, 1);
lean_inc(x_721);
lean_inc(x_720);
lean_dec(x_638);
x_722 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_722, 0, x_720);
lean_ctor_set(x_722, 1, x_721);
return x_722;
}
}
}
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; uint8_t x_831; 
x_738 = lean_ctor_get(x_599, 0);
x_739 = lean_ctor_get(x_599, 1);
lean_inc(x_739);
lean_inc(x_738);
lean_dec(x_599);
x_740 = lean_box(0);
x_831 = lean_unbox(x_738);
lean_dec(x_738);
if (x_831 == 0)
{
x_765 = x_2;
x_766 = x_3;
x_767 = x_4;
x_768 = x_5;
x_769 = x_6;
x_770 = x_7;
x_771 = x_8;
x_772 = x_9;
x_773 = x_739;
goto block_830;
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; 
lean_inc_ref(x_1);
x_832 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_739);
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 lean_ctor_release(x_832, 1);
 x_835 = x_832;
} else {
 lean_dec_ref(x_832);
 x_835 = lean_box(0);
}
x_836 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_835)) {
 x_837 = lean_alloc_ctor(7, 2, 0);
} else {
 x_837 = x_835;
 lean_ctor_set_tag(x_837, 7);
}
lean_ctor_set(x_837, 0, x_836);
lean_ctor_set(x_837, 1, x_833);
x_838 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_838, 0, x_837);
lean_ctor_set(x_838, 1, x_836);
x_839 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_598, x_838, x_6, x_7, x_8, x_9, x_834);
x_840 = lean_ctor_get(x_839, 1);
lean_inc(x_840);
lean_dec_ref(x_839);
x_765 = x_2;
x_766 = x_3;
x_767 = x_4;
x_768 = x_5;
x_769 = x_6;
x_770 = x_7;
x_771 = x_8;
x_772 = x_9;
x_773 = x_840;
goto block_830;
}
block_764:
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; uint8_t x_761; 
x_756 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_747, x_755);
x_757 = lean_ctor_get(x_756, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_757, 6);
lean_inc_ref(x_758);
lean_dec(x_757);
x_759 = lean_ctor_get(x_756, 1);
lean_inc(x_759);
lean_dec_ref(x_756);
x_760 = lean_ctor_get(x_758, 2);
lean_inc(x_760);
x_761 = lean_nat_dec_lt(x_746, x_760);
lean_dec(x_760);
if (x_761 == 0)
{
lean_object* x_762; 
lean_dec_ref(x_758);
x_762 = l_outOfBounds___redArg(x_740);
x_208 = x_741;
x_209 = x_752;
x_210 = x_743;
x_211 = x_751;
x_212 = x_744;
x_213 = x_748;
x_214 = x_750;
x_215 = x_749;
x_216 = x_754;
x_217 = x_746;
x_218 = x_747;
x_219 = x_753;
x_220 = x_742;
x_221 = x_759;
x_222 = x_745;
x_223 = x_762;
goto block_597;
}
else
{
lean_object* x_763; 
x_763 = l_Lean_PersistentArray_get_x21___redArg(x_740, x_758, x_746);
x_208 = x_741;
x_209 = x_752;
x_210 = x_743;
x_211 = x_751;
x_212 = x_744;
x_213 = x_748;
x_214 = x_750;
x_215 = x_749;
x_216 = x_754;
x_217 = x_746;
x_218 = x_747;
x_219 = x_753;
x_220 = x_742;
x_221 = x_759;
x_222 = x_745;
x_223 = x_763;
goto block_597;
}
}
block_830:
{
lean_object* x_774; lean_object* x_775; 
x_774 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_771);
x_775 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_774, x_765, x_766, x_767, x_768, x_769, x_770, x_771, x_772, x_773);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; uint8_t x_780; 
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
lean_dec_ref(x_775);
x_778 = lean_ctor_get(x_776, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_776, 1);
lean_inc_ref(x_779);
lean_inc(x_778);
x_780 = l_Int_Linear_Poly_isUnsatDvd(x_778, x_779);
if (x_780 == 0)
{
uint8_t x_781; 
x_781 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_776);
if (x_781 == 0)
{
if (lean_obj_tag(x_779) == 0)
{
lean_object* x_782; 
lean_dec_ref(x_779);
lean_dec(x_778);
lean_dec(x_768);
lean_dec_ref(x_767);
lean_dec(x_766);
x_782 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_776, x_765, x_769, x_770, x_771, x_772, x_777);
lean_dec(x_772);
lean_dec_ref(x_771);
lean_dec(x_770);
lean_dec_ref(x_769);
lean_dec(x_765);
return x_782;
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; uint8_t x_789; uint8_t x_790; uint8_t x_791; 
x_783 = lean_ctor_get(x_779, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_779, 1);
lean_inc(x_784);
x_785 = lean_ctor_get(x_779, 2);
lean_inc_ref(x_785);
lean_inc(x_776);
x_786 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_776, x_765, x_777);
x_787 = lean_ctor_get(x_786, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
lean_dec_ref(x_786);
x_789 = 0;
x_790 = lean_unbox(x_787);
lean_dec(x_787);
x_791 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_790, x_789);
if (x_791 == 0)
{
x_741 = x_779;
x_742 = x_783;
x_743 = x_778;
x_744 = x_785;
x_745 = x_776;
x_746 = x_784;
x_747 = x_765;
x_748 = x_766;
x_749 = x_767;
x_750 = x_768;
x_751 = x_769;
x_752 = x_770;
x_753 = x_771;
x_754 = x_772;
x_755 = x_788;
goto block_764;
}
else
{
lean_object* x_792; lean_object* x_793; 
x_792 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_784, x_765, x_788);
x_793 = lean_ctor_get(x_792, 1);
lean_inc(x_793);
lean_dec_ref(x_792);
x_741 = x_779;
x_742 = x_783;
x_743 = x_778;
x_744 = x_785;
x_745 = x_776;
x_746 = x_784;
x_747 = x_765;
x_748 = x_766;
x_749 = x_767;
x_750 = x_768;
x_751 = x_769;
x_752 = x_770;
x_753 = x_771;
x_754 = x_772;
x_755 = x_793;
goto block_764;
}
}
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; uint8_t x_797; 
lean_dec_ref(x_779);
lean_dec(x_778);
lean_dec(x_768);
lean_dec_ref(x_767);
lean_dec(x_766);
x_794 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_795 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_794, x_771, x_777);
x_796 = lean_ctor_get(x_795, 0);
lean_inc(x_796);
x_797 = lean_unbox(x_796);
lean_dec(x_796);
if (x_797 == 0)
{
lean_object* x_798; 
lean_dec(x_776);
lean_dec(x_772);
lean_dec_ref(x_771);
lean_dec(x_770);
lean_dec_ref(x_769);
lean_dec(x_765);
x_798 = lean_ctor_get(x_795, 1);
lean_inc(x_798);
lean_dec_ref(x_795);
x_183 = x_798;
goto block_186;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; 
x_799 = lean_ctor_get(x_795, 1);
lean_inc(x_799);
if (lean_is_exclusive(x_795)) {
 lean_ctor_release(x_795, 0);
 lean_ctor_release(x_795, 1);
 x_800 = x_795;
} else {
 lean_dec_ref(x_795);
 x_800 = lean_box(0);
}
x_801 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_776, x_765, x_799);
lean_dec(x_765);
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_801, 1);
lean_inc(x_803);
if (lean_is_exclusive(x_801)) {
 lean_ctor_release(x_801, 0);
 lean_ctor_release(x_801, 1);
 x_804 = x_801;
} else {
 lean_dec_ref(x_801);
 x_804 = lean_box(0);
}
x_805 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_804)) {
 x_806 = lean_alloc_ctor(7, 2, 0);
} else {
 x_806 = x_804;
 lean_ctor_set_tag(x_806, 7);
}
lean_ctor_set(x_806, 0, x_805);
lean_ctor_set(x_806, 1, x_802);
if (lean_is_scalar(x_800)) {
 x_807 = lean_alloc_ctor(7, 2, 0);
} else {
 x_807 = x_800;
 lean_ctor_set_tag(x_807, 7);
}
lean_ctor_set(x_807, 0, x_806);
lean_ctor_set(x_807, 1, x_805);
x_808 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_794, x_807, x_769, x_770, x_771, x_772, x_803);
lean_dec(x_772);
lean_dec_ref(x_771);
lean_dec(x_770);
lean_dec_ref(x_769);
x_809 = lean_ctor_get(x_808, 1);
lean_inc(x_809);
lean_dec_ref(x_808);
x_183 = x_809;
goto block_186;
}
}
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; uint8_t x_813; 
lean_dec_ref(x_779);
lean_dec(x_778);
x_810 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_811 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_810, x_771, x_777);
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
x_813 = lean_unbox(x_812);
lean_dec(x_812);
if (x_813 == 0)
{
lean_object* x_814; 
x_814 = lean_ctor_get(x_811, 1);
lean_inc(x_814);
lean_dec_ref(x_811);
x_164 = x_776;
x_165 = x_765;
x_166 = x_766;
x_167 = x_767;
x_168 = x_768;
x_169 = x_769;
x_170 = x_770;
x_171 = x_771;
x_172 = x_772;
x_173 = x_814;
goto block_182;
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_815 = lean_ctor_get(x_811, 1);
lean_inc(x_815);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 lean_ctor_release(x_811, 1);
 x_816 = x_811;
} else {
 lean_dec_ref(x_811);
 x_816 = lean_box(0);
}
lean_inc(x_776);
x_817 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_776, x_765, x_815);
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_817, 1);
lean_inc(x_819);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 x_820 = x_817;
} else {
 lean_dec_ref(x_817);
 x_820 = lean_box(0);
}
x_821 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_820)) {
 x_822 = lean_alloc_ctor(7, 2, 0);
} else {
 x_822 = x_820;
 lean_ctor_set_tag(x_822, 7);
}
lean_ctor_set(x_822, 0, x_821);
lean_ctor_set(x_822, 1, x_818);
if (lean_is_scalar(x_816)) {
 x_823 = lean_alloc_ctor(7, 2, 0);
} else {
 x_823 = x_816;
 lean_ctor_set_tag(x_823, 7);
}
lean_ctor_set(x_823, 0, x_822);
lean_ctor_set(x_823, 1, x_821);
x_824 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_810, x_823, x_769, x_770, x_771, x_772, x_819);
x_825 = lean_ctor_get(x_824, 1);
lean_inc(x_825);
lean_dec_ref(x_824);
x_164 = x_776;
x_165 = x_765;
x_166 = x_766;
x_167 = x_767;
x_168 = x_768;
x_169 = x_769;
x_170 = x_770;
x_171 = x_771;
x_172 = x_772;
x_173 = x_825;
goto block_182;
}
}
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; 
lean_dec(x_772);
lean_dec_ref(x_771);
lean_dec(x_770);
lean_dec_ref(x_769);
lean_dec(x_768);
lean_dec_ref(x_767);
lean_dec(x_766);
lean_dec(x_765);
x_826 = lean_ctor_get(x_775, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_775, 1);
lean_inc(x_827);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_828 = x_775;
} else {
 lean_dec_ref(x_775);
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
block_597:
{
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
lean_dec(x_220);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec(x_210);
x_224 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_225 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_224, x_219, x_221);
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
x_12 = x_217;
x_13 = x_222;
x_14 = x_218;
x_15 = x_211;
x_16 = x_209;
x_17 = x_219;
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
lean_inc_ref(x_222);
x_232 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_222, x_218, x_230);
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
x_237 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_224, x_225, x_211, x_209, x_219, x_216, x_235);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec_ref(x_237);
x_11 = x_208;
x_12 = x_217;
x_13 = x_222;
x_14 = x_218;
x_15 = x_211;
x_16 = x_209;
x_17 = x_219;
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
x_243 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_224, x_225, x_211, x_209, x_219, x_216, x_240);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec_ref(x_243);
x_11 = x_208;
x_12 = x_217;
x_13 = x_222;
x_14 = x_218;
x_15 = x_211;
x_16 = x_209;
x_17 = x_219;
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
lean_inc_ref(x_222);
x_246 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_222, x_218, x_245);
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
x_253 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_224, x_252, x_211, x_209, x_219, x_216, x_248);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec_ref(x_253);
x_11 = x_208;
x_12 = x_217;
x_13 = x_222;
x_14 = x_218;
x_15 = x_211;
x_16 = x_209;
x_17 = x_219;
x_18 = x_216;
x_19 = x_254;
goto block_163;
}
}
}
else
{
lean_object* x_255; lean_object* x_256; 
lean_dec_ref(x_208);
x_255 = lean_ctor_get(x_223, 0);
lean_inc(x_255);
lean_dec_ref(x_223);
x_256 = lean_ctor_get(x_255, 1);
lean_inc_ref(x_256);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; 
lean_dec_ref(x_256);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec(x_217);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec(x_210);
x_257 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_255, x_218, x_211, x_209, x_219, x_216, x_221);
lean_dec(x_216);
lean_dec_ref(x_219);
lean_dec(x_209);
lean_dec_ref(x_211);
lean_dec(x_218);
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
x_263 = lean_int_mul(x_220, x_258);
x_264 = lean_int_mul(x_260, x_210);
x_265 = l_Lean_Meta_Grind_Arith_gcdExt(x_263, x_264);
lean_dec(x_264);
lean_dec(x_263);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 0);
lean_inc(x_267);
lean_dec_ref(x_265);
x_268 = lean_ctor_get(x_266, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
lean_dec(x_266);
x_270 = lean_st_ref_take(x_218, x_221);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_271, 14);
lean_inc_ref(x_272);
x_273 = lean_ctor_get(x_272, 1);
lean_inc_ref(x_273);
x_274 = lean_ctor_get(x_270, 1);
lean_inc(x_274);
lean_dec_ref(x_270);
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
x_280 = lean_ctor_get(x_273, 6);
x_281 = lean_box(0);
x_282 = l_Lean_PersistentArray_set___redArg(x_280, x_217, x_281);
lean_ctor_set(x_273, 6, x_282);
x_283 = lean_st_ref_set(x_218, x_271, x_274);
x_284 = !lean_is_exclusive(x_283);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_285 = lean_ctor_get(x_283, 1);
x_286 = lean_ctor_get(x_283, 0);
lean_dec(x_286);
x_287 = lean_int_mul(x_268, x_258);
lean_dec(x_268);
lean_inc_ref(x_212);
x_288 = l_Int_Linear_Poly_mul(x_212, x_287);
lean_dec(x_287);
x_289 = lean_int_mul(x_269, x_210);
lean_dec(x_269);
lean_inc_ref(x_261);
x_290 = l_Int_Linear_Poly_mul(x_261, x_289);
lean_dec(x_289);
x_291 = lean_int_mul(x_210, x_258);
lean_dec(x_258);
lean_dec(x_210);
x_292 = l_Int_Linear_Poly_combine(x_288, x_290);
lean_inc(x_267);
lean_ctor_set(x_256, 2, x_292);
lean_ctor_set(x_256, 1, x_217);
lean_ctor_set(x_256, 0, x_267);
lean_inc(x_255);
lean_inc_ref(x_222);
lean_ctor_set_tag(x_283, 4);
lean_ctor_set(x_283, 1, x_255);
lean_ctor_set(x_283, 0, x_222);
x_293 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_256);
lean_ctor_set(x_293, 2, x_283);
lean_inc(x_216);
lean_inc_ref(x_219);
lean_inc(x_209);
lean_inc_ref(x_211);
lean_inc(x_214);
lean_inc_ref(x_215);
lean_inc(x_213);
lean_inc(x_218);
x_294 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_293, x_218, x_213, x_215, x_214, x_211, x_209, x_219, x_216, x_285);
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
x_298 = l_Int_Linear_Poly_mul(x_212, x_260);
lean_dec(x_260);
x_299 = lean_int_neg(x_220);
lean_dec(x_220);
x_300 = l_Int_Linear_Poly_mul(x_261, x_299);
lean_dec(x_299);
x_301 = l_Int_Linear_Poly_combine(x_298, x_300);
lean_inc(x_255);
lean_ctor_set_tag(x_294, 5);
lean_ctor_set(x_294, 1, x_255);
lean_ctor_set(x_294, 0, x_222);
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
x_2 = x_218;
x_3 = x_213;
x_4 = x_215;
x_5 = x_214;
x_6 = x_211;
x_7 = x_209;
x_8 = x_219;
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
x_2 = x_218;
x_3 = x_213;
x_4 = x_215;
x_5 = x_214;
x_6 = x_211;
x_7 = x_209;
x_8 = x_219;
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
x_310 = l_Int_Linear_Poly_mul(x_212, x_260);
lean_dec(x_260);
x_311 = lean_int_neg(x_220);
lean_dec(x_220);
x_312 = l_Int_Linear_Poly_mul(x_261, x_311);
lean_dec(x_311);
x_313 = l_Int_Linear_Poly_combine(x_310, x_312);
lean_inc(x_255);
x_314 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_314, 0, x_222);
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
x_2 = x_218;
x_3 = x_213;
x_4 = x_215;
x_5 = x_214;
x_6 = x_211;
x_7 = x_209;
x_8 = x_219;
x_9 = x_216;
x_10 = x_309;
goto _start;
}
}
else
{
lean_dec(x_267);
lean_dec_ref(x_261);
lean_dec(x_260);
lean_dec(x_255);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec(x_209);
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
lean_inc_ref(x_212);
x_320 = l_Int_Linear_Poly_mul(x_212, x_319);
lean_dec(x_319);
x_321 = lean_int_mul(x_269, x_210);
lean_dec(x_269);
lean_inc_ref(x_261);
x_322 = l_Int_Linear_Poly_mul(x_261, x_321);
lean_dec(x_321);
x_323 = lean_int_mul(x_210, x_258);
lean_dec(x_258);
lean_dec(x_210);
x_324 = l_Int_Linear_Poly_combine(x_320, x_322);
lean_inc(x_267);
lean_ctor_set(x_256, 2, x_324);
lean_ctor_set(x_256, 1, x_217);
lean_ctor_set(x_256, 0, x_267);
lean_inc(x_255);
lean_inc_ref(x_222);
x_325 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_325, 0, x_222);
lean_ctor_set(x_325, 1, x_255);
x_326 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_326, 0, x_323);
lean_ctor_set(x_326, 1, x_256);
lean_ctor_set(x_326, 2, x_325);
lean_inc(x_216);
lean_inc_ref(x_219);
lean_inc(x_209);
lean_inc_ref(x_211);
lean_inc(x_214);
lean_inc_ref(x_215);
lean_inc(x_213);
lean_inc(x_218);
x_327 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_326, x_218, x_213, x_215, x_214, x_211, x_209, x_219, x_216, x_318);
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
x_330 = l_Int_Linear_Poly_mul(x_212, x_260);
lean_dec(x_260);
x_331 = lean_int_neg(x_220);
lean_dec(x_220);
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
lean_ctor_set(x_334, 0, x_222);
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
x_2 = x_218;
x_3 = x_213;
x_4 = x_215;
x_5 = x_214;
x_6 = x_211;
x_7 = x_209;
x_8 = x_219;
x_9 = x_216;
x_10 = x_328;
goto _start;
}
else
{
lean_dec(x_267);
lean_dec_ref(x_261);
lean_dec(x_260);
lean_dec(x_255);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec(x_209);
return x_327;
}
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
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
x_353 = lean_ctor_get_uint8(x_273, sizeof(void*)*21);
x_354 = lean_ctor_get(x_273, 15);
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
lean_inc(x_354);
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
x_362 = l_Lean_PersistentArray_set___redArg(x_344, x_217, x_361);
x_363 = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(x_363, 0, x_338);
lean_ctor_set(x_363, 1, x_339);
lean_ctor_set(x_363, 2, x_340);
lean_ctor_set(x_363, 3, x_341);
lean_ctor_set(x_363, 4, x_342);
lean_ctor_set(x_363, 5, x_343);
lean_ctor_set(x_363, 6, x_362);
lean_ctor_set(x_363, 7, x_345);
lean_ctor_set(x_363, 8, x_346);
lean_ctor_set(x_363, 9, x_347);
lean_ctor_set(x_363, 10, x_348);
lean_ctor_set(x_363, 11, x_349);
lean_ctor_set(x_363, 12, x_350);
lean_ctor_set(x_363, 13, x_351);
lean_ctor_set(x_363, 14, x_352);
lean_ctor_set(x_363, 15, x_354);
lean_ctor_set(x_363, 16, x_355);
lean_ctor_set(x_363, 17, x_356);
lean_ctor_set(x_363, 18, x_357);
lean_ctor_set(x_363, 19, x_358);
lean_ctor_set(x_363, 20, x_359);
lean_ctor_set_uint8(x_363, sizeof(void*)*21, x_353);
lean_ctor_set_uint8(x_363, sizeof(void*)*21 + 1, x_360);
lean_ctor_set(x_272, 1, x_363);
x_364 = lean_st_ref_set(x_218, x_271, x_274);
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
lean_inc_ref(x_212);
x_368 = l_Int_Linear_Poly_mul(x_212, x_367);
lean_dec(x_367);
x_369 = lean_int_mul(x_269, x_210);
lean_dec(x_269);
lean_inc_ref(x_261);
x_370 = l_Int_Linear_Poly_mul(x_261, x_369);
lean_dec(x_369);
x_371 = lean_int_mul(x_210, x_258);
lean_dec(x_258);
lean_dec(x_210);
x_372 = l_Int_Linear_Poly_combine(x_368, x_370);
lean_inc(x_267);
lean_ctor_set(x_256, 2, x_372);
lean_ctor_set(x_256, 1, x_217);
lean_ctor_set(x_256, 0, x_267);
lean_inc(x_255);
lean_inc_ref(x_222);
if (lean_is_scalar(x_366)) {
 x_373 = lean_alloc_ctor(4, 2, 0);
} else {
 x_373 = x_366;
 lean_ctor_set_tag(x_373, 4);
}
lean_ctor_set(x_373, 0, x_222);
lean_ctor_set(x_373, 1, x_255);
x_374 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_256);
lean_ctor_set(x_374, 2, x_373);
lean_inc(x_216);
lean_inc_ref(x_219);
lean_inc(x_209);
lean_inc_ref(x_211);
lean_inc(x_214);
lean_inc_ref(x_215);
lean_inc(x_213);
lean_inc(x_218);
x_375 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_374, x_218, x_213, x_215, x_214, x_211, x_209, x_219, x_216, x_365);
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
x_378 = l_Int_Linear_Poly_mul(x_212, x_260);
lean_dec(x_260);
x_379 = lean_int_neg(x_220);
lean_dec(x_220);
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
lean_ctor_set(x_382, 0, x_222);
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
x_2 = x_218;
x_3 = x_213;
x_4 = x_215;
x_5 = x_214;
x_6 = x_211;
x_7 = x_209;
x_8 = x_219;
x_9 = x_216;
x_10 = x_376;
goto _start;
}
else
{
lean_dec(x_267);
lean_dec_ref(x_261);
lean_dec(x_260);
lean_dec(x_255);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec(x_209);
return x_375;
}
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_386 = lean_ctor_get(x_272, 0);
x_387 = lean_ctor_get(x_272, 2);
x_388 = lean_ctor_get(x_272, 3);
lean_inc(x_388);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_272);
x_389 = lean_ctor_get(x_273, 0);
lean_inc_ref(x_389);
x_390 = lean_ctor_get(x_273, 1);
lean_inc_ref(x_390);
x_391 = lean_ctor_get(x_273, 2);
lean_inc_ref(x_391);
x_392 = lean_ctor_get(x_273, 3);
lean_inc_ref(x_392);
x_393 = lean_ctor_get(x_273, 4);
lean_inc_ref(x_393);
x_394 = lean_ctor_get(x_273, 5);
lean_inc_ref(x_394);
x_395 = lean_ctor_get(x_273, 6);
lean_inc_ref(x_395);
x_396 = lean_ctor_get(x_273, 7);
lean_inc_ref(x_396);
x_397 = lean_ctor_get(x_273, 8);
lean_inc_ref(x_397);
x_398 = lean_ctor_get(x_273, 9);
lean_inc_ref(x_398);
x_399 = lean_ctor_get(x_273, 10);
lean_inc_ref(x_399);
x_400 = lean_ctor_get(x_273, 11);
lean_inc(x_400);
x_401 = lean_ctor_get(x_273, 12);
lean_inc_ref(x_401);
x_402 = lean_ctor_get(x_273, 13);
lean_inc_ref(x_402);
x_403 = lean_ctor_get(x_273, 14);
lean_inc(x_403);
x_404 = lean_ctor_get_uint8(x_273, sizeof(void*)*21);
x_405 = lean_ctor_get(x_273, 15);
lean_inc(x_405);
x_406 = lean_ctor_get(x_273, 16);
lean_inc_ref(x_406);
x_407 = lean_ctor_get(x_273, 17);
lean_inc_ref(x_407);
x_408 = lean_ctor_get(x_273, 18);
lean_inc_ref(x_408);
x_409 = lean_ctor_get(x_273, 19);
lean_inc_ref(x_409);
x_410 = lean_ctor_get(x_273, 20);
lean_inc_ref(x_410);
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
x_414 = l_Lean_PersistentArray_set___redArg(x_395, x_217, x_413);
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
lean_ctor_set(x_415, 6, x_414);
lean_ctor_set(x_415, 7, x_396);
lean_ctor_set(x_415, 8, x_397);
lean_ctor_set(x_415, 9, x_398);
lean_ctor_set(x_415, 10, x_399);
lean_ctor_set(x_415, 11, x_400);
lean_ctor_set(x_415, 12, x_401);
lean_ctor_set(x_415, 13, x_402);
lean_ctor_set(x_415, 14, x_403);
lean_ctor_set(x_415, 15, x_405);
lean_ctor_set(x_415, 16, x_406);
lean_ctor_set(x_415, 17, x_407);
lean_ctor_set(x_415, 18, x_408);
lean_ctor_set(x_415, 19, x_409);
lean_ctor_set(x_415, 20, x_410);
lean_ctor_set_uint8(x_415, sizeof(void*)*21, x_404);
lean_ctor_set_uint8(x_415, sizeof(void*)*21 + 1, x_411);
x_416 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_416, 0, x_386);
lean_ctor_set(x_416, 1, x_415);
lean_ctor_set(x_416, 2, x_387);
lean_ctor_set(x_416, 3, x_388);
lean_ctor_set(x_271, 14, x_416);
x_417 = lean_st_ref_set(x_218, x_271, x_274);
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
lean_inc_ref(x_212);
x_421 = l_Int_Linear_Poly_mul(x_212, x_420);
lean_dec(x_420);
x_422 = lean_int_mul(x_269, x_210);
lean_dec(x_269);
lean_inc_ref(x_261);
x_423 = l_Int_Linear_Poly_mul(x_261, x_422);
lean_dec(x_422);
x_424 = lean_int_mul(x_210, x_258);
lean_dec(x_258);
lean_dec(x_210);
x_425 = l_Int_Linear_Poly_combine(x_421, x_423);
lean_inc(x_267);
lean_ctor_set(x_256, 2, x_425);
lean_ctor_set(x_256, 1, x_217);
lean_ctor_set(x_256, 0, x_267);
lean_inc(x_255);
lean_inc_ref(x_222);
if (lean_is_scalar(x_419)) {
 x_426 = lean_alloc_ctor(4, 2, 0);
} else {
 x_426 = x_419;
 lean_ctor_set_tag(x_426, 4);
}
lean_ctor_set(x_426, 0, x_222);
lean_ctor_set(x_426, 1, x_255);
x_427 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_427, 0, x_424);
lean_ctor_set(x_427, 1, x_256);
lean_ctor_set(x_427, 2, x_426);
lean_inc(x_216);
lean_inc_ref(x_219);
lean_inc(x_209);
lean_inc_ref(x_211);
lean_inc(x_214);
lean_inc_ref(x_215);
lean_inc(x_213);
lean_inc(x_218);
x_428 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_427, x_218, x_213, x_215, x_214, x_211, x_209, x_219, x_216, x_418);
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
x_431 = l_Int_Linear_Poly_mul(x_212, x_260);
lean_dec(x_260);
x_432 = lean_int_neg(x_220);
lean_dec(x_220);
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
lean_ctor_set(x_435, 0, x_222);
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
x_2 = x_218;
x_3 = x_213;
x_4 = x_215;
x_5 = x_214;
x_6 = x_211;
x_7 = x_209;
x_8 = x_219;
x_9 = x_216;
x_10 = x_429;
goto _start;
}
else
{
lean_dec(x_267);
lean_dec_ref(x_261);
lean_dec(x_260);
lean_dec(x_255);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec(x_209);
return x_428;
}
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
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
lean_inc_ref(x_455);
x_456 = lean_ctor_get(x_272, 2);
lean_inc_ref(x_456);
x_457 = lean_ctor_get(x_272, 3);
lean_inc_ref(x_457);
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
lean_inc_ref(x_459);
x_460 = lean_ctor_get(x_273, 1);
lean_inc_ref(x_460);
x_461 = lean_ctor_get(x_273, 2);
lean_inc_ref(x_461);
x_462 = lean_ctor_get(x_273, 3);
lean_inc_ref(x_462);
x_463 = lean_ctor_get(x_273, 4);
lean_inc_ref(x_463);
x_464 = lean_ctor_get(x_273, 5);
lean_inc_ref(x_464);
x_465 = lean_ctor_get(x_273, 6);
lean_inc_ref(x_465);
x_466 = lean_ctor_get(x_273, 7);
lean_inc_ref(x_466);
x_467 = lean_ctor_get(x_273, 8);
lean_inc_ref(x_467);
x_468 = lean_ctor_get(x_273, 9);
lean_inc_ref(x_468);
x_469 = lean_ctor_get(x_273, 10);
lean_inc_ref(x_469);
x_470 = lean_ctor_get(x_273, 11);
lean_inc(x_470);
x_471 = lean_ctor_get(x_273, 12);
lean_inc_ref(x_471);
x_472 = lean_ctor_get(x_273, 13);
lean_inc_ref(x_472);
x_473 = lean_ctor_get(x_273, 14);
lean_inc(x_473);
x_474 = lean_ctor_get_uint8(x_273, sizeof(void*)*21);
x_475 = lean_ctor_get(x_273, 15);
lean_inc(x_475);
x_476 = lean_ctor_get(x_273, 16);
lean_inc_ref(x_476);
x_477 = lean_ctor_get(x_273, 17);
lean_inc_ref(x_477);
x_478 = lean_ctor_get(x_273, 18);
lean_inc_ref(x_478);
x_479 = lean_ctor_get(x_273, 19);
lean_inc_ref(x_479);
x_480 = lean_ctor_get(x_273, 20);
lean_inc_ref(x_480);
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
x_484 = l_Lean_PersistentArray_set___redArg(x_465, x_217, x_483);
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
lean_ctor_set(x_485, 6, x_484);
lean_ctor_set(x_485, 7, x_466);
lean_ctor_set(x_485, 8, x_467);
lean_ctor_set(x_485, 9, x_468);
lean_ctor_set(x_485, 10, x_469);
lean_ctor_set(x_485, 11, x_470);
lean_ctor_set(x_485, 12, x_471);
lean_ctor_set(x_485, 13, x_472);
lean_ctor_set(x_485, 14, x_473);
lean_ctor_set(x_485, 15, x_475);
lean_ctor_set(x_485, 16, x_476);
lean_ctor_set(x_485, 17, x_477);
lean_ctor_set(x_485, 18, x_478);
lean_ctor_set(x_485, 19, x_479);
lean_ctor_set(x_485, 20, x_480);
lean_ctor_set_uint8(x_485, sizeof(void*)*21, x_474);
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
x_488 = lean_st_ref_set(x_218, x_487, x_274);
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
lean_inc_ref(x_212);
x_492 = l_Int_Linear_Poly_mul(x_212, x_491);
lean_dec(x_491);
x_493 = lean_int_mul(x_269, x_210);
lean_dec(x_269);
lean_inc_ref(x_261);
x_494 = l_Int_Linear_Poly_mul(x_261, x_493);
lean_dec(x_493);
x_495 = lean_int_mul(x_210, x_258);
lean_dec(x_258);
lean_dec(x_210);
x_496 = l_Int_Linear_Poly_combine(x_492, x_494);
lean_inc(x_267);
lean_ctor_set(x_256, 2, x_496);
lean_ctor_set(x_256, 1, x_217);
lean_ctor_set(x_256, 0, x_267);
lean_inc(x_255);
lean_inc_ref(x_222);
if (lean_is_scalar(x_490)) {
 x_497 = lean_alloc_ctor(4, 2, 0);
} else {
 x_497 = x_490;
 lean_ctor_set_tag(x_497, 4);
}
lean_ctor_set(x_497, 0, x_222);
lean_ctor_set(x_497, 1, x_255);
x_498 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_498, 0, x_495);
lean_ctor_set(x_498, 1, x_256);
lean_ctor_set(x_498, 2, x_497);
lean_inc(x_216);
lean_inc_ref(x_219);
lean_inc(x_209);
lean_inc_ref(x_211);
lean_inc(x_214);
lean_inc_ref(x_215);
lean_inc(x_213);
lean_inc(x_218);
x_499 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_498, x_218, x_213, x_215, x_214, x_211, x_209, x_219, x_216, x_489);
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
x_502 = l_Int_Linear_Poly_mul(x_212, x_260);
lean_dec(x_260);
x_503 = lean_int_neg(x_220);
lean_dec(x_220);
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
lean_ctor_set(x_506, 0, x_222);
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
x_2 = x_218;
x_3 = x_213;
x_4 = x_215;
x_5 = x_214;
x_6 = x_211;
x_7 = x_209;
x_8 = x_219;
x_9 = x_216;
x_10 = x_500;
goto _start;
}
else
{
lean_dec(x_267);
lean_dec_ref(x_261);
lean_dec(x_260);
lean_dec(x_255);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec(x_209);
return x_499;
}
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; uint8_t x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; uint8_t x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_510 = lean_ctor_get(x_256, 0);
x_511 = lean_ctor_get(x_256, 2);
lean_inc(x_511);
lean_inc(x_510);
lean_dec(x_256);
x_512 = lean_int_mul(x_220, x_258);
x_513 = lean_int_mul(x_510, x_210);
x_514 = l_Lean_Meta_Grind_Arith_gcdExt(x_512, x_513);
lean_dec(x_513);
lean_dec(x_512);
x_515 = lean_ctor_get(x_514, 1);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 0);
lean_inc(x_516);
lean_dec_ref(x_514);
x_517 = lean_ctor_get(x_515, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_515, 1);
lean_inc(x_518);
lean_dec(x_515);
x_519 = lean_st_ref_take(x_218, x_221);
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_520, 14);
lean_inc_ref(x_521);
x_522 = lean_ctor_get(x_521, 1);
lean_inc_ref(x_522);
x_523 = lean_ctor_get(x_519, 1);
lean_inc(x_523);
lean_dec_ref(x_519);
x_524 = lean_ctor_get(x_520, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_520, 1);
lean_inc_ref(x_525);
x_526 = lean_ctor_get(x_520, 2);
lean_inc_ref(x_526);
x_527 = lean_ctor_get(x_520, 3);
lean_inc_ref(x_527);
x_528 = lean_ctor_get(x_520, 4);
lean_inc_ref(x_528);
x_529 = lean_ctor_get(x_520, 5);
lean_inc_ref(x_529);
x_530 = lean_ctor_get(x_520, 6);
lean_inc_ref(x_530);
x_531 = lean_ctor_get(x_520, 7);
lean_inc_ref(x_531);
x_532 = lean_ctor_get_uint8(x_520, sizeof(void*)*16);
x_533 = lean_ctor_get(x_520, 8);
lean_inc(x_533);
x_534 = lean_ctor_get(x_520, 9);
lean_inc_ref(x_534);
x_535 = lean_ctor_get(x_520, 10);
lean_inc_ref(x_535);
x_536 = lean_ctor_get(x_520, 11);
lean_inc_ref(x_536);
x_537 = lean_ctor_get(x_520, 12);
lean_inc_ref(x_537);
x_538 = lean_ctor_get(x_520, 13);
lean_inc_ref(x_538);
x_539 = lean_ctor_get(x_520, 15);
lean_inc_ref(x_539);
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
lean_inc_ref(x_541);
x_542 = lean_ctor_get(x_521, 2);
lean_inc_ref(x_542);
x_543 = lean_ctor_get(x_521, 3);
lean_inc_ref(x_543);
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
lean_inc_ref(x_545);
x_546 = lean_ctor_get(x_522, 1);
lean_inc_ref(x_546);
x_547 = lean_ctor_get(x_522, 2);
lean_inc_ref(x_547);
x_548 = lean_ctor_get(x_522, 3);
lean_inc_ref(x_548);
x_549 = lean_ctor_get(x_522, 4);
lean_inc_ref(x_549);
x_550 = lean_ctor_get(x_522, 5);
lean_inc_ref(x_550);
x_551 = lean_ctor_get(x_522, 6);
lean_inc_ref(x_551);
x_552 = lean_ctor_get(x_522, 7);
lean_inc_ref(x_552);
x_553 = lean_ctor_get(x_522, 8);
lean_inc_ref(x_553);
x_554 = lean_ctor_get(x_522, 9);
lean_inc_ref(x_554);
x_555 = lean_ctor_get(x_522, 10);
lean_inc_ref(x_555);
x_556 = lean_ctor_get(x_522, 11);
lean_inc(x_556);
x_557 = lean_ctor_get(x_522, 12);
lean_inc_ref(x_557);
x_558 = lean_ctor_get(x_522, 13);
lean_inc_ref(x_558);
x_559 = lean_ctor_get(x_522, 14);
lean_inc(x_559);
x_560 = lean_ctor_get_uint8(x_522, sizeof(void*)*21);
x_561 = lean_ctor_get(x_522, 15);
lean_inc(x_561);
x_562 = lean_ctor_get(x_522, 16);
lean_inc_ref(x_562);
x_563 = lean_ctor_get(x_522, 17);
lean_inc_ref(x_563);
x_564 = lean_ctor_get(x_522, 18);
lean_inc_ref(x_564);
x_565 = lean_ctor_get(x_522, 19);
lean_inc_ref(x_565);
x_566 = lean_ctor_get(x_522, 20);
lean_inc_ref(x_566);
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
x_570 = l_Lean_PersistentArray_set___redArg(x_551, x_217, x_569);
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
lean_ctor_set(x_571, 6, x_570);
lean_ctor_set(x_571, 7, x_552);
lean_ctor_set(x_571, 8, x_553);
lean_ctor_set(x_571, 9, x_554);
lean_ctor_set(x_571, 10, x_555);
lean_ctor_set(x_571, 11, x_556);
lean_ctor_set(x_571, 12, x_557);
lean_ctor_set(x_571, 13, x_558);
lean_ctor_set(x_571, 14, x_559);
lean_ctor_set(x_571, 15, x_561);
lean_ctor_set(x_571, 16, x_562);
lean_ctor_set(x_571, 17, x_563);
lean_ctor_set(x_571, 18, x_564);
lean_ctor_set(x_571, 19, x_565);
lean_ctor_set(x_571, 20, x_566);
lean_ctor_set_uint8(x_571, sizeof(void*)*21, x_560);
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
x_574 = lean_st_ref_set(x_218, x_573, x_523);
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
lean_inc_ref(x_212);
x_578 = l_Int_Linear_Poly_mul(x_212, x_577);
lean_dec(x_577);
x_579 = lean_int_mul(x_518, x_210);
lean_dec(x_518);
lean_inc_ref(x_511);
x_580 = l_Int_Linear_Poly_mul(x_511, x_579);
lean_dec(x_579);
x_581 = lean_int_mul(x_210, x_258);
lean_dec(x_258);
lean_dec(x_210);
x_582 = l_Int_Linear_Poly_combine(x_578, x_580);
lean_inc(x_516);
x_583 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_583, 0, x_516);
lean_ctor_set(x_583, 1, x_217);
lean_ctor_set(x_583, 2, x_582);
lean_inc(x_255);
lean_inc_ref(x_222);
if (lean_is_scalar(x_576)) {
 x_584 = lean_alloc_ctor(4, 2, 0);
} else {
 x_584 = x_576;
 lean_ctor_set_tag(x_584, 4);
}
lean_ctor_set(x_584, 0, x_222);
lean_ctor_set(x_584, 1, x_255);
x_585 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_585, 0, x_581);
lean_ctor_set(x_585, 1, x_583);
lean_ctor_set(x_585, 2, x_584);
lean_inc(x_216);
lean_inc_ref(x_219);
lean_inc(x_209);
lean_inc_ref(x_211);
lean_inc(x_214);
lean_inc_ref(x_215);
lean_inc(x_213);
lean_inc(x_218);
x_586 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_585, x_218, x_213, x_215, x_214, x_211, x_209, x_219, x_216, x_575);
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
x_589 = l_Int_Linear_Poly_mul(x_212, x_510);
lean_dec(x_510);
x_590 = lean_int_neg(x_220);
lean_dec(x_220);
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
lean_ctor_set(x_593, 0, x_222);
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
x_2 = x_218;
x_3 = x_213;
x_4 = x_215;
x_5 = x_214;
x_6 = x_211;
x_7 = x_209;
x_8 = x_219;
x_9 = x_216;
x_10 = x_587;
goto _start;
}
else
{
lean_dec(x_516);
lean_dec_ref(x_511);
lean_dec(x_510);
lean_dec(x_255);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec(x_209);
return x_586;
}
}
}
}
}
}
else
{
uint8_t x_841; 
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
x_841 = !lean_is_exclusive(x_202);
if (x_841 == 0)
{
lean_object* x_842; lean_object* x_843; 
x_842 = lean_ctor_get(x_202, 0);
lean_dec(x_842);
x_843 = lean_box(0);
lean_ctor_set(x_202, 0, x_843);
return x_202;
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; 
x_844 = lean_ctor_get(x_202, 1);
lean_inc(x_844);
lean_dec(x_202);
x_845 = lean_box(0);
x_846 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_846, 0, x_845);
lean_ctor_set(x_846, 1, x_844);
return x_846;
}
}
}
else
{
lean_object* x_847; 
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
x_847 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_193, x_10);
return x_847;
}
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; uint8_t x_859; lean_object* x_860; uint8_t x_861; lean_object* x_862; uint8_t x_863; 
x_848 = lean_ctor_get(x_8, 0);
x_849 = lean_ctor_get(x_8, 1);
x_850 = lean_ctor_get(x_8, 2);
x_851 = lean_ctor_get(x_8, 3);
x_852 = lean_ctor_get(x_8, 4);
x_853 = lean_ctor_get(x_8, 5);
x_854 = lean_ctor_get(x_8, 6);
x_855 = lean_ctor_get(x_8, 7);
x_856 = lean_ctor_get(x_8, 8);
x_857 = lean_ctor_get(x_8, 9);
x_858 = lean_ctor_get(x_8, 10);
x_859 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_860 = lean_ctor_get(x_8, 11);
x_861 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_862 = lean_ctor_get(x_8, 12);
lean_inc(x_862);
lean_inc(x_860);
lean_inc(x_858);
lean_inc(x_857);
lean_inc(x_856);
lean_inc(x_855);
lean_inc(x_854);
lean_inc(x_853);
lean_inc(x_852);
lean_inc(x_851);
lean_inc(x_850);
lean_inc(x_849);
lean_inc(x_848);
lean_dec(x_8);
x_863 = lean_nat_dec_eq(x_851, x_852);
if (x_863 == 0)
{
lean_object* x_864; lean_object* x_865; uint8_t x_866; 
x_864 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
x_866 = lean_unbox(x_865);
lean_dec(x_865);
if (x_866 == 0)
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; uint8_t x_1092; 
x_867 = lean_ctor_get(x_864, 1);
lean_inc(x_867);
lean_dec_ref(x_864);
x_868 = lean_unsigned_to_nat(1u);
x_869 = lean_nat_add(x_851, x_868);
lean_dec(x_851);
x_870 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_870, 0, x_848);
lean_ctor_set(x_870, 1, x_849);
lean_ctor_set(x_870, 2, x_850);
lean_ctor_set(x_870, 3, x_869);
lean_ctor_set(x_870, 4, x_852);
lean_ctor_set(x_870, 5, x_853);
lean_ctor_set(x_870, 6, x_854);
lean_ctor_set(x_870, 7, x_855);
lean_ctor_set(x_870, 8, x_856);
lean_ctor_set(x_870, 9, x_857);
lean_ctor_set(x_870, 10, x_858);
lean_ctor_set(x_870, 11, x_860);
lean_ctor_set(x_870, 12, x_862);
lean_ctor_set_uint8(x_870, sizeof(void*)*13, x_859);
lean_ctor_set_uint8(x_870, sizeof(void*)*13 + 1, x_861);
x_996 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_997 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_996, x_870, x_867);
x_998 = lean_ctor_get(x_997, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_997, 1);
lean_inc(x_999);
if (lean_is_exclusive(x_997)) {
 lean_ctor_release(x_997, 0);
 lean_ctor_release(x_997, 1);
 x_1000 = x_997;
} else {
 lean_dec_ref(x_997);
 x_1000 = lean_box(0);
}
x_1001 = lean_box(0);
x_1092 = lean_unbox(x_998);
lean_dec(x_998);
if (x_1092 == 0)
{
lean_dec(x_1000);
x_1026 = x_2;
x_1027 = x_3;
x_1028 = x_4;
x_1029 = x_5;
x_1030 = x_6;
x_1031 = x_7;
x_1032 = x_870;
x_1033 = x_9;
x_1034 = x_999;
goto block_1091;
}
else
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
lean_inc_ref(x_1);
x_1093 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_999);
x_1094 = lean_ctor_get(x_1093, 0);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_1093, 1);
lean_inc(x_1095);
if (lean_is_exclusive(x_1093)) {
 lean_ctor_release(x_1093, 0);
 lean_ctor_release(x_1093, 1);
 x_1096 = x_1093;
} else {
 lean_dec_ref(x_1093);
 x_1096 = lean_box(0);
}
x_1097 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1096)) {
 x_1098 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1098 = x_1096;
 lean_ctor_set_tag(x_1098, 7);
}
lean_ctor_set(x_1098, 0, x_1097);
lean_ctor_set(x_1098, 1, x_1094);
if (lean_is_scalar(x_1000)) {
 x_1099 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1099 = x_1000;
 lean_ctor_set_tag(x_1099, 7);
}
lean_ctor_set(x_1099, 0, x_1098);
lean_ctor_set(x_1099, 1, x_1097);
x_1100 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_996, x_1099, x_6, x_7, x_870, x_9, x_1095);
x_1101 = lean_ctor_get(x_1100, 1);
lean_inc(x_1101);
lean_dec_ref(x_1100);
x_1026 = x_2;
x_1027 = x_3;
x_1028 = x_4;
x_1029 = x_5;
x_1030 = x_6;
x_1031 = x_7;
x_1032 = x_870;
x_1033 = x_9;
x_1034 = x_1101;
goto block_1091;
}
block_995:
{
if (lean_obj_tag(x_886) == 0)
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; uint8_t x_890; 
lean_dec(x_883);
lean_dec_ref(x_878);
lean_dec(x_877);
lean_dec(x_876);
lean_dec_ref(x_875);
lean_dec(x_873);
x_887 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_888 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_887, x_882, x_884);
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
x_890 = lean_unbox(x_889);
lean_dec(x_889);
if (x_890 == 0)
{
lean_object* x_891; 
x_891 = lean_ctor_get(x_888, 1);
lean_inc(x_891);
lean_dec_ref(x_888);
x_11 = x_871;
x_12 = x_880;
x_13 = x_885;
x_14 = x_881;
x_15 = x_874;
x_16 = x_872;
x_17 = x_882;
x_18 = x_879;
x_19 = x_891;
goto block_163;
}
else
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
x_892 = lean_ctor_get(x_888, 1);
lean_inc(x_892);
if (lean_is_exclusive(x_888)) {
 lean_ctor_release(x_888, 0);
 lean_ctor_release(x_888, 1);
 x_893 = x_888;
} else {
 lean_dec_ref(x_888);
 x_893 = lean_box(0);
}
lean_inc_ref(x_885);
x_894 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_885, x_881, x_892);
x_895 = lean_ctor_get(x_894, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_894, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 lean_ctor_release(x_894, 1);
 x_897 = x_894;
} else {
 lean_dec_ref(x_894);
 x_897 = lean_box(0);
}
x_898 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_897)) {
 x_899 = lean_alloc_ctor(7, 2, 0);
} else {
 x_899 = x_897;
 lean_ctor_set_tag(x_899, 7);
}
lean_ctor_set(x_899, 0, x_898);
lean_ctor_set(x_899, 1, x_895);
if (lean_is_scalar(x_893)) {
 x_900 = lean_alloc_ctor(7, 2, 0);
} else {
 x_900 = x_893;
 lean_ctor_set_tag(x_900, 7);
}
lean_ctor_set(x_900, 0, x_899);
lean_ctor_set(x_900, 1, x_898);
x_901 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_887, x_900, x_874, x_872, x_882, x_879, x_896);
x_902 = lean_ctor_get(x_901, 1);
lean_inc(x_902);
lean_dec_ref(x_901);
x_11 = x_871;
x_12 = x_880;
x_13 = x_885;
x_14 = x_881;
x_15 = x_874;
x_16 = x_872;
x_17 = x_882;
x_18 = x_879;
x_19 = x_902;
goto block_163;
}
}
else
{
lean_object* x_903; lean_object* x_904; 
lean_dec_ref(x_871);
x_903 = lean_ctor_get(x_886, 0);
lean_inc(x_903);
lean_dec_ref(x_886);
x_904 = lean_ctor_get(x_903, 1);
lean_inc_ref(x_904);
if (lean_obj_tag(x_904) == 0)
{
lean_object* x_905; 
lean_dec_ref(x_904);
lean_dec_ref(x_885);
lean_dec(x_883);
lean_dec(x_880);
lean_dec_ref(x_878);
lean_dec(x_877);
lean_dec(x_876);
lean_dec_ref(x_875);
lean_dec(x_873);
x_905 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_903, x_881, x_874, x_872, x_882, x_879, x_884);
lean_dec(x_879);
lean_dec_ref(x_882);
lean_dec(x_872);
lean_dec_ref(x_874);
lean_dec(x_881);
return x_905;
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; uint8_t x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; uint8_t x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; uint8_t x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_906 = lean_ctor_get(x_903, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_904, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_904, 2);
lean_inc_ref(x_908);
if (lean_is_exclusive(x_904)) {
 lean_ctor_release(x_904, 0);
 lean_ctor_release(x_904, 1);
 lean_ctor_release(x_904, 2);
 x_909 = x_904;
} else {
 lean_dec_ref(x_904);
 x_909 = lean_box(0);
}
x_910 = lean_int_mul(x_883, x_906);
x_911 = lean_int_mul(x_907, x_873);
x_912 = l_Lean_Meta_Grind_Arith_gcdExt(x_910, x_911);
lean_dec(x_911);
lean_dec(x_910);
x_913 = lean_ctor_get(x_912, 1);
lean_inc(x_913);
x_914 = lean_ctor_get(x_912, 0);
lean_inc(x_914);
lean_dec_ref(x_912);
x_915 = lean_ctor_get(x_913, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_913, 1);
lean_inc(x_916);
lean_dec(x_913);
x_917 = lean_st_ref_take(x_881, x_884);
x_918 = lean_ctor_get(x_917, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_918, 14);
lean_inc_ref(x_919);
x_920 = lean_ctor_get(x_919, 1);
lean_inc_ref(x_920);
x_921 = lean_ctor_get(x_917, 1);
lean_inc(x_921);
lean_dec_ref(x_917);
x_922 = lean_ctor_get(x_918, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_918, 1);
lean_inc_ref(x_923);
x_924 = lean_ctor_get(x_918, 2);
lean_inc_ref(x_924);
x_925 = lean_ctor_get(x_918, 3);
lean_inc_ref(x_925);
x_926 = lean_ctor_get(x_918, 4);
lean_inc_ref(x_926);
x_927 = lean_ctor_get(x_918, 5);
lean_inc_ref(x_927);
x_928 = lean_ctor_get(x_918, 6);
lean_inc_ref(x_928);
x_929 = lean_ctor_get(x_918, 7);
lean_inc_ref(x_929);
x_930 = lean_ctor_get_uint8(x_918, sizeof(void*)*16);
x_931 = lean_ctor_get(x_918, 8);
lean_inc(x_931);
x_932 = lean_ctor_get(x_918, 9);
lean_inc_ref(x_932);
x_933 = lean_ctor_get(x_918, 10);
lean_inc_ref(x_933);
x_934 = lean_ctor_get(x_918, 11);
lean_inc_ref(x_934);
x_935 = lean_ctor_get(x_918, 12);
lean_inc_ref(x_935);
x_936 = lean_ctor_get(x_918, 13);
lean_inc_ref(x_936);
x_937 = lean_ctor_get(x_918, 15);
lean_inc_ref(x_937);
if (lean_is_exclusive(x_918)) {
 lean_ctor_release(x_918, 0);
 lean_ctor_release(x_918, 1);
 lean_ctor_release(x_918, 2);
 lean_ctor_release(x_918, 3);
 lean_ctor_release(x_918, 4);
 lean_ctor_release(x_918, 5);
 lean_ctor_release(x_918, 6);
 lean_ctor_release(x_918, 7);
 lean_ctor_release(x_918, 8);
 lean_ctor_release(x_918, 9);
 lean_ctor_release(x_918, 10);
 lean_ctor_release(x_918, 11);
 lean_ctor_release(x_918, 12);
 lean_ctor_release(x_918, 13);
 lean_ctor_release(x_918, 14);
 lean_ctor_release(x_918, 15);
 x_938 = x_918;
} else {
 lean_dec_ref(x_918);
 x_938 = lean_box(0);
}
x_939 = lean_ctor_get(x_919, 0);
lean_inc_ref(x_939);
x_940 = lean_ctor_get(x_919, 2);
lean_inc_ref(x_940);
x_941 = lean_ctor_get(x_919, 3);
lean_inc_ref(x_941);
if (lean_is_exclusive(x_919)) {
 lean_ctor_release(x_919, 0);
 lean_ctor_release(x_919, 1);
 lean_ctor_release(x_919, 2);
 lean_ctor_release(x_919, 3);
 x_942 = x_919;
} else {
 lean_dec_ref(x_919);
 x_942 = lean_box(0);
}
x_943 = lean_ctor_get(x_920, 0);
lean_inc_ref(x_943);
x_944 = lean_ctor_get(x_920, 1);
lean_inc_ref(x_944);
x_945 = lean_ctor_get(x_920, 2);
lean_inc_ref(x_945);
x_946 = lean_ctor_get(x_920, 3);
lean_inc_ref(x_946);
x_947 = lean_ctor_get(x_920, 4);
lean_inc_ref(x_947);
x_948 = lean_ctor_get(x_920, 5);
lean_inc_ref(x_948);
x_949 = lean_ctor_get(x_920, 6);
lean_inc_ref(x_949);
x_950 = lean_ctor_get(x_920, 7);
lean_inc_ref(x_950);
x_951 = lean_ctor_get(x_920, 8);
lean_inc_ref(x_951);
x_952 = lean_ctor_get(x_920, 9);
lean_inc_ref(x_952);
x_953 = lean_ctor_get(x_920, 10);
lean_inc_ref(x_953);
x_954 = lean_ctor_get(x_920, 11);
lean_inc(x_954);
x_955 = lean_ctor_get(x_920, 12);
lean_inc_ref(x_955);
x_956 = lean_ctor_get(x_920, 13);
lean_inc_ref(x_956);
x_957 = lean_ctor_get(x_920, 14);
lean_inc(x_957);
x_958 = lean_ctor_get_uint8(x_920, sizeof(void*)*21);
x_959 = lean_ctor_get(x_920, 15);
lean_inc(x_959);
x_960 = lean_ctor_get(x_920, 16);
lean_inc_ref(x_960);
x_961 = lean_ctor_get(x_920, 17);
lean_inc_ref(x_961);
x_962 = lean_ctor_get(x_920, 18);
lean_inc_ref(x_962);
x_963 = lean_ctor_get(x_920, 19);
lean_inc_ref(x_963);
x_964 = lean_ctor_get(x_920, 20);
lean_inc_ref(x_964);
x_965 = lean_ctor_get_uint8(x_920, sizeof(void*)*21 + 1);
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
 lean_ctor_release(x_920, 16);
 lean_ctor_release(x_920, 17);
 lean_ctor_release(x_920, 18);
 lean_ctor_release(x_920, 19);
 lean_ctor_release(x_920, 20);
 x_966 = x_920;
} else {
 lean_dec_ref(x_920);
 x_966 = lean_box(0);
}
x_967 = lean_box(0);
x_968 = l_Lean_PersistentArray_set___redArg(x_949, x_880, x_967);
if (lean_is_scalar(x_966)) {
 x_969 = lean_alloc_ctor(0, 21, 2);
} else {
 x_969 = x_966;
}
lean_ctor_set(x_969, 0, x_943);
lean_ctor_set(x_969, 1, x_944);
lean_ctor_set(x_969, 2, x_945);
lean_ctor_set(x_969, 3, x_946);
lean_ctor_set(x_969, 4, x_947);
lean_ctor_set(x_969, 5, x_948);
lean_ctor_set(x_969, 6, x_968);
lean_ctor_set(x_969, 7, x_950);
lean_ctor_set(x_969, 8, x_951);
lean_ctor_set(x_969, 9, x_952);
lean_ctor_set(x_969, 10, x_953);
lean_ctor_set(x_969, 11, x_954);
lean_ctor_set(x_969, 12, x_955);
lean_ctor_set(x_969, 13, x_956);
lean_ctor_set(x_969, 14, x_957);
lean_ctor_set(x_969, 15, x_959);
lean_ctor_set(x_969, 16, x_960);
lean_ctor_set(x_969, 17, x_961);
lean_ctor_set(x_969, 18, x_962);
lean_ctor_set(x_969, 19, x_963);
lean_ctor_set(x_969, 20, x_964);
lean_ctor_set_uint8(x_969, sizeof(void*)*21, x_958);
lean_ctor_set_uint8(x_969, sizeof(void*)*21 + 1, x_965);
if (lean_is_scalar(x_942)) {
 x_970 = lean_alloc_ctor(0, 4, 0);
} else {
 x_970 = x_942;
}
lean_ctor_set(x_970, 0, x_939);
lean_ctor_set(x_970, 1, x_969);
lean_ctor_set(x_970, 2, x_940);
lean_ctor_set(x_970, 3, x_941);
if (lean_is_scalar(x_938)) {
 x_971 = lean_alloc_ctor(0, 16, 1);
} else {
 x_971 = x_938;
}
lean_ctor_set(x_971, 0, x_922);
lean_ctor_set(x_971, 1, x_923);
lean_ctor_set(x_971, 2, x_924);
lean_ctor_set(x_971, 3, x_925);
lean_ctor_set(x_971, 4, x_926);
lean_ctor_set(x_971, 5, x_927);
lean_ctor_set(x_971, 6, x_928);
lean_ctor_set(x_971, 7, x_929);
lean_ctor_set(x_971, 8, x_931);
lean_ctor_set(x_971, 9, x_932);
lean_ctor_set(x_971, 10, x_933);
lean_ctor_set(x_971, 11, x_934);
lean_ctor_set(x_971, 12, x_935);
lean_ctor_set(x_971, 13, x_936);
lean_ctor_set(x_971, 14, x_970);
lean_ctor_set(x_971, 15, x_937);
lean_ctor_set_uint8(x_971, sizeof(void*)*16, x_930);
x_972 = lean_st_ref_set(x_881, x_971, x_921);
x_973 = lean_ctor_get(x_972, 1);
lean_inc(x_973);
if (lean_is_exclusive(x_972)) {
 lean_ctor_release(x_972, 0);
 lean_ctor_release(x_972, 1);
 x_974 = x_972;
} else {
 lean_dec_ref(x_972);
 x_974 = lean_box(0);
}
x_975 = lean_int_mul(x_915, x_906);
lean_dec(x_915);
lean_inc_ref(x_875);
x_976 = l_Int_Linear_Poly_mul(x_875, x_975);
lean_dec(x_975);
x_977 = lean_int_mul(x_916, x_873);
lean_dec(x_916);
lean_inc_ref(x_908);
x_978 = l_Int_Linear_Poly_mul(x_908, x_977);
lean_dec(x_977);
x_979 = lean_int_mul(x_873, x_906);
lean_dec(x_906);
lean_dec(x_873);
x_980 = l_Int_Linear_Poly_combine(x_976, x_978);
lean_inc(x_914);
if (lean_is_scalar(x_909)) {
 x_981 = lean_alloc_ctor(1, 3, 0);
} else {
 x_981 = x_909;
}
lean_ctor_set(x_981, 0, x_914);
lean_ctor_set(x_981, 1, x_880);
lean_ctor_set(x_981, 2, x_980);
lean_inc(x_903);
lean_inc_ref(x_885);
if (lean_is_scalar(x_974)) {
 x_982 = lean_alloc_ctor(4, 2, 0);
} else {
 x_982 = x_974;
 lean_ctor_set_tag(x_982, 4);
}
lean_ctor_set(x_982, 0, x_885);
lean_ctor_set(x_982, 1, x_903);
x_983 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_983, 0, x_979);
lean_ctor_set(x_983, 1, x_981);
lean_ctor_set(x_983, 2, x_982);
lean_inc(x_879);
lean_inc_ref(x_882);
lean_inc(x_872);
lean_inc_ref(x_874);
lean_inc(x_877);
lean_inc_ref(x_878);
lean_inc(x_876);
lean_inc(x_881);
x_984 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_983, x_881, x_876, x_878, x_877, x_874, x_872, x_882, x_879, x_973);
if (lean_obj_tag(x_984) == 0)
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_985 = lean_ctor_get(x_984, 1);
lean_inc(x_985);
if (lean_is_exclusive(x_984)) {
 lean_ctor_release(x_984, 0);
 lean_ctor_release(x_984, 1);
 x_986 = x_984;
} else {
 lean_dec_ref(x_984);
 x_986 = lean_box(0);
}
x_987 = l_Int_Linear_Poly_mul(x_875, x_907);
lean_dec(x_907);
x_988 = lean_int_neg(x_883);
lean_dec(x_883);
x_989 = l_Int_Linear_Poly_mul(x_908, x_988);
lean_dec(x_988);
x_990 = l_Int_Linear_Poly_combine(x_987, x_989);
lean_inc(x_903);
if (lean_is_scalar(x_986)) {
 x_991 = lean_alloc_ctor(5, 2, 0);
} else {
 x_991 = x_986;
 lean_ctor_set_tag(x_991, 5);
}
lean_ctor_set(x_991, 0, x_885);
lean_ctor_set(x_991, 1, x_903);
if (lean_is_exclusive(x_903)) {
 lean_ctor_release(x_903, 0);
 lean_ctor_release(x_903, 1);
 lean_ctor_release(x_903, 2);
 x_992 = x_903;
} else {
 lean_dec_ref(x_903);
 x_992 = lean_box(0);
}
if (lean_is_scalar(x_992)) {
 x_993 = lean_alloc_ctor(0, 3, 0);
} else {
 x_993 = x_992;
}
lean_ctor_set(x_993, 0, x_914);
lean_ctor_set(x_993, 1, x_990);
lean_ctor_set(x_993, 2, x_991);
x_1 = x_993;
x_2 = x_881;
x_3 = x_876;
x_4 = x_878;
x_5 = x_877;
x_6 = x_874;
x_7 = x_872;
x_8 = x_882;
x_9 = x_879;
x_10 = x_985;
goto _start;
}
else
{
lean_dec(x_914);
lean_dec_ref(x_908);
lean_dec(x_907);
lean_dec(x_903);
lean_dec_ref(x_885);
lean_dec(x_883);
lean_dec_ref(x_882);
lean_dec(x_881);
lean_dec(x_879);
lean_dec_ref(x_878);
lean_dec(x_877);
lean_dec(x_876);
lean_dec_ref(x_875);
lean_dec_ref(x_874);
lean_dec(x_872);
return x_984;
}
}
}
}
block_1025:
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; uint8_t x_1022; 
x_1017 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_1008, x_1016);
x_1018 = lean_ctor_get(x_1017, 0);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_1018, 6);
lean_inc_ref(x_1019);
lean_dec(x_1018);
x_1020 = lean_ctor_get(x_1017, 1);
lean_inc(x_1020);
lean_dec_ref(x_1017);
x_1021 = lean_ctor_get(x_1019, 2);
lean_inc(x_1021);
x_1022 = lean_nat_dec_lt(x_1007, x_1021);
lean_dec(x_1021);
if (x_1022 == 0)
{
lean_object* x_1023; 
lean_dec_ref(x_1019);
x_1023 = l_outOfBounds___redArg(x_1001);
x_871 = x_1002;
x_872 = x_1013;
x_873 = x_1004;
x_874 = x_1012;
x_875 = x_1005;
x_876 = x_1009;
x_877 = x_1011;
x_878 = x_1010;
x_879 = x_1015;
x_880 = x_1007;
x_881 = x_1008;
x_882 = x_1014;
x_883 = x_1003;
x_884 = x_1020;
x_885 = x_1006;
x_886 = x_1023;
goto block_995;
}
else
{
lean_object* x_1024; 
x_1024 = l_Lean_PersistentArray_get_x21___redArg(x_1001, x_1019, x_1007);
x_871 = x_1002;
x_872 = x_1013;
x_873 = x_1004;
x_874 = x_1012;
x_875 = x_1005;
x_876 = x_1009;
x_877 = x_1011;
x_878 = x_1010;
x_879 = x_1015;
x_880 = x_1007;
x_881 = x_1008;
x_882 = x_1014;
x_883 = x_1003;
x_884 = x_1020;
x_885 = x_1006;
x_886 = x_1024;
goto block_995;
}
}
block_1091:
{
lean_object* x_1035; lean_object* x_1036; 
x_1035 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_1032);
x_1036 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_1035, x_1026, x_1027, x_1028, x_1029, x_1030, x_1031, x_1032, x_1033, x_1034);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; uint8_t x_1041; 
x_1037 = lean_ctor_get(x_1036, 0);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_1036, 1);
lean_inc(x_1038);
lean_dec_ref(x_1036);
x_1039 = lean_ctor_get(x_1037, 0);
lean_inc(x_1039);
x_1040 = lean_ctor_get(x_1037, 1);
lean_inc_ref(x_1040);
lean_inc(x_1039);
x_1041 = l_Int_Linear_Poly_isUnsatDvd(x_1039, x_1040);
if (x_1041 == 0)
{
uint8_t x_1042; 
x_1042 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_1037);
if (x_1042 == 0)
{
if (lean_obj_tag(x_1040) == 0)
{
lean_object* x_1043; 
lean_dec_ref(x_1040);
lean_dec(x_1039);
lean_dec(x_1029);
lean_dec_ref(x_1028);
lean_dec(x_1027);
x_1043 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_1037, x_1026, x_1030, x_1031, x_1032, x_1033, x_1038);
lean_dec(x_1033);
lean_dec_ref(x_1032);
lean_dec(x_1031);
lean_dec_ref(x_1030);
lean_dec(x_1026);
return x_1043;
}
else
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; uint8_t x_1050; uint8_t x_1051; uint8_t x_1052; 
x_1044 = lean_ctor_get(x_1040, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1040, 1);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1040, 2);
lean_inc_ref(x_1046);
lean_inc(x_1037);
x_1047 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_1037, x_1026, x_1038);
x_1048 = lean_ctor_get(x_1047, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1047, 1);
lean_inc(x_1049);
lean_dec_ref(x_1047);
x_1050 = 0;
x_1051 = lean_unbox(x_1048);
lean_dec(x_1048);
x_1052 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_1051, x_1050);
if (x_1052 == 0)
{
x_1002 = x_1040;
x_1003 = x_1044;
x_1004 = x_1039;
x_1005 = x_1046;
x_1006 = x_1037;
x_1007 = x_1045;
x_1008 = x_1026;
x_1009 = x_1027;
x_1010 = x_1028;
x_1011 = x_1029;
x_1012 = x_1030;
x_1013 = x_1031;
x_1014 = x_1032;
x_1015 = x_1033;
x_1016 = x_1049;
goto block_1025;
}
else
{
lean_object* x_1053; lean_object* x_1054; 
x_1053 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_1045, x_1026, x_1049);
x_1054 = lean_ctor_get(x_1053, 1);
lean_inc(x_1054);
lean_dec_ref(x_1053);
x_1002 = x_1040;
x_1003 = x_1044;
x_1004 = x_1039;
x_1005 = x_1046;
x_1006 = x_1037;
x_1007 = x_1045;
x_1008 = x_1026;
x_1009 = x_1027;
x_1010 = x_1028;
x_1011 = x_1029;
x_1012 = x_1030;
x_1013 = x_1031;
x_1014 = x_1032;
x_1015 = x_1033;
x_1016 = x_1054;
goto block_1025;
}
}
}
else
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; uint8_t x_1058; 
lean_dec_ref(x_1040);
lean_dec(x_1039);
lean_dec(x_1029);
lean_dec_ref(x_1028);
lean_dec(x_1027);
x_1055 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_1056 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1055, x_1032, x_1038);
x_1057 = lean_ctor_get(x_1056, 0);
lean_inc(x_1057);
x_1058 = lean_unbox(x_1057);
lean_dec(x_1057);
if (x_1058 == 0)
{
lean_object* x_1059; 
lean_dec(x_1037);
lean_dec(x_1033);
lean_dec_ref(x_1032);
lean_dec(x_1031);
lean_dec_ref(x_1030);
lean_dec(x_1026);
x_1059 = lean_ctor_get(x_1056, 1);
lean_inc(x_1059);
lean_dec_ref(x_1056);
x_183 = x_1059;
goto block_186;
}
else
{
lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
x_1060 = lean_ctor_get(x_1056, 1);
lean_inc(x_1060);
if (lean_is_exclusive(x_1056)) {
 lean_ctor_release(x_1056, 0);
 lean_ctor_release(x_1056, 1);
 x_1061 = x_1056;
} else {
 lean_dec_ref(x_1056);
 x_1061 = lean_box(0);
}
x_1062 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1037, x_1026, x_1060);
lean_dec(x_1026);
x_1063 = lean_ctor_get(x_1062, 0);
lean_inc(x_1063);
x_1064 = lean_ctor_get(x_1062, 1);
lean_inc(x_1064);
if (lean_is_exclusive(x_1062)) {
 lean_ctor_release(x_1062, 0);
 lean_ctor_release(x_1062, 1);
 x_1065 = x_1062;
} else {
 lean_dec_ref(x_1062);
 x_1065 = lean_box(0);
}
x_1066 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1065)) {
 x_1067 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1067 = x_1065;
 lean_ctor_set_tag(x_1067, 7);
}
lean_ctor_set(x_1067, 0, x_1066);
lean_ctor_set(x_1067, 1, x_1063);
if (lean_is_scalar(x_1061)) {
 x_1068 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1068 = x_1061;
 lean_ctor_set_tag(x_1068, 7);
}
lean_ctor_set(x_1068, 0, x_1067);
lean_ctor_set(x_1068, 1, x_1066);
x_1069 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1055, x_1068, x_1030, x_1031, x_1032, x_1033, x_1064);
lean_dec(x_1033);
lean_dec_ref(x_1032);
lean_dec(x_1031);
lean_dec_ref(x_1030);
x_1070 = lean_ctor_get(x_1069, 1);
lean_inc(x_1070);
lean_dec_ref(x_1069);
x_183 = x_1070;
goto block_186;
}
}
}
else
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; uint8_t x_1074; 
lean_dec_ref(x_1040);
lean_dec(x_1039);
x_1071 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_1072 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_1071, x_1032, x_1038);
x_1073 = lean_ctor_get(x_1072, 0);
lean_inc(x_1073);
x_1074 = lean_unbox(x_1073);
lean_dec(x_1073);
if (x_1074 == 0)
{
lean_object* x_1075; 
x_1075 = lean_ctor_get(x_1072, 1);
lean_inc(x_1075);
lean_dec_ref(x_1072);
x_164 = x_1037;
x_165 = x_1026;
x_166 = x_1027;
x_167 = x_1028;
x_168 = x_1029;
x_169 = x_1030;
x_170 = x_1031;
x_171 = x_1032;
x_172 = x_1033;
x_173 = x_1075;
goto block_182;
}
else
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
x_1076 = lean_ctor_get(x_1072, 1);
lean_inc(x_1076);
if (lean_is_exclusive(x_1072)) {
 lean_ctor_release(x_1072, 0);
 lean_ctor_release(x_1072, 1);
 x_1077 = x_1072;
} else {
 lean_dec_ref(x_1072);
 x_1077 = lean_box(0);
}
lean_inc(x_1037);
x_1078 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1037, x_1026, x_1076);
x_1079 = lean_ctor_get(x_1078, 0);
lean_inc(x_1079);
x_1080 = lean_ctor_get(x_1078, 1);
lean_inc(x_1080);
if (lean_is_exclusive(x_1078)) {
 lean_ctor_release(x_1078, 0);
 lean_ctor_release(x_1078, 1);
 x_1081 = x_1078;
} else {
 lean_dec_ref(x_1078);
 x_1081 = lean_box(0);
}
x_1082 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
if (lean_is_scalar(x_1081)) {
 x_1083 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1083 = x_1081;
 lean_ctor_set_tag(x_1083, 7);
}
lean_ctor_set(x_1083, 0, x_1082);
lean_ctor_set(x_1083, 1, x_1079);
if (lean_is_scalar(x_1077)) {
 x_1084 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1084 = x_1077;
 lean_ctor_set_tag(x_1084, 7);
}
lean_ctor_set(x_1084, 0, x_1083);
lean_ctor_set(x_1084, 1, x_1082);
x_1085 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_1071, x_1084, x_1030, x_1031, x_1032, x_1033, x_1080);
x_1086 = lean_ctor_get(x_1085, 1);
lean_inc(x_1086);
lean_dec_ref(x_1085);
x_164 = x_1037;
x_165 = x_1026;
x_166 = x_1027;
x_167 = x_1028;
x_168 = x_1029;
x_169 = x_1030;
x_170 = x_1031;
x_171 = x_1032;
x_172 = x_1033;
x_173 = x_1086;
goto block_182;
}
}
}
else
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; 
lean_dec(x_1033);
lean_dec_ref(x_1032);
lean_dec(x_1031);
lean_dec_ref(x_1030);
lean_dec(x_1029);
lean_dec_ref(x_1028);
lean_dec(x_1027);
lean_dec(x_1026);
x_1087 = lean_ctor_get(x_1036, 0);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_1036, 1);
lean_inc(x_1088);
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 lean_ctor_release(x_1036, 1);
 x_1089 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1089 = lean_box(0);
}
if (lean_is_scalar(x_1089)) {
 x_1090 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1090 = x_1089;
}
lean_ctor_set(x_1090, 0, x_1087);
lean_ctor_set(x_1090, 1, x_1088);
return x_1090;
}
}
}
else
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
lean_dec_ref(x_862);
lean_dec(x_860);
lean_dec(x_858);
lean_dec(x_857);
lean_dec(x_856);
lean_dec(x_855);
lean_dec(x_854);
lean_dec(x_853);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_850);
lean_dec_ref(x_849);
lean_dec_ref(x_848);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1102 = lean_ctor_get(x_864, 1);
lean_inc(x_1102);
if (lean_is_exclusive(x_864)) {
 lean_ctor_release(x_864, 0);
 lean_ctor_release(x_864, 1);
 x_1103 = x_864;
} else {
 lean_dec_ref(x_864);
 x_1103 = lean_box(0);
}
x_1104 = lean_box(0);
if (lean_is_scalar(x_1103)) {
 x_1105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1105 = x_1103;
}
lean_ctor_set(x_1105, 0, x_1104);
lean_ctor_set(x_1105, 1, x_1102);
return x_1105;
}
}
else
{
lean_object* x_1106; 
lean_dec_ref(x_862);
lean_dec(x_860);
lean_dec(x_858);
lean_dec(x_857);
lean_dec(x_856);
lean_dec(x_855);
lean_dec(x_854);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_850);
lean_dec_ref(x_849);
lean_dec_ref(x_848);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1106 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_853, x_10);
return x_1106;
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
lean_ctor_set(x_33, 0, x_13);
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
lean_ctor_set(x_65, 0, x_13);
x_66 = l_Lean_PersistentArray_set___redArg(x_48, x_12, x_65);
lean_dec(x_12);
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
lean_ctor_set(x_100, 0, x_13);
x_101 = l_Lean_PersistentArray_set___redArg(x_82, x_12, x_100);
lean_dec(x_12);
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
lean_ctor_set(x_153, 0, x_13);
x_154 = l_Lean_PersistentArray_set___redArg(x_135, x_12, x_153);
lean_dec(x_12);
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
lean_dec_ref(x_13);
lean_dec(x_12);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; uint8_t x_23; 
lean_inc_ref(x_1);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_2);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_48);
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
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec_ref(x_60);
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
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec_ref(x_68);
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
lean_dec_ref(x_46);
x_71 = !lean_is_exclusive(x_47);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_47, 0);
lean_inc_ref(x_1);
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
lean_dec_ref(x_73);
lean_inc_ref(x_1);
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
lean_dec_ref(x_77);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_87 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec_ref(x_87);
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
lean_dec_ref(x_27);
x_104 = lean_ctor_get(x_73, 1);
lean_inc(x_104);
lean_dec_ref(x_73);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
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
lean_dec_ref(x_105);
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
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_inc_ref(x_1);
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
lean_dec_ref(x_119);
lean_inc_ref(x_1);
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
lean_dec_ref(x_123);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_131 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec_ref(x_131);
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
lean_dec_ref(x_27);
x_148 = lean_ctor_get(x_119, 1);
lean_inc(x_148);
lean_dec_ref(x_119);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
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
lean_dec_ref(x_149);
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
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Meta_isInstDvdNat___redArg(x_27, x_7, x_10);
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
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec(x_2);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_45);
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
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_46, 1);
x_52 = lean_ctor_get(x_46, 0);
lean_dec(x_52);
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
x_54 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_46, 7);
lean_ctor_set(x_46, 1, x_54);
lean_ctor_set(x_46, 0, x_53);
x_55 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_46);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Meta_Grind_reportIssue(x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
x_15 = x_58;
goto block_18;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_dec(x_46);
x_60 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
x_61 = l_Lean_indentExpr(x_1);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___redArg___closed__6;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Meta_Grind_reportIssue(x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_59);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec_ref(x_65);
x_15 = x_66;
goto block_18;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_43, 1);
lean_inc(x_67);
lean_dec_ref(x_43);
x_68 = lean_ctor_get(x_44, 0);
lean_inc(x_68);
lean_dec_ref(x_44);
lean_inc_ref(x_1);
x_69 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_68);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec_ref(x_69);
lean_inc_ref(x_1);
x_73 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
uint8_t x_76; 
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
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_73, 0);
lean_dec(x_77);
x_78 = lean_box(0);
lean_ctor_set(x_73, 0, x_78);
return x_73;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
lean_dec(x_73);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_73, 1);
lean_inc(x_82);
lean_dec_ref(x_73);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_83 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
x_86 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_87 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_84);
x_88 = l_Lean_mkApp3(x_86, x_24, x_21, x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Lean_Meta_Grind_pushNewFact(x_88, x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_85);
return x_90;
}
else
{
uint8_t x_91; 
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
x_91 = !lean_is_exclusive(x_83);
if (x_91 == 0)
{
return x_83;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_83, 0);
x_93 = lean_ctor_get(x_83, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_83);
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
x_95 = !lean_is_exclusive(x_73);
if (x_95 == 0)
{
return x_73;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_73, 0);
x_97 = lean_ctor_get(x_73, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_73);
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
x_99 = lean_ctor_get(x_69, 1);
lean_inc(x_99);
lean_dec_ref(x_69);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_24);
x_100 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_99);
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
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_21);
x_105 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec_ref(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
lean_inc_ref(x_1);
x_110 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_107);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_108);
x_113 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_108, x_111, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec_ref(x_113);
x_116 = l_Int_Linear_Expr_norm(x_114);
x_117 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
x_118 = l_Lean_mkApp6(x_117, x_24, x_21, x_103, x_108, x_104, x_109);
lean_inc(x_68);
x_119 = lean_nat_to_int(x_68);
x_120 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_118);
lean_ctor_set(x_120, 2, x_68);
lean_ctor_set(x_120, 3, x_114);
x_121 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_116);
lean_ctor_set(x_121, 2, x_120);
x_122 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_115);
return x_122;
}
else
{
uint8_t x_123; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_68);
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
x_123 = !lean_is_exclusive(x_113);
if (x_123 == 0)
{
return x_113;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_113, 0);
x_125 = lean_ctor_get(x_113, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_113);
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
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_68);
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
x_127 = !lean_is_exclusive(x_105);
if (x_127 == 0)
{
return x_105;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_105, 0);
x_129 = lean_ctor_get(x_105, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_105);
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
lean_dec(x_68);
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
x_131 = !lean_is_exclusive(x_100);
if (x_131 == 0)
{
return x_100;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_100, 0);
x_133 = lean_ctor_get(x_100, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_100);
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
lean_dec(x_68);
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
x_135 = !lean_is_exclusive(x_69);
if (x_135 == 0)
{
return x_69;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_69, 0);
x_137 = lean_ctor_get(x_69, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_69);
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
x_139 = !lean_is_exclusive(x_43);
if (x_139 == 0)
{
return x_43;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_43, 0);
x_141 = lean_ctor_get(x_43, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_43);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_10);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; uint8_t x_29; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec_ref(x_11);
lean_inc_ref(x_1);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2962_(lean_object* x_1) {
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
if (builtin) {res = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2962_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

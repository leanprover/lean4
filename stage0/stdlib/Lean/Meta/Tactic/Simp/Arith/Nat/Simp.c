// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Nat.Simp
// Imports: public import Lean.Meta.Tactic.Simp.Arith.Util public import Lean.Meta.Tactic.Simp.Arith.Nat.Basic import Lean.Meta.AppBuilder
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
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20;
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___lam__0___closed__0;
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__2;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__7;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5;
lean_object* l_Nat_Linear_PolyCnstr_norm(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__0;
uint8_t l_Nat_Linear_PolyCnstr_isUnsat(lean_object*);
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Nat_Linear_Poly_toExpr(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__6;
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3;
lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31;
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__4;
lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16;
lean_object* l_Nat_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32;
lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Nat_Linear_PolyCnstr_toExpr(lean_object*);
lean_object* l_Nat_Linear_ExprCnstr_toPoly(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23;
lean_object* l_Lean_Meta_Simp_Arith_withAbstractAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
lean_object* l_Nat_Linear_Expr_toPoly(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__26;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__1;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2;
uint8_t l_Nat_Linear_PolyCnstr_isValid(lean_object*);
uint8_t l_Nat_Linear_instBEqExpr_beq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__10;
lean_object* l_Lean_mkNatEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25;
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_of_toNormPoly_eq", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_eagerReflBoolTrue;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_true_of_isValid", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__9;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_false_of_isUnsat", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_1);
x_9 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(x_3, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc_ref(x_1);
x_11 = l_Nat_Linear_ExprCnstr_toPoly(x_1);
x_12 = l_Nat_Linear_PolyCnstr_norm(x_11);
x_13 = l_Nat_Linear_PolyCnstr_isUnsat(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Nat_Linear_PolyCnstr_isValid(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Nat_Linear_PolyCnstr_toExpr(x_12);
lean_inc_ref(x_15);
x_16 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(x_3, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_56; 
x_18 = lean_ctor_get(x_16, 0);
x_56 = lean_expr_eqv(x_18, x_10);
if (x_56 == 0)
{
lean_free_object(x_16);
goto block_55;
}
else
{
if (x_14 == 0)
{
lean_object* x_57; 
lean_dec(x_18);
lean_dec_ref(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_57 = lean_box(0);
lean_ctor_set(x_16, 0, x_57);
return x_16;
}
else
{
lean_free_object(x_16);
goto block_55;
}
}
block_55:
{
lean_object* x_19; 
x_19 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__0;
x_23 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__1;
x_24 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__2;
x_25 = l_Lean_Name_mkStr4(x_2, x_22, x_23, x_24);
x_26 = lean_box(0);
x_27 = l_Lean_mkConst(x_25, x_26);
x_28 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
x_29 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_15);
x_30 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__3;
x_31 = l_Lean_mkApp4(x_27, x_21, x_28, x_29, x_30);
lean_inc(x_18);
x_32 = l_Lean_mkPropEq(x_10, x_18);
x_33 = l_Lean_Meta_mkExpectedPropHint(x_31, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_36 = lean_ctor_get(x_19, 0);
lean_inc(x_36);
lean_dec(x_19);
x_37 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__0;
x_38 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__1;
x_39 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__2;
x_40 = l_Lean_Name_mkStr4(x_2, x_37, x_38, x_39);
x_41 = lean_box(0);
x_42 = l_Lean_mkConst(x_40, x_41);
x_43 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
x_44 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_15);
x_45 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__3;
x_46 = l_Lean_mkApp4(x_42, x_36, x_43, x_44, x_45);
lean_inc(x_18);
x_47 = l_Lean_mkPropEq(x_10, x_18);
x_48 = l_Lean_Meta_mkExpectedPropHint(x_46, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_18);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_18);
lean_dec_ref(x_15);
lean_dec(x_10);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_52 = !lean_is_exclusive(x_19);
if (x_52 == 0)
{
return x_19;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_19, 0);
lean_inc(x_53);
lean_dec(x_19);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_58; uint8_t x_81; 
x_58 = lean_ctor_get(x_16, 0);
lean_inc(x_58);
lean_dec(x_16);
x_81 = lean_expr_eqv(x_58, x_10);
if (x_81 == 0)
{
goto block_80;
}
else
{
if (x_14 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_58);
lean_dec_ref(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
else
{
goto block_80;
}
}
block_80:
{
lean_object* x_59; 
x_59 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__0;
x_63 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__1;
x_64 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__2;
x_65 = l_Lean_Name_mkStr4(x_2, x_62, x_63, x_64);
x_66 = lean_box(0);
x_67 = l_Lean_mkConst(x_65, x_66);
x_68 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
x_69 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_15);
x_70 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__3;
x_71 = l_Lean_mkApp4(x_67, x_60, x_68, x_69, x_70);
lean_inc(x_58);
x_72 = l_Lean_mkPropEq(x_10, x_58);
x_73 = l_Lean_Meta_mkExpectedPropHint(x_71, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_58);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_61)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_61;
}
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_58);
lean_dec_ref(x_15);
lean_dec(x_10);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_77 = lean_ctor_get(x_59, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_78 = x_59;
} else {
 lean_dec_ref(x_59);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec_ref(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_84 = !lean_is_exclusive(x_16);
if (x_84 == 0)
{
return x_16;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_16, 0);
lean_inc(x_85);
lean_dec(x_16);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; 
lean_dec_ref(x_12);
x_87 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_box(0);
x_91 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__6;
x_92 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__0;
x_93 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__1;
x_94 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__7;
x_95 = l_Lean_Name_mkStr4(x_2, x_92, x_93, x_94);
x_96 = l_Lean_mkConst(x_95, x_90);
x_97 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
x_98 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__3;
x_99 = l_Lean_mkApp3(x_96, x_89, x_97, x_98);
x_100 = l_Lean_mkPropEq(x_10, x_91);
x_101 = l_Lean_Meta_mkExpectedPropHint(x_99, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_91);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_87, 0, x_103);
return x_87;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_104 = lean_ctor_get(x_87, 0);
lean_inc(x_104);
lean_dec(x_87);
x_105 = lean_box(0);
x_106 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__6;
x_107 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__0;
x_108 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__1;
x_109 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__7;
x_110 = l_Lean_Name_mkStr4(x_2, x_107, x_108, x_109);
x_111 = l_Lean_mkConst(x_110, x_105);
x_112 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
x_113 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__3;
x_114 = l_Lean_mkApp3(x_111, x_104, x_112, x_113);
x_115 = l_Lean_mkPropEq(x_10, x_106);
x_116 = l_Lean_Meta_mkExpectedPropHint(x_114, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_106);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
else
{
uint8_t x_120; 
lean_dec(x_10);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_120 = !lean_is_exclusive(x_87);
if (x_120 == 0)
{
return x_87;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_87, 0);
lean_inc(x_121);
lean_dec(x_87);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
}
}
else
{
lean_object* x_123; 
lean_dec_ref(x_12);
x_123 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_box(0);
x_127 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__10;
x_128 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__0;
x_129 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__1;
x_130 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__11;
x_131 = l_Lean_Name_mkStr4(x_2, x_128, x_129, x_130);
x_132 = l_Lean_mkConst(x_131, x_126);
x_133 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
x_134 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__3;
x_135 = l_Lean_mkApp3(x_132, x_125, x_133, x_134);
x_136 = l_Lean_mkPropEq(x_10, x_127);
x_137 = l_Lean_Meta_mkExpectedPropHint(x_135, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_127);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_123, 0, x_139);
return x_123;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_140 = lean_ctor_get(x_123, 0);
lean_inc(x_140);
lean_dec(x_123);
x_141 = lean_box(0);
x_142 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__10;
x_143 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__0;
x_144 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__1;
x_145 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__11;
x_146 = l_Lean_Name_mkStr4(x_2, x_143, x_144, x_145);
x_147 = l_Lean_mkConst(x_146, x_141);
x_148 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
x_149 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__3;
x_150 = l_Lean_mkApp3(x_147, x_140, x_148, x_149);
x_151 = l_Lean_mkPropEq(x_10, x_142);
x_152 = l_Lean_Meta_mkExpectedPropHint(x_150, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_142);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
}
else
{
uint8_t x_156; 
lean_dec(x_10);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_156 = !lean_is_exclusive(x_123);
if (x_156 == 0)
{
return x_123;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
lean_dec(x_123);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_159 = !lean_is_exclusive(x_9);
if (x_159 == 0)
{
return x_9;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_9, 0);
lean_inc(x_160);
lean_dec(x_9);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = lean_box(0);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_free_object(x_7);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___boxed), 8, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1;
x_17 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_13, x_16, x_15, x_2, x_3, x_4, x_5);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec(x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___boxed), 8, 2);
lean_closure_set(x_25, 0, x_22);
lean_closure_set(x_25, 1, x_24);
x_26 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1;
x_27 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_23, x_26, x_25, x_2, x_3, x_4, x_5);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_28 = !lean_is_exclusive(x_7);
if (x_28 == 0)
{
return x_7;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
lean_dec(x_7);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trans", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__1;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_levelOne;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ge", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_mkNatLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_le_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_ge_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__26;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_lt_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_gt_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8;
x_63 = lean_unsigned_to_nat(1u);
x_64 = l_Lean_Expr_isAppOfArity(x_1, x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(x_1, x_2, x_3, x_4, x_5);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lean_Expr_appArg_x21(x_1);
x_67 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_66, x_3);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l_Lean_Expr_cleanupAnnotations(x_68);
x_70 = l_Lean_Expr_isApp(x_69);
if (x_70 == 0)
{
lean_dec_ref(x_69);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_71; uint8_t x_72; 
lean_inc_ref(x_69);
x_71 = l_Lean_Expr_appFnCleanup___redArg(x_69);
x_72 = l_Lean_Expr_isApp(x_71);
if (x_72 == 0)
{
lean_dec_ref(x_71);
lean_dec_ref(x_69);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_73; uint8_t x_74; 
lean_inc_ref(x_71);
x_73 = l_Lean_Expr_appFnCleanup___redArg(x_71);
x_74 = l_Lean_Expr_isApp(x_73);
if (x_74 == 0)
{
lean_dec_ref(x_73);
lean_dec_ref(x_71);
lean_dec_ref(x_69);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = l_Lean_Expr_appFnCleanup___redArg(x_73);
x_76 = l_Lean_Expr_isApp(x_75);
if (x_76 == 0)
{
lean_dec_ref(x_75);
lean_dec_ref(x_71);
lean_dec_ref(x_69);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_77 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_77);
lean_dec_ref(x_69);
x_78 = lean_ctor_get(x_71, 1);
lean_inc_ref(x_78);
lean_dec_ref(x_71);
x_79 = lean_ctor_get(x_75, 1);
lean_inc_ref(x_79);
x_80 = l_Lean_Expr_appFnCleanup___redArg(x_75);
x_81 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11;
x_82 = l_Lean_Expr_isConstOf(x_80, x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14;
x_84 = l_Lean_Expr_isConstOf(x_80, x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17;
x_86 = l_Lean_Expr_isConstOf(x_80, x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20;
x_88 = l_Lean_Expr_isConstOf(x_80, x_87);
lean_dec_ref(x_80);
if (x_88 == 0)
{
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_89; 
x_89 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_79, x_3);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = l_Lean_Expr_cleanupAnnotations(x_90);
x_92 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1;
x_93 = l_Lean_Expr_isConstOf(x_91, x_92);
lean_dec_ref(x_91);
if (x_93 == 0)
{
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21;
lean_inc_ref(x_77);
x_95 = l_Lean_mkNatAdd(x_77, x_94);
lean_inc_ref(x_78);
x_96 = l_Lean_mkNatLE(x_95, x_78);
x_97 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24;
x_98 = l_Lean_mkAppB(x_97, x_78, x_77);
x_11 = x_96;
x_12 = x_98;
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_61;
}
}
else
{
uint8_t x_99; 
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_99 = !lean_is_exclusive(x_89);
if (x_99 == 0)
{
return x_89;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_89, 0);
lean_inc(x_100);
lean_dec(x_89);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
}
else
{
lean_object* x_102; 
lean_dec_ref(x_80);
x_102 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_79, x_3);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
x_104 = l_Lean_Expr_cleanupAnnotations(x_103);
x_105 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1;
x_106 = l_Lean_Expr_isConstOf(x_104, x_105);
lean_dec_ref(x_104);
if (x_106 == 0)
{
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21;
lean_inc_ref(x_78);
x_108 = l_Lean_mkNatAdd(x_78, x_107);
lean_inc_ref(x_77);
x_109 = l_Lean_mkNatLE(x_108, x_77);
x_110 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27;
x_111 = l_Lean_mkAppB(x_110, x_78, x_77);
x_11 = x_109;
x_12 = x_111;
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_61;
}
}
else
{
uint8_t x_112; 
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_112 = !lean_is_exclusive(x_102);
if (x_112 == 0)
{
return x_102;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_102, 0);
lean_inc(x_113);
lean_dec(x_102);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
}
else
{
lean_object* x_115; 
lean_dec_ref(x_80);
x_115 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_79, x_3);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
x_117 = l_Lean_Expr_cleanupAnnotations(x_116);
x_118 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1;
x_119 = l_Lean_Expr_isConstOf(x_117, x_118);
lean_dec_ref(x_117);
if (x_119 == 0)
{
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_inc_ref(x_78);
lean_inc_ref(x_77);
x_120 = l_Lean_mkNatLE(x_77, x_78);
x_121 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30;
x_122 = l_Lean_mkAppB(x_121, x_78, x_77);
x_11 = x_120;
x_12 = x_122;
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_61;
}
}
else
{
uint8_t x_123; 
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_123 = !lean_is_exclusive(x_115);
if (x_123 == 0)
{
return x_115;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_115, 0);
lean_inc(x_124);
lean_dec(x_115);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
}
else
{
lean_object* x_126; 
lean_dec_ref(x_80);
x_126 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_79, x_3);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = l_Lean_Expr_cleanupAnnotations(x_127);
x_129 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1;
x_130 = l_Lean_Expr_isConstOf(x_128, x_129);
lean_dec_ref(x_128);
if (x_130 == 0)
{
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_inc_ref(x_77);
lean_inc_ref(x_78);
x_131 = l_Lean_mkNatLE(x_78, x_77);
x_132 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33;
x_133 = l_Lean_mkAppB(x_132, x_78, x_77);
x_11 = x_131;
x_12 = x_133;
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_61;
}
}
else
{
uint8_t x_134; 
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_134 = !lean_is_exclusive(x_126);
if (x_134 == 0)
{
return x_126;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_126, 0);
lean_inc(x_135);
lean_dec(x_126);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
}
}
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_137 = !lean_is_exclusive(x_67);
if (x_137 == 0)
{
return x_67;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_67, 0);
lean_inc(x_138);
lean_dec(x_67);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
block_61:
{
lean_object* x_18; 
lean_inc_ref(x_11);
x_18 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(x_11, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_12);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5;
x_29 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6;
lean_inc(x_26);
x_30 = l_Lean_mkApp6(x_28, x_29, x_1, x_11, x_26, x_12, x_27);
lean_ctor_set(x_24, 1, x_30);
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5;
x_34 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6;
lean_inc(x_31);
x_35 = l_Lean_mkApp6(x_33, x_34, x_1, x_11, x_31, x_12, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_20, 0, x_36);
return x_18;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_20, 0);
lean_inc(x_37);
lean_dec(x_20);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5;
x_42 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6;
lean_inc(x_38);
x_43 = l_Lean_mkApp6(x_41, x_42, x_1, x_11, x_38, x_12, x_39);
if (lean_is_scalar(x_40)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_40;
}
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_18, 0, x_45);
return x_18;
}
}
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_18, 0);
lean_inc(x_46);
lean_dec(x_18);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_1);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_12);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
x_55 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5;
x_56 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6;
lean_inc(x_52);
x_57 = l_Lean_mkApp6(x_55, x_56, x_1, x_11, x_52, x_12, x_53);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_57);
if (lean_is_scalar(x_51)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_51;
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expr", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = l_Nat_Linear_Expr_toPoly(x_1);
x_10 = l_Nat_Linear_Poly_norm(x_9);
x_11 = l_Nat_Linear_Poly_toExpr(x_10);
x_12 = l_Nat_Linear_instBEqExpr_beq(x_11, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc_ref(x_3);
x_13 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_3, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc_ref(x_11);
x_17 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_3, x_11);
lean_dec_ref(x_3);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__0;
x_21 = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___lam__0___closed__0;
x_22 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__2;
x_23 = l_Lean_Name_mkStr4(x_2, x_20, x_21, x_22);
x_24 = lean_box(0);
x_25 = l_Lean_mkConst(x_23, x_24);
x_26 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_1);
x_27 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_11);
x_28 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__3;
x_29 = l_Lean_mkApp4(x_25, x_14, x_26, x_27, x_28);
lean_inc(x_19);
x_30 = l_Lean_mkNatEq(x_16, x_19);
x_31 = l_Lean_Meta_mkExpectedPropHint(x_29, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_17, 0, x_33);
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
lean_dec(x_17);
x_35 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__0;
x_36 = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___lam__0___closed__0;
x_37 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__2;
x_38 = l_Lean_Name_mkStr4(x_2, x_35, x_36, x_37);
x_39 = lean_box(0);
x_40 = l_Lean_mkConst(x_38, x_39);
x_41 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_1);
x_42 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_11);
x_43 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__3;
x_44 = l_Lean_mkApp4(x_40, x_14, x_41, x_42, x_43);
lean_inc(x_34);
x_45 = l_Lean_mkNatEq(x_16, x_34);
x_46 = l_Lean_Meta_mkExpectedPropHint(x_44, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_50 = !lean_is_exclusive(x_17);
if (x_50 == 0)
{
return x_17;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_17, 0);
lean_inc(x_51);
lean_dec(x_17);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_15);
if (x_53 == 0)
{
return x_15;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_15, 0);
lean_inc(x_54);
lean_dec(x_15);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec_ref(x_11);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_56 = !lean_is_exclusive(x_13);
if (x_56 == 0)
{
return x_13;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_13, 0);
lean_inc(x_57);
lean_dec(x_13);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___lam__0___boxed), 8, 2);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1;
x_14 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_10, x_13, x_12, x_2, x_3, x_4, x_5);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__0);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__1);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__2 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__2);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__3 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__3);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__4 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__4);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__5 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__5);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__6 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__6);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__7 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__7);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__8 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__8);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__9 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__9);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__10 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__10);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__11 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0___closed__11);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__26 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__26();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__26);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32);
l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33);
l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___lam__0___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___lam__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

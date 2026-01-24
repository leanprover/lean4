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
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20;
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17;
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13;
lean_object* l_Nat_Linear_PolyCnstr_norm(lean_object*);
uint8_t l_Nat_Linear_PolyCnstr_isUnsat(lean_object*);
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Nat_Linear_Poly_toExpr(lean_object*);
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11;
lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3;
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22;
lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7;
lean_object* l_Nat_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32;
lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Nat_Linear_PolyCnstr_toExpr(lean_object*);
lean_object* l_Nat_Linear_ExprCnstr_toPoly(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23;
extern lean_object* l_Lean_levelOne;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17;
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
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10;
lean_object* l_Lean_mkNatEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25;
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_of_toNormPoly_eq", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_true_of_isValid", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_false_of_isUnsat", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
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
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_11 = x_9;
} else {
 lean_dec_ref(x_9);
 x_11 = lean_box(0);
}
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_14 = x_10;
} else {
 lean_dec_ref(x_10);
 x_14 = lean_box(0);
}
lean_inc(x_12);
x_15 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(x_13, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_12);
x_17 = l_Nat_Linear_ExprCnstr_toPoly(x_12);
x_18 = l_Nat_Linear_PolyCnstr_norm(x_17);
x_19 = l_Nat_Linear_PolyCnstr_isUnsat(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Nat_Linear_PolyCnstr_isValid(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Nat_Linear_PolyCnstr_toExpr(x_18);
lean_inc_ref(x_21);
x_22 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(x_13, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_52; 
x_24 = lean_ctor_get(x_22, 0);
x_52 = lean_expr_eqv(x_24, x_16);
if (x_52 == 0)
{
lean_free_object(x_22);
goto block_51;
}
else
{
if (x_20 == 0)
{
lean_object* x_53; 
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_53 = lean_box(0);
lean_ctor_set(x_22, 0, x_53);
return x_22;
}
else
{
lean_free_object(x_22);
goto block_51;
}
}
block_51:
{
lean_object* x_25; 
x_25 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5;
x_29 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_12);
x_30 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_21);
x_31 = l_Lean_eagerReflBoolTrue;
x_32 = l_Lean_mkApp4(x_28, x_27, x_29, x_30, x_31);
lean_inc(x_24);
x_33 = l_Lean_mkPropEq(x_16, x_24);
x_34 = l_Lean_Meta_mkExpectedPropHint(x_32, x_33);
if (lean_is_scalar(x_14)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_14;
}
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
if (lean_is_scalar(x_11)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_11;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_25, 0, x_36);
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_25, 0);
lean_inc(x_37);
lean_dec(x_25);
x_38 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5;
x_39 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_12);
x_40 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_21);
x_41 = l_Lean_eagerReflBoolTrue;
x_42 = l_Lean_mkApp4(x_38, x_37, x_39, x_40, x_41);
lean_inc(x_24);
x_43 = l_Lean_mkPropEq(x_16, x_24);
x_44 = l_Lean_Meta_mkExpectedPropHint(x_42, x_43);
if (lean_is_scalar(x_14)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_14;
}
lean_ctor_set(x_45, 0, x_24);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_11)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_11;
}
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_25);
if (x_48 == 0)
{
return x_25;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_25, 0);
lean_inc(x_49);
lean_dec(x_25);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_54; uint8_t x_72; 
x_54 = lean_ctor_get(x_22, 0);
lean_inc(x_54);
lean_dec(x_22);
x_72 = lean_expr_eqv(x_54, x_16);
if (x_72 == 0)
{
goto block_71;
}
else
{
if (x_20 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_54);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
else
{
goto block_71;
}
}
block_71:
{
lean_object* x_55; 
x_55 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5;
x_59 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_12);
x_60 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_21);
x_61 = l_Lean_eagerReflBoolTrue;
x_62 = l_Lean_mkApp4(x_58, x_56, x_59, x_60, x_61);
lean_inc(x_54);
x_63 = l_Lean_mkPropEq(x_16, x_54);
x_64 = l_Lean_Meta_mkExpectedPropHint(x_62, x_63);
if (lean_is_scalar(x_14)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_14;
}
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_64);
if (lean_is_scalar(x_11)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_11;
}
lean_ctor_set(x_66, 0, x_65);
if (lean_is_scalar(x_57)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_57;
}
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_54);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
x_68 = lean_ctor_get(x_55, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_69 = x_55;
} else {
 lean_dec_ref(x_55);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_75 = !lean_is_exclusive(x_22);
if (x_75 == 0)
{
return x_22;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_22, 0);
lean_inc(x_76);
lean_dec(x_22);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; 
lean_dec_ref(x_18);
x_78 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8;
x_82 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11;
x_83 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_12);
x_84 = l_Lean_eagerReflBoolTrue;
x_85 = l_Lean_mkApp3(x_82, x_80, x_83, x_84);
x_86 = l_Lean_mkPropEq(x_16, x_81);
x_87 = l_Lean_Meta_mkExpectedPropHint(x_85, x_86);
if (lean_is_scalar(x_14)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_14;
}
lean_ctor_set(x_88, 0, x_81);
lean_ctor_set(x_88, 1, x_87);
if (lean_is_scalar(x_11)) {
 x_89 = lean_alloc_ctor(1, 1, 0);
} else {
 x_89 = x_11;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_78, 0, x_89);
return x_78;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_90 = lean_ctor_get(x_78, 0);
lean_inc(x_90);
lean_dec(x_78);
x_91 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8;
x_92 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11;
x_93 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_12);
x_94 = l_Lean_eagerReflBoolTrue;
x_95 = l_Lean_mkApp3(x_92, x_90, x_93, x_94);
x_96 = l_Lean_mkPropEq(x_16, x_91);
x_97 = l_Lean_Meta_mkExpectedPropHint(x_95, x_96);
if (lean_is_scalar(x_14)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_14;
}
lean_ctor_set(x_98, 0, x_91);
lean_ctor_set(x_98, 1, x_97);
if (lean_is_scalar(x_11)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_11;
}
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
x_101 = !lean_is_exclusive(x_78);
if (x_101 == 0)
{
return x_78;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_78, 0);
lean_inc(x_102);
lean_dec(x_78);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
}
else
{
lean_object* x_104; 
lean_dec_ref(x_18);
x_104 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14;
x_108 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17;
x_109 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_12);
x_110 = l_Lean_eagerReflBoolTrue;
x_111 = l_Lean_mkApp3(x_108, x_106, x_109, x_110);
x_112 = l_Lean_mkPropEq(x_16, x_107);
x_113 = l_Lean_Meta_mkExpectedPropHint(x_111, x_112);
if (lean_is_scalar(x_14)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_14;
}
lean_ctor_set(x_114, 0, x_107);
lean_ctor_set(x_114, 1, x_113);
if (lean_is_scalar(x_11)) {
 x_115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_115 = x_11;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_104, 0, x_115);
return x_104;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_116 = lean_ctor_get(x_104, 0);
lean_inc(x_116);
lean_dec(x_104);
x_117 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14;
x_118 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17;
x_119 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_12);
x_120 = l_Lean_eagerReflBoolTrue;
x_121 = l_Lean_mkApp3(x_118, x_116, x_119, x_120);
x_122 = l_Lean_mkPropEq(x_16, x_117);
x_123 = l_Lean_Meta_mkExpectedPropHint(x_121, x_122);
if (lean_is_scalar(x_14)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_14;
}
lean_ctor_set(x_124, 0, x_117);
lean_ctor_set(x_124, 1, x_123);
if (lean_is_scalar(x_11)) {
 x_125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_125 = x_11;
}
lean_ctor_set(x_125, 0, x_124);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
else
{
uint8_t x_127; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
x_127 = !lean_is_exclusive(x_104);
if (x_127 == 0)
{
return x_104;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_104, 0);
lean_inc(x_128);
lean_dec(x_104);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_130 = !lean_is_exclusive(x_15);
if (x_130 == 0)
{
return x_15;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_15, 0);
lean_inc(x_131);
lean_dec(x_15);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
else
{
lean_object* x_133; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_133 = lean_box(0);
lean_ctor_set(x_7, 0, x_133);
return x_7;
}
}
else
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_7, 0);
lean_inc(x_134);
lean_dec(x_7);
if (lean_obj_tag(x_134) == 1)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
lean_inc(x_137);
x_140 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(x_138, x_137);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
lean_inc(x_137);
x_142 = l_Nat_Linear_ExprCnstr_toPoly(x_137);
x_143 = l_Nat_Linear_PolyCnstr_norm(x_142);
x_144 = l_Nat_Linear_PolyCnstr_isUnsat(x_143);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = l_Nat_Linear_PolyCnstr_isValid(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = l_Nat_Linear_PolyCnstr_toExpr(x_143);
lean_inc_ref(x_146);
x_147 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(x_138, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_167; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
x_167 = lean_expr_eqv(x_148, x_141);
if (x_167 == 0)
{
lean_dec(x_149);
goto block_166;
}
else
{
if (x_145 == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_148);
lean_dec_ref(x_146);
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_168 = lean_box(0);
if (lean_is_scalar(x_149)) {
 x_169 = lean_alloc_ctor(0, 1, 0);
} else {
 x_169 = x_149;
}
lean_ctor_set(x_169, 0, x_168);
return x_169;
}
else
{
lean_dec(x_149);
goto block_166;
}
}
block_166:
{
lean_object* x_150; 
x_150 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_138, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
x_153 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5;
x_154 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_137);
x_155 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_146);
x_156 = l_Lean_eagerReflBoolTrue;
x_157 = l_Lean_mkApp4(x_153, x_151, x_154, x_155, x_156);
lean_inc(x_148);
x_158 = l_Lean_mkPropEq(x_141, x_148);
x_159 = l_Lean_Meta_mkExpectedPropHint(x_157, x_158);
if (lean_is_scalar(x_139)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_139;
}
lean_ctor_set(x_160, 0, x_148);
lean_ctor_set(x_160, 1, x_159);
if (lean_is_scalar(x_136)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_136;
}
lean_ctor_set(x_161, 0, x_160);
if (lean_is_scalar(x_152)) {
 x_162 = lean_alloc_ctor(0, 1, 0);
} else {
 x_162 = x_152;
}
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_148);
lean_dec_ref(x_146);
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
x_163 = lean_ctor_get(x_150, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_164 = x_150;
} else {
 lean_dec_ref(x_150);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 1, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_163);
return x_165;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec_ref(x_146);
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_170 = lean_ctor_get(x_147, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_171 = x_147;
} else {
 lean_dec_ref(x_147);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 1, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_170);
return x_172;
}
}
else
{
lean_object* x_173; 
lean_dec_ref(x_143);
x_173 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_138, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
x_176 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8;
x_177 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11;
x_178 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_137);
x_179 = l_Lean_eagerReflBoolTrue;
x_180 = l_Lean_mkApp3(x_177, x_174, x_178, x_179);
x_181 = l_Lean_mkPropEq(x_141, x_176);
x_182 = l_Lean_Meta_mkExpectedPropHint(x_180, x_181);
if (lean_is_scalar(x_139)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_139;
}
lean_ctor_set(x_183, 0, x_176);
lean_ctor_set(x_183, 1, x_182);
if (lean_is_scalar(x_136)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_136;
}
lean_ctor_set(x_184, 0, x_183);
if (lean_is_scalar(x_175)) {
 x_185 = lean_alloc_ctor(0, 1, 0);
} else {
 x_185 = x_175;
}
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
x_186 = lean_ctor_get(x_173, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_187 = x_173;
} else {
 lean_dec_ref(x_173);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 1, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_186);
return x_188;
}
}
}
else
{
lean_object* x_189; 
lean_dec_ref(x_143);
x_189 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_138, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_191 = x_189;
} else {
 lean_dec_ref(x_189);
 x_191 = lean_box(0);
}
x_192 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14;
x_193 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17;
x_194 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_137);
x_195 = l_Lean_eagerReflBoolTrue;
x_196 = l_Lean_mkApp3(x_193, x_190, x_194, x_195);
x_197 = l_Lean_mkPropEq(x_141, x_192);
x_198 = l_Lean_Meta_mkExpectedPropHint(x_196, x_197);
if (lean_is_scalar(x_139)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_139;
}
lean_ctor_set(x_199, 0, x_192);
lean_ctor_set(x_199, 1, x_198);
if (lean_is_scalar(x_136)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_136;
}
lean_ctor_set(x_200, 0, x_199);
if (lean_is_scalar(x_191)) {
 x_201 = lean_alloc_ctor(0, 1, 0);
} else {
 x_201 = x_191;
}
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
x_202 = lean_ctor_get(x_189, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_203 = x_189;
} else {
 lean_dec_ref(x_189);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
return x_204;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_205 = lean_ctor_get(x_140, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_206 = x_140;
} else {
 lean_dec_ref(x_140);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_205);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_134);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_209, 0, x_208);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_210 = !lean_is_exclusive(x_7);
if (x_210 == 0)
{
return x_7;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_7, 0);
lean_inc(x_211);
lean_dec(x_7);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelOne;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ge", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
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
x_62 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7;
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
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_71);
x_72 = l_Lean_Expr_appFnCleanup___redArg(x_69);
x_73 = l_Lean_Expr_isApp(x_72);
if (x_73 == 0)
{
lean_dec_ref(x_72);
lean_dec_ref(x_71);
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
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_72, 1);
lean_inc_ref(x_74);
x_75 = l_Lean_Expr_appFnCleanup___redArg(x_72);
x_76 = l_Lean_Expr_isApp(x_75);
if (x_76 == 0)
{
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_71);
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
lean_object* x_77; uint8_t x_78; 
x_77 = l_Lean_Expr_appFnCleanup___redArg(x_75);
x_78 = l_Lean_Expr_isApp(x_77);
if (x_78 == 0)
{
lean_dec_ref(x_77);
lean_dec_ref(x_74);
lean_dec_ref(x_71);
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
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_77, 1);
lean_inc_ref(x_79);
x_80 = l_Lean_Expr_appFnCleanup___redArg(x_77);
x_81 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10;
x_82 = l_Lean_Expr_isConstOf(x_80, x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13;
x_84 = l_Lean_Expr_isConstOf(x_80, x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16;
x_86 = l_Lean_Expr_isConstOf(x_80, x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19;
x_88 = l_Lean_Expr_isConstOf(x_80, x_87);
lean_dec_ref(x_80);
if (x_88 == 0)
{
lean_dec_ref(x_79);
lean_dec_ref(x_74);
lean_dec_ref(x_71);
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
x_92 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20;
x_93 = l_Lean_Expr_isConstOf(x_91, x_92);
lean_dec_ref(x_91);
if (x_93 == 0)
{
lean_dec_ref(x_74);
lean_dec_ref(x_71);
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
lean_inc_ref(x_71);
x_95 = l_Lean_mkNatAdd(x_71, x_94);
lean_inc_ref(x_74);
x_96 = l_Lean_mkNatLE(x_95, x_74);
x_97 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24;
x_98 = l_Lean_mkAppB(x_97, x_74, x_71);
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
lean_dec_ref(x_74);
lean_dec_ref(x_71);
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
x_105 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20;
x_106 = l_Lean_Expr_isConstOf(x_104, x_105);
lean_dec_ref(x_104);
if (x_106 == 0)
{
lean_dec_ref(x_74);
lean_dec_ref(x_71);
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
lean_inc_ref(x_74);
x_108 = l_Lean_mkNatAdd(x_74, x_107);
lean_inc_ref(x_71);
x_109 = l_Lean_mkNatLE(x_108, x_71);
x_110 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27;
x_111 = l_Lean_mkAppB(x_110, x_74, x_71);
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
lean_dec_ref(x_74);
lean_dec_ref(x_71);
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
x_118 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20;
x_119 = l_Lean_Expr_isConstOf(x_117, x_118);
lean_dec_ref(x_117);
if (x_119 == 0)
{
lean_dec_ref(x_74);
lean_dec_ref(x_71);
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
lean_inc_ref(x_74);
lean_inc_ref(x_71);
x_120 = l_Lean_mkNatLE(x_71, x_74);
x_121 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30;
x_122 = l_Lean_mkAppB(x_121, x_74, x_71);
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
lean_dec_ref(x_74);
lean_dec_ref(x_71);
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
x_129 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20;
x_130 = l_Lean_Expr_isConstOf(x_128, x_129);
lean_dec_ref(x_128);
if (x_130 == 0)
{
lean_dec_ref(x_74);
lean_dec_ref(x_71);
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
lean_inc_ref(x_71);
lean_inc_ref(x_74);
x_131 = l_Lean_mkNatLE(x_74, x_71);
x_132 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33;
x_133 = l_Lean_mkAppB(x_132, x_74, x_71);
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
lean_dec_ref(x_74);
lean_dec_ref(x_71);
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
if (lean_obj_tag(x_20) == 1)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4;
x_27 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5;
lean_inc(x_24);
x_28 = l_Lean_mkApp6(x_26, x_27, x_1, x_11, x_24, x_12, x_25);
lean_ctor_set(x_22, 1, x_28);
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4;
x_32 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5;
lean_inc(x_29);
x_33 = l_Lean_mkApp6(x_31, x_32, x_1, x_11, x_29, x_12, x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_20, 0, x_34);
return x_18;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_20, 0);
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4;
x_40 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5;
lean_inc(x_36);
x_41 = l_Lean_mkApp6(x_39, x_40, x_1, x_11, x_36, x_12, x_37);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_18, 0, x_43);
return x_18;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_20);
lean_dec_ref(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_11);
lean_ctor_set(x_44, 1, x_12);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_18, 0, x_45);
return x_18;
}
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_18, 0);
lean_inc(x_46);
lean_dec(x_18);
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_51 = x_47;
} else {
 lean_dec_ref(x_47);
 x_51 = lean_box(0);
}
x_52 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4;
x_53 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5;
lean_inc(x_49);
x_54 = l_Lean_mkApp6(x_52, x_53, x_1, x_11, x_49, x_12, x_50);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
if (lean_is_scalar(x_48)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_48;
}
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_46);
lean_dec_ref(x_1);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_11);
lean_ctor_set(x_58, 1, x_12);
x_59 = lean_alloc_ctor(1, 1, 0);
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3;
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0;
x_3 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
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
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Nat_Linear_Expr_toPoly(x_11);
x_14 = l_Nat_Linear_Poly_norm(x_13);
x_15 = l_Nat_Linear_Poly_toExpr(x_14);
x_16 = l_Nat_Linear_instBEqExpr_beq(x_15, x_11);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_7);
lean_inc(x_12);
x_17 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_12, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc(x_11);
x_19 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_11);
x_20 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_12, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc_ref(x_15);
x_22 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_15);
x_23 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_12, x_15);
lean_dec(x_12);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2;
x_27 = l_Lean_eagerReflBoolTrue;
x_28 = l_Lean_mkApp4(x_26, x_18, x_19, x_22, x_27);
lean_inc(x_25);
x_29 = l_Lean_mkNatEq(x_21, x_25);
x_30 = l_Lean_Meta_mkExpectedPropHint(x_28, x_29);
lean_ctor_set(x_9, 1, x_30);
lean_ctor_set(x_9, 0, x_25);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_23, 0, x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2;
x_34 = l_Lean_eagerReflBoolTrue;
x_35 = l_Lean_mkApp4(x_33, x_18, x_19, x_22, x_34);
lean_inc(x_32);
x_36 = l_Lean_mkNatEq(x_21, x_32);
x_37 = l_Lean_Meta_mkExpectedPropHint(x_35, x_36);
lean_ctor_set(x_9, 1, x_37);
lean_ctor_set(x_9, 0, x_32);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_9);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_free_object(x_9);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_15);
lean_free_object(x_9);
lean_dec(x_12);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_20, 0);
lean_inc(x_44);
lean_dec(x_20);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec_ref(x_15);
lean_free_object(x_9);
lean_dec(x_12);
lean_dec(x_11);
x_46 = !lean_is_exclusive(x_17);
if (x_46 == 0)
{
return x_17;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_17, 0);
lean_inc(x_47);
lean_dec(x_17);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec_ref(x_15);
lean_free_object(x_9);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_49 = lean_box(0);
lean_ctor_set(x_7, 0, x_49);
return x_7;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_9, 0);
x_51 = lean_ctor_get(x_9, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_9);
x_52 = l_Nat_Linear_Expr_toPoly(x_50);
x_53 = l_Nat_Linear_Poly_norm(x_52);
x_54 = l_Nat_Linear_Poly_toExpr(x_53);
x_55 = l_Nat_Linear_instBEqExpr_beq(x_54, x_50);
if (x_55 == 0)
{
lean_object* x_56; 
lean_free_object(x_7);
lean_inc(x_51);
x_56 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_51, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
lean_inc(x_50);
x_58 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_50);
x_59 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_51, x_50);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
lean_inc_ref(x_54);
x_61 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_54);
x_62 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_51, x_54);
lean_dec(x_51);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2;
x_66 = l_Lean_eagerReflBoolTrue;
x_67 = l_Lean_mkApp4(x_65, x_57, x_58, x_61, x_66);
lean_inc(x_63);
x_68 = l_Lean_mkNatEq(x_60, x_63);
x_69 = l_Lean_Meta_mkExpectedPropHint(x_67, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
if (lean_is_scalar(x_64)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_64;
}
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_58);
lean_dec(x_57);
x_73 = lean_ctor_get(x_62, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_74 = x_62;
} else {
 lean_dec_ref(x_62);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec_ref(x_54);
lean_dec(x_51);
x_76 = lean_ctor_get(x_59, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_77 = x_59;
} else {
 lean_dec_ref(x_59);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_54);
lean_dec(x_51);
lean_dec(x_50);
x_79 = lean_ctor_get(x_56, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_80 = x_56;
} else {
 lean_dec_ref(x_56);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
return x_81;
}
}
else
{
lean_object* x_82; 
lean_dec_ref(x_54);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_82 = lean_box(0);
lean_ctor_set(x_7, 0, x_82);
return x_7;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_83 = lean_ctor_get(x_7, 0);
lean_inc(x_83);
lean_dec(x_7);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = l_Nat_Linear_Expr_toPoly(x_84);
x_88 = l_Nat_Linear_Poly_norm(x_87);
x_89 = l_Nat_Linear_Poly_toExpr(x_88);
x_90 = l_Nat_Linear_instBEqExpr_beq(x_89, x_84);
if (x_90 == 0)
{
lean_object* x_91; 
lean_inc(x_85);
x_91 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_85, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
lean_inc(x_84);
x_93 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_84);
x_94 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_85, x_84);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
lean_inc_ref(x_89);
x_96 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_89);
x_97 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_85, x_89);
lean_dec(x_85);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2;
x_101 = l_Lean_eagerReflBoolTrue;
x_102 = l_Lean_mkApp4(x_100, x_92, x_93, x_96, x_101);
lean_inc(x_98);
x_103 = l_Lean_mkNatEq(x_95, x_98);
x_104 = l_Lean_Meta_mkExpectedPropHint(x_102, x_103);
if (lean_is_scalar(x_86)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_86;
}
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
if (lean_is_scalar(x_99)) {
 x_107 = lean_alloc_ctor(0, 1, 0);
} else {
 x_107 = x_99;
}
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec(x_86);
x_108 = lean_ctor_get(x_97, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_109 = x_97;
} else {
 lean_dec_ref(x_97);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec_ref(x_89);
lean_dec(x_86);
lean_dec(x_85);
x_111 = lean_ctor_get(x_94, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_112 = x_94;
} else {
 lean_dec_ref(x_94);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec_ref(x_89);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
x_114 = lean_ctor_get(x_91, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_115 = x_91;
} else {
 lean_dec_ref(x_91);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec_ref(x_89);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_119 = !lean_is_exclusive(x_7);
if (x_119 == 0)
{
return x_7;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_7, 0);
lean_inc(x_120);
lean_dec(x_7);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
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
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16);
l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17 = _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17);
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
l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2 = _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

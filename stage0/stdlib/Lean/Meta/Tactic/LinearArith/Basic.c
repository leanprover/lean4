// Lean compiler output
// Module: Lean.Meta.Tactic.LinearArith.Basic
// Imports: Lean.Expr
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
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__15;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__8;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__13;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__10;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__1;
static lean_object* l_Lean_Meta_Linear_isLinearTerm___closed__5;
LEAN_EXPORT uint8_t l_Lean_Meta_Linear_isLinearCnstr(lean_object*);
static lean_object* l_Lean_Meta_Linear_isLinearTerm___closed__1;
static lean_object* l_Lean_Meta_Linear_isLinearTerm___closed__12;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__4;
static lean_object* l_Lean_Meta_Linear_isLinearTerm___closed__8;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__7;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Meta_Linear_isLinearTerm___closed__6;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__6;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__12;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__14;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__5;
lean_object* l_Lean_Expr_constName_x21(lean_object*);
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__16;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Linear_isLinearTerm___closed__4;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__9;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__11;
static lean_object* l_Lean_Meta_Linear_isLinearTerm___closed__11;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__18;
LEAN_EXPORT uint8_t l_Lean_Meta_Linear_isLinearTerm(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Linear_isLinearTerm___closed__10;
static lean_object* l_Lean_Meta_Linear_isLinearTerm___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_isLinearTerm___boxed(lean_object*);
static lean_object* l_Lean_Meta_Linear_isLinearTerm___closed__7;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_Linear_isLinearTerm___closed__9;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_isLinearCnstr___boxed(lean_object*);
static lean_object* l_Lean_Meta_Linear_isLinearTerm___closed__3;
static lean_object* l_Lean_Meta_Linear_isLinearCnstr___closed__17;
uint8_t l_Lean_Expr_isConst(lean_object*);
static lean_object* _init_l_Lean_Meta_Linear_isLinearTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearTerm___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearTerm___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Linear_isLinearTerm___closed__1;
x_2 = l_Lean_Meta_Linear_isLinearTerm___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearTerm___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearTerm___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearTerm___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Linear_isLinearTerm___closed__4;
x_2 = l_Lean_Meta_Linear_isLinearTerm___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearTerm___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearTerm___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearTerm___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Linear_isLinearTerm___closed__7;
x_2 = l_Lean_Meta_Linear_isLinearTerm___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearTerm___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearTerm___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearTerm___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Linear_isLinearTerm___closed__10;
x_2 = l_Lean_Meta_Linear_isLinearTerm___closed__11;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Linear_isLinearTerm(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_getAppFn(x_1);
x_3 = l_Lean_Expr_isConst(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Expr_constName_x21(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_Linear_isLinearTerm___closed__3;
x_7 = lean_name_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_Linear_isLinearTerm___closed__6;
x_9 = lean_name_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_Linear_isLinearTerm___closed__9;
x_11 = lean_name_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_Linear_isLinearTerm___closed__12;
x_13 = lean_name_eq(x_5, x_12);
lean_dec(x_5);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_5);
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_5);
x_16 = 1;
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_isLinearTerm___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Linear_isLinearTerm(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Linear_isLinearCnstr___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Linear_isLinearCnstr___closed__3;
x_2 = l_Lean_Meta_Linear_isLinearCnstr___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Linear_isLinearCnstr___closed__6;
x_2 = l_Lean_Meta_Linear_isLinearCnstr___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Linear_isLinearCnstr___closed__9;
x_2 = l_Lean_Meta_Linear_isLinearCnstr___closed__10;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ge", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Linear_isLinearCnstr___closed__12;
x_2 = l_Lean_Meta_Linear_isLinearCnstr___closed__13;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ne", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Linear_isLinearCnstr___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_isLinearCnstr___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Linear_isLinearCnstr___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Linear_isLinearCnstr(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_getAppFn(x_1);
x_3 = l_Lean_Expr_isConst(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Expr_constName_x21(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_Linear_isLinearCnstr___closed__2;
x_7 = lean_name_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_Linear_isLinearCnstr___closed__5;
x_9 = lean_name_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_Linear_isLinearCnstr___closed__8;
x_11 = lean_name_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_Linear_isLinearCnstr___closed__11;
x_13 = lean_name_eq(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Meta_Linear_isLinearCnstr___closed__14;
x_15 = lean_name_eq(x_5, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Meta_Linear_isLinearCnstr___closed__16;
x_17 = lean_name_eq(x_5, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Meta_Linear_isLinearCnstr___closed__18;
x_19 = lean_name_eq(x_5, x_18);
lean_dec(x_5);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = 0;
return x_25;
}
else
{
lean_object* x_26; 
x_26 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_1 = x_26;
goto _start;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_5);
lean_dec(x_1);
x_28 = 1;
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_5);
lean_dec(x_1);
x_29 = 1;
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_5);
lean_dec(x_1);
x_30 = 1;
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec(x_1);
x_31 = 1;
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
lean_dec(x_1);
x_32 = 1;
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_5);
lean_dec(x_1);
x_33 = 1;
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_isLinearCnstr___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Linear_isLinearCnstr(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_LinearArith_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Linear_isLinearTerm___closed__1 = _init_l_Lean_Meta_Linear_isLinearTerm___closed__1();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearTerm___closed__1);
l_Lean_Meta_Linear_isLinearTerm___closed__2 = _init_l_Lean_Meta_Linear_isLinearTerm___closed__2();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearTerm___closed__2);
l_Lean_Meta_Linear_isLinearTerm___closed__3 = _init_l_Lean_Meta_Linear_isLinearTerm___closed__3();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearTerm___closed__3);
l_Lean_Meta_Linear_isLinearTerm___closed__4 = _init_l_Lean_Meta_Linear_isLinearTerm___closed__4();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearTerm___closed__4);
l_Lean_Meta_Linear_isLinearTerm___closed__5 = _init_l_Lean_Meta_Linear_isLinearTerm___closed__5();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearTerm___closed__5);
l_Lean_Meta_Linear_isLinearTerm___closed__6 = _init_l_Lean_Meta_Linear_isLinearTerm___closed__6();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearTerm___closed__6);
l_Lean_Meta_Linear_isLinearTerm___closed__7 = _init_l_Lean_Meta_Linear_isLinearTerm___closed__7();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearTerm___closed__7);
l_Lean_Meta_Linear_isLinearTerm___closed__8 = _init_l_Lean_Meta_Linear_isLinearTerm___closed__8();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearTerm___closed__8);
l_Lean_Meta_Linear_isLinearTerm___closed__9 = _init_l_Lean_Meta_Linear_isLinearTerm___closed__9();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearTerm___closed__9);
l_Lean_Meta_Linear_isLinearTerm___closed__10 = _init_l_Lean_Meta_Linear_isLinearTerm___closed__10();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearTerm___closed__10);
l_Lean_Meta_Linear_isLinearTerm___closed__11 = _init_l_Lean_Meta_Linear_isLinearTerm___closed__11();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearTerm___closed__11);
l_Lean_Meta_Linear_isLinearTerm___closed__12 = _init_l_Lean_Meta_Linear_isLinearTerm___closed__12();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearTerm___closed__12);
l_Lean_Meta_Linear_isLinearCnstr___closed__1 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__1();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__1);
l_Lean_Meta_Linear_isLinearCnstr___closed__2 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__2();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__2);
l_Lean_Meta_Linear_isLinearCnstr___closed__3 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__3();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__3);
l_Lean_Meta_Linear_isLinearCnstr___closed__4 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__4();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__4);
l_Lean_Meta_Linear_isLinearCnstr___closed__5 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__5();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__5);
l_Lean_Meta_Linear_isLinearCnstr___closed__6 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__6();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__6);
l_Lean_Meta_Linear_isLinearCnstr___closed__7 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__7();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__7);
l_Lean_Meta_Linear_isLinearCnstr___closed__8 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__8();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__8);
l_Lean_Meta_Linear_isLinearCnstr___closed__9 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__9();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__9);
l_Lean_Meta_Linear_isLinearCnstr___closed__10 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__10();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__10);
l_Lean_Meta_Linear_isLinearCnstr___closed__11 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__11();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__11);
l_Lean_Meta_Linear_isLinearCnstr___closed__12 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__12();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__12);
l_Lean_Meta_Linear_isLinearCnstr___closed__13 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__13();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__13);
l_Lean_Meta_Linear_isLinearCnstr___closed__14 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__14();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__14);
l_Lean_Meta_Linear_isLinearCnstr___closed__15 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__15();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__15);
l_Lean_Meta_Linear_isLinearCnstr___closed__16 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__16();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__16);
l_Lean_Meta_Linear_isLinearCnstr___closed__17 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__17();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__17);
l_Lean_Meta_Linear_isLinearCnstr___closed__18 = _init_l_Lean_Meta_Linear_isLinearCnstr___closed__18();
lean_mark_persistent(l_Lean_Meta_Linear_isLinearCnstr___closed__18);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

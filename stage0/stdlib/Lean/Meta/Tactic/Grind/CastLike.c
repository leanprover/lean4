// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CastLike
// Imports: public import Lean.Expr import Init.Grind.ToInt import Init.Grind.Ring.Envelope import Init.Grind.Module.Envelope
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
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__6;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeDeclName(lean_object*);
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeApp(lean_object*);
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__14;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__8;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeFn(lean_object*);
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__10;
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__4;
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__12;
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeFn___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__2;
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__0;
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__7;
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__16;
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__5;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__15;
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeApp___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__13;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__3;
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ToInt", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toInt", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__3;
x_2 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__2;
x_3 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__1;
x_4 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("NatCast", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("natCast", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__6;
x_2 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IntCast", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intCast", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__9;
x_2 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ring", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfSemiring", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toQ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__13;
x_2 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__12;
x_3 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__11;
x_4 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__1;
x_5 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IntModule", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNatModule", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__13;
x_2 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__16;
x_3 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__15;
x_4 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__1;
x_5 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeDeclName(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__14;
x_11 = lean_name_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__17;
x_13 = lean_name_eq(x_1, x_12);
x_2 = x_13;
goto block_9;
}
else
{
x_2 = x_11;
goto block_9;
}
block_9:
{
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__4;
x_4 = lean_name_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__7;
x_6 = lean_name_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_Grind_isCastLikeDeclName___closed__10;
x_8 = lean_name_eq(x_1, x_7);
return x_8;
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isCastLikeDeclName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeFn(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Meta_Grind_isCastLikeDeclName(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isCastLikeFn(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeApp(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_getAppFn(x_1);
x_3 = l_Lean_Meta_Grind_isCastLikeFn(x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeApp___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isCastLikeApp(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Ring_Envelope(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Module_Envelope(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_CastLike(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_ToInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_Envelope(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Module_Envelope(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__0 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__0);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__1 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__1);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__2 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__2);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__3 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__3);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__4 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__4);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__5 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__5);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__6 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__6);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__7 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__7);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__8 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__8);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__9 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__9);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__10 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__10);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__11 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__11);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__12 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__12);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__13 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__13);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__14 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__14);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__15 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__15();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__15);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__16 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__16();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__16);
l_Lean_Meta_Grind_isCastLikeDeclName___closed__17 = _init_l_Lean_Meta_Grind_isCastLikeDeclName___closed__17();
lean_mark_persistent(l_Lean_Meta_Grind_isCastLikeDeclName___closed__17);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

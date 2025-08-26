// Lean compiler output
// Module: Init.GrindInstances.Ring.Rat
// Imports: Init.Grind.Ring.Field Init.Data.Rat.Lemmas
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
lean_object* l_Rat_instOfNat(lean_object*);
lean_object* l_Rat_div___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_instFieldRat___closed__1;
static lean_object* l_Lean_Grind_instFieldRat___closed__3;
static lean_object* l_Lean_Grind_instFieldRat___closed__8;
static lean_object* l_Lean_Grind_instFieldRat___closed__10;
static lean_object* l_Lean_Grind_instFieldRat___closed__7;
lean_object* l_Rat_mul___boxed(lean_object*, lean_object*);
lean_object* l_Rat_pow___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_instFieldRat___closed__6;
LEAN_EXPORT lean_object* l_Lean_Grind_instFieldRat___lam__1(lean_object*, lean_object*);
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instFieldRat;
static lean_object* l_Lean_Grind_instFieldRat___closed__5;
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* l_Rat_inv(lean_object*);
lean_object* l_instHPow___redArg(lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_instFieldRat___closed__4;
static lean_object* l_Lean_Grind_instFieldRat___closed__2;
lean_object* l_Rat_zpow___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_instFieldRat___closed__0;
static lean_object* l_Lean_Grind_instFieldRat___closed__11;
static lean_object* l_Lean_Grind_instFieldRat___closed__12;
static lean_object* l_Lean_Grind_instFieldRat___closed__9;
lean_object* l_Rat_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instFieldRat___lam__0(lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instFieldRat___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Rat_instNatCast___lam__0(x_1);
x_4 = l_Rat_mul(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instFieldRat___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Rat_ofInt(x_1);
x_4 = l_Rat_mul(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_instFieldRat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Rat_add), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instFieldRat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Rat_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instFieldRat___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Rat_instNatCast___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instFieldRat___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Rat_pow___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instFieldRat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_instFieldRat___closed__3;
x_2 = l_instHPow___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instFieldRat___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Rat_neg), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instFieldRat___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Rat_sub), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instFieldRat___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Rat_ofInt), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instFieldRat___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Rat_inv), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instFieldRat___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Rat_div___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instFieldRat___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Rat_zpow___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instFieldRat___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_instFieldRat___closed__10;
x_2 = l_instHPow___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instFieldRat___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Rat_instOfNat), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instFieldRat() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_instFieldRat___lam__0), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Grind_instFieldRat___lam__1), 2, 0);
x_3 = l_Lean_Grind_instFieldRat___closed__0;
x_4 = l_Lean_Grind_instFieldRat___closed__1;
x_5 = l_Lean_Grind_instFieldRat___closed__2;
x_6 = l_Lean_Grind_instFieldRat___closed__4;
x_7 = l_Lean_Grind_instFieldRat___closed__5;
x_8 = l_Lean_Grind_instFieldRat___closed__6;
x_9 = l_Lean_Grind_instFieldRat___closed__7;
x_10 = l_Lean_Grind_instFieldRat___closed__8;
x_11 = l_Lean_Grind_instFieldRat___closed__9;
x_12 = l_Lean_Grind_instFieldRat___closed__11;
x_13 = l_Lean_Grind_instFieldRat___closed__12;
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_5);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_1);
lean_ctor_set(x_14, 5, x_6);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_15, 2, x_8);
lean_ctor_set(x_15, 3, x_9);
lean_ctor_set(x_15, 4, x_2);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
return x_16;
}
}
lean_object* initialize_Init_Grind_Ring_Field(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Rat_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_Ring_Rat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Field(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Rat_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_instFieldRat___closed__0 = _init_l_Lean_Grind_instFieldRat___closed__0();
lean_mark_persistent(l_Lean_Grind_instFieldRat___closed__0);
l_Lean_Grind_instFieldRat___closed__1 = _init_l_Lean_Grind_instFieldRat___closed__1();
lean_mark_persistent(l_Lean_Grind_instFieldRat___closed__1);
l_Lean_Grind_instFieldRat___closed__2 = _init_l_Lean_Grind_instFieldRat___closed__2();
lean_mark_persistent(l_Lean_Grind_instFieldRat___closed__2);
l_Lean_Grind_instFieldRat___closed__3 = _init_l_Lean_Grind_instFieldRat___closed__3();
lean_mark_persistent(l_Lean_Grind_instFieldRat___closed__3);
l_Lean_Grind_instFieldRat___closed__4 = _init_l_Lean_Grind_instFieldRat___closed__4();
lean_mark_persistent(l_Lean_Grind_instFieldRat___closed__4);
l_Lean_Grind_instFieldRat___closed__5 = _init_l_Lean_Grind_instFieldRat___closed__5();
lean_mark_persistent(l_Lean_Grind_instFieldRat___closed__5);
l_Lean_Grind_instFieldRat___closed__6 = _init_l_Lean_Grind_instFieldRat___closed__6();
lean_mark_persistent(l_Lean_Grind_instFieldRat___closed__6);
l_Lean_Grind_instFieldRat___closed__7 = _init_l_Lean_Grind_instFieldRat___closed__7();
lean_mark_persistent(l_Lean_Grind_instFieldRat___closed__7);
l_Lean_Grind_instFieldRat___closed__8 = _init_l_Lean_Grind_instFieldRat___closed__8();
lean_mark_persistent(l_Lean_Grind_instFieldRat___closed__8);
l_Lean_Grind_instFieldRat___closed__9 = _init_l_Lean_Grind_instFieldRat___closed__9();
lean_mark_persistent(l_Lean_Grind_instFieldRat___closed__9);
l_Lean_Grind_instFieldRat___closed__10 = _init_l_Lean_Grind_instFieldRat___closed__10();
lean_mark_persistent(l_Lean_Grind_instFieldRat___closed__10);
l_Lean_Grind_instFieldRat___closed__11 = _init_l_Lean_Grind_instFieldRat___closed__11();
lean_mark_persistent(l_Lean_Grind_instFieldRat___closed__11);
l_Lean_Grind_instFieldRat___closed__12 = _init_l_Lean_Grind_instFieldRat___closed__12();
lean_mark_persistent(l_Lean_Grind_instFieldRat___closed__12);
l_Lean_Grind_instFieldRat = _init_l_Lean_Grind_instFieldRat();
lean_mark_persistent(l_Lean_Grind_instFieldRat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Init.GrindInstances.Ring.Int
// Imports: Init.Grind.Ring.Basic Init.Data.Int.Lemmas
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
lean_object* l_instIntCastInt___lam__0___boxed(lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_instCommRingInt___closed__7;
static lean_object* l_Lean_Grind_instCommRingInt___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt___lam__0(lean_object*, lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_instCommRingInt___closed__3;
lean_object* l_instNatCastInt___lam__0(lean_object*);
static lean_object* l_Lean_Grind_instCommRingInt___closed__8;
static lean_object* l_Lean_Grind_instCommRingInt___closed__6;
lean_object* l_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_instCommRingInt___closed__5;
static lean_object* l_Lean_Grind_instCommRingInt___closed__10;
lean_object* l_instHPow___redArg(lean_object*);
lean_object* l_instPowNat___redArg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_instCommRingInt___closed__9;
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* l_Int_mul___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_instCommRingInt___closed__1;
lean_object* l_instSMulOfMul___redArg(lean_object*);
static lean_object* l_Lean_Grind_instCommRingInt___closed__2;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt;
static lean_object* l_Lean_Grind_instCommRingInt___closed__4;
lean_object* l_Int_pow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_instNatCastInt___lam__0(x_1);
x_4 = lean_int_mul(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_add___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instNatCastInt___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_pow___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_instCommRingInt___closed__3;
x_2 = l_instPowNat___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_instCommRingInt___closed__4;
x_2 = l_instHPow___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_neg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_sub___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instIntCastInt___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_instCommRingInt___closed__1;
x_2 = l_instSMulOfMul___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instOfNat), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_instCommRingInt___lam__0___boxed), 2, 0);
x_2 = l_Lean_Grind_instCommRingInt___closed__0;
x_3 = l_Lean_Grind_instCommRingInt___closed__1;
x_4 = l_Lean_Grind_instCommRingInt___closed__2;
x_5 = l_Lean_Grind_instCommRingInt___closed__5;
x_6 = l_Lean_Grind_instCommRingInt___closed__6;
x_7 = l_Lean_Grind_instCommRingInt___closed__7;
x_8 = l_Lean_Grind_instCommRingInt___closed__8;
x_9 = l_Lean_Grind_instCommRingInt___closed__9;
x_10 = l_Lean_Grind_instCommRingInt___closed__10;
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set(x_11, 4, x_1);
lean_ctor_set(x_11, 5, x_5);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_7);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_instCommRingInt___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_Ring_Int(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_instCommRingInt___closed__0 = _init_l_Lean_Grind_instCommRingInt___closed__0();
lean_mark_persistent(l_Lean_Grind_instCommRingInt___closed__0);
l_Lean_Grind_instCommRingInt___closed__1 = _init_l_Lean_Grind_instCommRingInt___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommRingInt___closed__1);
l_Lean_Grind_instCommRingInt___closed__2 = _init_l_Lean_Grind_instCommRingInt___closed__2();
lean_mark_persistent(l_Lean_Grind_instCommRingInt___closed__2);
l_Lean_Grind_instCommRingInt___closed__3 = _init_l_Lean_Grind_instCommRingInt___closed__3();
lean_mark_persistent(l_Lean_Grind_instCommRingInt___closed__3);
l_Lean_Grind_instCommRingInt___closed__4 = _init_l_Lean_Grind_instCommRingInt___closed__4();
lean_mark_persistent(l_Lean_Grind_instCommRingInt___closed__4);
l_Lean_Grind_instCommRingInt___closed__5 = _init_l_Lean_Grind_instCommRingInt___closed__5();
lean_mark_persistent(l_Lean_Grind_instCommRingInt___closed__5);
l_Lean_Grind_instCommRingInt___closed__6 = _init_l_Lean_Grind_instCommRingInt___closed__6();
lean_mark_persistent(l_Lean_Grind_instCommRingInt___closed__6);
l_Lean_Grind_instCommRingInt___closed__7 = _init_l_Lean_Grind_instCommRingInt___closed__7();
lean_mark_persistent(l_Lean_Grind_instCommRingInt___closed__7);
l_Lean_Grind_instCommRingInt___closed__8 = _init_l_Lean_Grind_instCommRingInt___closed__8();
lean_mark_persistent(l_Lean_Grind_instCommRingInt___closed__8);
l_Lean_Grind_instCommRingInt___closed__9 = _init_l_Lean_Grind_instCommRingInt___closed__9();
lean_mark_persistent(l_Lean_Grind_instCommRingInt___closed__9);
l_Lean_Grind_instCommRingInt___closed__10 = _init_l_Lean_Grind_instCommRingInt___closed__10();
lean_mark_persistent(l_Lean_Grind_instCommRingInt___closed__10);
l_Lean_Grind_instCommRingInt = _init_l_Lean_Grind_instCommRingInt();
lean_mark_persistent(l_Lean_Grind_instCommRingInt);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

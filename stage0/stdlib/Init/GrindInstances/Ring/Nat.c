// Lean compiler output
// Module: Init.GrindInstances.Ring.Nat
// Imports: Init.Grind.Ordered.Ring Init.Data.Int.Lemmas
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
static lean_object* l_Lean_Grind_instCommSemiringNat___closed__1;
lean_object* l_instPowNat___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_instCommSemiringNat___closed__0;
static lean_object* l_Lean_Grind_instCommSemiringNat___closed__2;
static lean_object* l_Lean_Grind_instCommSemiringNat___closed__7;
static lean_object* l_Lean_Grind_instCommSemiringNat___closed__3;
lean_object* l_instHAdd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_instCommSemiringNat___closed__8;
static lean_object* l_Lean_Grind_instCommSemiringNat___closed__6;
lean_object* l_Nat_mul___boxed(lean_object*, lean_object*);
lean_object* l_instOfNatNat___boxed(lean_object*);
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_instCommSemiringNat___closed__4;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommSemiringNat;
static lean_object* l_Lean_Grind_instCommSemiringNat___closed__5;
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instNatCastNat___lam__0___boxed(lean_object*);
lean_object* l_Nat_pow___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Grind_instCommSemiringNat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_add___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommSemiringNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommSemiringNat___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instNatCastNat___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommSemiringNat___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_instCommSemiringNat___closed__1;
x_2 = lean_alloc_closure((void*)(l_instSMulOfMul___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommSemiringNat___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_pow___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommSemiringNat___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_instCommSemiringNat___closed__4;
x_2 = lean_alloc_closure((void*)(l_instPowNat___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommSemiringNat___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_instCommSemiringNat___closed__5;
x_2 = lean_alloc_closure((void*)(l_instHAdd___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instCommSemiringNat___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instOfNatNat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instCommSemiringNat___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Grind_instCommSemiringNat___closed__6;
x_2 = l_Lean_Grind_instCommSemiringNat___closed__3;
x_3 = l_Lean_Grind_instCommSemiringNat___closed__7;
x_4 = l_Lean_Grind_instCommSemiringNat___closed__2;
x_5 = l_Lean_Grind_instCommSemiringNat___closed__1;
x_6 = l_Lean_Grind_instCommSemiringNat___closed__0;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Grind_instCommSemiringNat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommSemiringNat___closed__8;
return x_1;
}
}
lean_object* initialize_Init_Grind_Ordered_Ring(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_Ring_Nat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ordered_Ring(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_instCommSemiringNat___closed__0 = _init_l_Lean_Grind_instCommSemiringNat___closed__0();
lean_mark_persistent(l_Lean_Grind_instCommSemiringNat___closed__0);
l_Lean_Grind_instCommSemiringNat___closed__1 = _init_l_Lean_Grind_instCommSemiringNat___closed__1();
lean_mark_persistent(l_Lean_Grind_instCommSemiringNat___closed__1);
l_Lean_Grind_instCommSemiringNat___closed__2 = _init_l_Lean_Grind_instCommSemiringNat___closed__2();
lean_mark_persistent(l_Lean_Grind_instCommSemiringNat___closed__2);
l_Lean_Grind_instCommSemiringNat___closed__3 = _init_l_Lean_Grind_instCommSemiringNat___closed__3();
lean_mark_persistent(l_Lean_Grind_instCommSemiringNat___closed__3);
l_Lean_Grind_instCommSemiringNat___closed__4 = _init_l_Lean_Grind_instCommSemiringNat___closed__4();
lean_mark_persistent(l_Lean_Grind_instCommSemiringNat___closed__4);
l_Lean_Grind_instCommSemiringNat___closed__5 = _init_l_Lean_Grind_instCommSemiringNat___closed__5();
lean_mark_persistent(l_Lean_Grind_instCommSemiringNat___closed__5);
l_Lean_Grind_instCommSemiringNat___closed__6 = _init_l_Lean_Grind_instCommSemiringNat___closed__6();
lean_mark_persistent(l_Lean_Grind_instCommSemiringNat___closed__6);
l_Lean_Grind_instCommSemiringNat___closed__7 = _init_l_Lean_Grind_instCommSemiringNat___closed__7();
lean_mark_persistent(l_Lean_Grind_instCommSemiringNat___closed__7);
l_Lean_Grind_instCommSemiringNat___closed__8 = _init_l_Lean_Grind_instCommSemiringNat___closed__8();
lean_mark_persistent(l_Lean_Grind_instCommSemiringNat___closed__8);
l_Lean_Grind_instCommSemiringNat = _init_l_Lean_Grind_instCommSemiringNat();
lean_mark_persistent(l_Lean_Grind_instCommSemiringNat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

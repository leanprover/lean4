// Lean compiler output
// Module: Init.Data.Dyadic.Instances
// Imports: Init.Data.Dyadic.Basic Init.Grind.Ring.Basic Init.Grind.Ordered.Ring
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
static lean_object* l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__4;
lean_object* l_Dyadic_add(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__7;
static lean_object* l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__0;
lean_object* l_Dyadic_instOfNat(lean_object*);
lean_object* l_Dyadic_neg(lean_object*);
lean_object* l_Dyadic_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___lam__0(lean_object*, lean_object*);
lean_object* l_Dyadic_instNatCast___lam__0(lean_object*);
static lean_object* l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing;
lean_object* l_Dyadic_mul___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__3;
static lean_object* l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___lam__1(lean_object*, lean_object*);
lean_object* l_instHAdd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__1;
lean_object* l_Dyadic_mul(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__6;
lean_object* l_Dyadic_ofInt(lean_object*);
static lean_object* l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__8;
static lean_object* l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__5;
lean_object* l_Dyadic_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Dyadic_instNatCast___lam__0(x_1);
x_4 = l_Dyadic_mul(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Dyadic_ofInt(x_1);
x_4 = l_Dyadic_mul(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Dyadic_add), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Dyadic_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Dyadic_instNatCast___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Dyadic_pow), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__3;
x_2 = lean_alloc_closure((void*)(l_instHAdd___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Dyadic_neg), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Dyadic_sub), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Dyadic_ofInt), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Dyadic_instOfNat), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___lam__0), 2, 0);
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___lam__1), 2, 0);
x_3 = l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__0;
x_4 = l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__1;
x_5 = l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__2;
x_6 = l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__4;
x_7 = l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__5;
x_8 = l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__6;
x_9 = l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__7;
x_10 = l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__8;
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_5);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set(x_11, 4, x_1);
lean_ctor_set(x_11, 5, x_6);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_2);
return x_12;
}
}
lean_object* initialize_Init_Data_Dyadic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Ordered_Ring(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Dyadic_Instances(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Dyadic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Ring(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__0 = _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__0();
lean_mark_persistent(l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__0);
l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__1 = _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__1();
lean_mark_persistent(l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__1);
l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__2 = _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__2();
lean_mark_persistent(l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__2);
l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__3 = _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__3();
lean_mark_persistent(l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__3);
l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__4 = _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__4();
lean_mark_persistent(l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__4);
l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__5 = _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__5();
lean_mark_persistent(l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__5);
l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__6 = _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__6();
lean_mark_persistent(l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__6);
l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__7 = _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__7();
lean_mark_persistent(l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__7);
l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__8 = _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__8();
lean_mark_persistent(l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing___closed__8);
l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing = _init_l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing();
lean_mark_persistent(l___private_Init_Data_Dyadic_Instances_0__Dyadic_instCommRing);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

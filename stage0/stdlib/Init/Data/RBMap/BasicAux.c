// Lean compiler output
// Module: Init.Data.RBMap.BasicAux
// Imports: Init.Data.RBMap.Basic Init.Util
#include "runtime/lean.h"
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
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_min_x21___rarg___closed__2;
lean_object* l_RBMap_min_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_min_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_min_x21___rarg___closed__1;
lean_object* l_RBMap_min_x21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_find_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_max_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_find_x21(lean_object*, lean_object*);
lean_object* l_RBNode_min___main___rarg(lean_object*);
lean_object* l_RBMap_max_x21___rarg___closed__1;
lean_object* l_RBMap_max_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_find_x21___rarg___closed__2;
lean_object* l_RBMap_find_x21___rarg___closed__1;
lean_object* l_RBMap_min_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_RBMap_max_x21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_max___main___rarg(lean_object*);
lean_object* l_RBMap_max_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_min_x21___rarg___closed__3;
lean_object* _init_l_RBMap_min_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Data.RBMap.BasicAux");
return x_1;
}
}
lean_object* _init_l_RBMap_min_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("map is empty");
return x_1;
}
}
lean_object* _init_l_RBMap_min_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_RBMap_min_x21___rarg___closed__1;
x_2 = lean_unsigned_to_nat(18u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_RBMap_min_x21___rarg___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_RBMap_min_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_10; 
x_10 = l_RBNode_min___main___rarg(x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
x_4 = x_11;
goto block_9;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_10, 0, x_16);
x_4 = x_10;
goto block_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_4 = x_21;
goto block_9;
}
}
block_9:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = l_RBMap_min_x21___rarg___closed__3;
x_7 = lean_panic_fn(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
return x_8;
}
}
}
}
lean_object* l_RBMap_min_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBMap_min_x21___rarg___boxed), 3, 0);
return x_4;
}
}
lean_object* l_RBMap_min_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_min_x21___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBMap_min_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_min_x21(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* _init_l_RBMap_max_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_RBMap_min_x21___rarg___closed__1;
x_2 = lean_unsigned_to_nat(23u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_RBMap_min_x21___rarg___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_RBMap_max_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_10; 
x_10 = l_RBNode_max___main___rarg(x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
x_4 = x_11;
goto block_9;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_10, 0, x_16);
x_4 = x_10;
goto block_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_4 = x_21;
goto block_9;
}
}
block_9:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = l_RBMap_max_x21___rarg___closed__1;
x_7 = lean_panic_fn(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
return x_8;
}
}
}
}
lean_object* l_RBMap_max_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBMap_max_x21___rarg___boxed), 3, 0);
return x_4;
}
}
lean_object* l_RBMap_max_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_max_x21___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBMap_max_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_max_x21(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* _init_l_RBMap_find_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("key is not in the map");
return x_1;
}
}
lean_object* _init_l_RBMap_find_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_RBMap_min_x21___rarg___closed__1;
x_2 = lean_unsigned_to_nat(28u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_RBMap_find_x21___rarg___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_RBMap_find_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_find___main___rarg(x_1, lean_box(0), x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_RBMap_find_x21___rarg___closed__2;
x_7 = lean_panic_fn(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
return x_8;
}
}
}
lean_object* l_RBMap_find_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBMap_find_x21___rarg), 4, 0);
return x_3;
}
}
lean_object* initialize_Init_Data_RBMap_Basic(lean_object*);
lean_object* initialize_Init_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_RBMap_BasicAux(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_RBMap_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_RBMap_min_x21___rarg___closed__1 = _init_l_RBMap_min_x21___rarg___closed__1();
lean_mark_persistent(l_RBMap_min_x21___rarg___closed__1);
l_RBMap_min_x21___rarg___closed__2 = _init_l_RBMap_min_x21___rarg___closed__2();
lean_mark_persistent(l_RBMap_min_x21___rarg___closed__2);
l_RBMap_min_x21___rarg___closed__3 = _init_l_RBMap_min_x21___rarg___closed__3();
lean_mark_persistent(l_RBMap_min_x21___rarg___closed__3);
l_RBMap_max_x21___rarg___closed__1 = _init_l_RBMap_max_x21___rarg___closed__1();
lean_mark_persistent(l_RBMap_max_x21___rarg___closed__1);
l_RBMap_find_x21___rarg___closed__1 = _init_l_RBMap_find_x21___rarg___closed__1();
lean_mark_persistent(l_RBMap_find_x21___rarg___closed__1);
l_RBMap_find_x21___rarg___closed__2 = _init_l_RBMap_find_x21___rarg___closed__2();
lean_mark_persistent(l_RBMap_find_x21___rarg___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

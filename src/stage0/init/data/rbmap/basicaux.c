// Lean compiler output
// Module: init.data.rbmap.basicaux
// Imports: init.data.rbmap.basic init.util
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
lean_object* l_RBMap_max_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_RBMap_min_x21___spec__1(lean_object*, lean_object*);
lean_object* l_RBNode_min___main___rarg(lean_object*);
lean_object* l_RBNode_max___main___rarg(lean_object*);
lean_object* l_RBMap_find_x21(lean_object*, lean_object*);
lean_object* l_RBMap_max_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_max_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_max_x21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__3;
lean_object* l_panicWithPos___at_RBMap_min_x21___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_panicWithPos___at_RBMap_max_x21___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_RBMap_max_x21___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_RBMap_min_x21___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_min_x21(lean_object*, lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__1;
lean_object* l_RBMap_min_x21___rarg___closed__2;
lean_object* l_RBNode_find___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_RBMap_max_x21___spec__1(lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_min_x21___rarg___closed__1;
lean_object* l_RBMap_find_x21___rarg___closed__1;
lean_object* l_RBMap_min_x21___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__2;
lean_object* l_RBMap_find_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_min_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_min_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_RBMap_min_x21___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_8 = l_panicWithPos___rarg___closed__1;
x_9 = lean_string_append(x_8, x_3);
x_10 = l_panicWithPos___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_repr(x_4);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l_panicWithPos___rarg___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Nat_repr(x_5);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_panicWithPos___rarg___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_6);
x_21 = lean_panic_fn(x_20);
return x_21;
}
}
lean_object* l_panicWithPos___at_RBMap_min_x21___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_panicWithPos___at_RBMap_min_x21___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* _init_l_RBMap_min_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("/Users/leonardodemoura/projects/lean4/library/init/data/rbmap/basicaux.lean");
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
lean_object* l_RBMap_min_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_12; 
x_12 = l_RBNode_min___main___rarg(x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_box(0);
x_4 = x_13;
goto block_11;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_12, 0, x_18);
x_4 = x_12;
goto block_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_4 = x_23;
goto block_11;
}
}
block_11:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_RBMap_min_x21___rarg___closed__1;
x_6 = lean_unsigned_to_nat(18u);
x_7 = lean_unsigned_to_nat(12u);
x_8 = l_RBMap_min_x21___rarg___closed__2;
x_9 = l_panicWithPos___at_RBMap_min_x21___spec__1___rarg(x_1, x_2, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
return x_10;
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
lean_object* l_panicWithPos___at_RBMap_min_x21___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panicWithPos___at_RBMap_min_x21___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
return x_7;
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
lean_object* l_panicWithPos___at_RBMap_max_x21___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_8 = l_panicWithPos___rarg___closed__1;
x_9 = lean_string_append(x_8, x_3);
x_10 = l_panicWithPos___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_repr(x_4);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l_panicWithPos___rarg___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Nat_repr(x_5);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_panicWithPos___rarg___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_6);
x_21 = lean_panic_fn(x_20);
return x_21;
}
}
lean_object* l_panicWithPos___at_RBMap_max_x21___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_panicWithPos___at_RBMap_max_x21___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_RBMap_max_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_12; 
x_12 = l_RBNode_max___main___rarg(x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_box(0);
x_4 = x_13;
goto block_11;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_12, 0, x_18);
x_4 = x_12;
goto block_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_4 = x_23;
goto block_11;
}
}
block_11:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_RBMap_min_x21___rarg___closed__1;
x_6 = lean_unsigned_to_nat(23u);
x_7 = lean_unsigned_to_nat(12u);
x_8 = l_RBMap_min_x21___rarg___closed__2;
x_9 = l_panicWithPos___at_RBMap_max_x21___spec__1___rarg(x_1, x_2, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
return x_10;
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
lean_object* l_panicWithPos___at_RBMap_max_x21___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panicWithPos___at_RBMap_max_x21___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
return x_7;
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
lean_object* l_RBMap_find_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_find___main___rarg(x_1, lean_box(0), x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_RBMap_min_x21___rarg___closed__1;
x_7 = lean_unsigned_to_nat(28u);
x_8 = lean_unsigned_to_nat(12u);
x_9 = l_RBMap_find_x21___rarg___closed__1;
x_10 = l_panicWithPos___rarg(x_2, x_6, x_7, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
return x_11;
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
lean_object* initialize_init_data_rbmap_basic(lean_object*);
lean_object* initialize_init_util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_data_rbmap_basicaux(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_rbmap_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_util(w);
if (lean_io_result_is_error(w)) return w;
l_RBMap_min_x21___rarg___closed__1 = _init_l_RBMap_min_x21___rarg___closed__1();
lean_mark_persistent(l_RBMap_min_x21___rarg___closed__1);
l_RBMap_min_x21___rarg___closed__2 = _init_l_RBMap_min_x21___rarg___closed__2();
lean_mark_persistent(l_RBMap_min_x21___rarg___closed__2);
l_RBMap_find_x21___rarg___closed__1 = _init_l_RBMap_find_x21___rarg___closed__1();
lean_mark_persistent(l_RBMap_find_x21___rarg___closed__1);
return w;
}
#ifdef __cplusplus
}
#endif

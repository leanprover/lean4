// Lean compiler output
// Module: Init.Lean.Data.SMap
// Imports: Init.Data.HashMap Init.Data.PersistentHashMap
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
lean_object* l_Lean_SMap_HasEmptyc___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x21___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_SMap_foldStage2___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_Inhabited___rarg(lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_Inhabited(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_HashMapImp_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f_x27(lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___at_Lean_SMap_foldStage2___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_foldStage2(lean_object*, lean_object*);
lean_object* l_Lean_SMap_findD___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SMap_HasEmptyc___rarg(lean_object*, lean_object*);
lean_object* l_Lean_SMap_numBuckets___rarg(lean_object*);
lean_object* l_Lean_SMap_findD(lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_SMap_foldStage2___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___at_Lean_SMap_foldStage2___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x21___rarg___closed__2;
lean_object* l_Lean_SMap_switch(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_stageSizes___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_foldStage2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_empty___rarg(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_numBuckets___rarg___boxed(lean_object*);
lean_object* l_HashMap_numBuckets___rarg(lean_object*);
lean_object* l_Lean_SMap_empty___rarg(lean_object*, lean_object*);
lean_object* l_Lean_SMap_stageSizes___rarg___boxed(lean_object*);
lean_object* l_Lean_SMap_contains(lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_stageSizes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_Inhabited___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_HasEmptyc(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___at_Lean_SMap_foldStage2___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_findD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___at_Lean_SMap_foldStage2___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_foldStage2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_numBuckets___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_size___rarg___boxed(lean_object*);
lean_object* l_Lean_SMap_size___rarg(lean_object*);
lean_object* l_Lean_SMap_switch___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_SMap_foldStage2___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_size(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_find_x21___rarg___closed__2;
lean_object* l_Lean_SMap_find_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_numBuckets(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_stageSizes(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l_Lean_SMap_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x21(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_SMap_Inhabited___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_PersistentHashMap_empty___rarg(x_2, x_1);
x_4 = 1;
x_5 = l_HashMap_Inhabited___closed__1;
x_6 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_4);
return x_6;
}
}
lean_object* l_Lean_SMap_Inhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_Inhabited___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_Inhabited___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_Inhabited___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_empty___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_PersistentHashMap_empty___rarg(x_2, x_1);
x_4 = 1;
x_5 = l_HashMap_Inhabited___closed__1;
x_6 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_4);
return x_6;
}
}
lean_object* l_Lean_SMap_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_empty___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_empty___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_empty___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_HasEmptyc___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_empty___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_SMap_HasEmptyc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_HasEmptyc___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_HasEmptyc___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_HasEmptyc___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_PersistentHashMap_insert___rarg(x_1, x_2, x_8, x_4, x_5);
lean_ctor_set(x_3, 1, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_PersistentHashMap_insert___rarg(x_1, x_2, x_11, x_4, x_5);
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_6);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = l_HashMapImp_insert___rarg(x_1, x_2, x_15, x_4, x_5);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = l_HashMapImp_insert___rarg(x_1, x_2, x_17, x_4, x_5);
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_6);
return x_20;
}
}
}
}
lean_object* l_Lean_SMap_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_insert___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_PersistentHashMap_find_x3f___rarg(x_1, x_2, x_7, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_HashMapImp_find_x3f___rarg(x_1, x_2, x_6, x_4);
lean_dec(x_6);
return x_9;
}
else
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_HashMapImp_find_x3f___rarg(x_1, x_2, x_10, x_4);
lean_dec(x_10);
return x_11;
}
}
}
lean_object* l_Lean_SMap_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_find_x3f___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_findD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_SMap_find_x3f___rarg(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l_Lean_SMap_findD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_findD___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_findD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_SMap_findD___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* _init_l_Lean_SMap_find_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.Data.SMap");
return x_1;
}
}
lean_object* _init_l_Lean_SMap_find_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_SMap_find_x21___rarg___closed__1;
x_2 = lean_unsigned_to_nat(56u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_PersistentHashMap_find_x21___rarg___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_SMap_find_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_SMap_find_x3f___rarg(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_SMap_find_x21___rarg___closed__2;
x_8 = lean_panic_fn(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
lean_object* l_Lean_SMap_find_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_find_x21___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_HashMapImp_contains___rarg(x_1, x_2, x_6, x_4);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_PersistentHashMap_contains___rarg(x_1, x_2, x_7, x_4);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 1;
x_11 = lean_box(x_10);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_HashMapImp_contains___rarg(x_1, x_2, x_12, x_4);
lean_dec(x_12);
x_14 = lean_box(x_13);
return x_14;
}
}
}
lean_object* l_Lean_SMap_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_contains___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_HashMapImp_find_x3f___rarg(x_1, x_2, x_6, x_4);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_PersistentHashMap_find_x3f___rarg(x_1, x_2, x_7, x_4);
return x_9;
}
else
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_HashMapImp_find_x3f___rarg(x_1, x_2, x_10, x_4);
lean_dec(x_10);
return x_11;
}
}
}
lean_object* l_Lean_SMap_find_x3f_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_find_x3f_x27___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_switch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
if (x_4 == 0)
{
return x_3;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
lean_ctor_set_uint8(x_3, sizeof(void*)*2, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = 0;
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_SMap_switch(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_switch___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_switch___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_switch___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_1);
x_13 = lean_apply_3(x_1, x_5, x_11, x_12);
x_4 = x_10;
x_5 = x_13;
goto _start;
}
case 1:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
lean_inc(x_1);
x_16 = l_PersistentHashMap_foldlMAux___main___at_Lean_SMap_foldStage2___spec__2___rarg(x_1, x_15, x_5);
lean_dec(x_15);
x_4 = x_10;
x_5 = x_16;
goto _start;
}
default: 
{
x_4 = x_10;
goto _start;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__3___rarg___boxed), 5, 0);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
lean_inc(x_1);
x_11 = lean_apply_3(x_1, x_6, x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
x_6 = x_11;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__4___rarg___boxed), 6, 0);
return x_4;
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_SMap_foldStage2___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__3___rarg(x_1, x_4, x_4, x_5, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__4___rarg(x_1, x_7, x_8, x_7, x_9, x_3);
return x_10;
}
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_SMap_foldStage2___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_PersistentHashMap_foldlMAux___main___at_Lean_SMap_foldStage2___spec__2___rarg___boxed), 3, 0);
return x_4;
}
}
lean_object* l_PersistentHashMap_foldlM___at_Lean_SMap_foldStage2___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_PersistentHashMap_foldlMAux___main___at_Lean_SMap_foldStage2___spec__2___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_foldlM___at_Lean_SMap_foldStage2___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_PersistentHashMap_foldlM___at_Lean_SMap_foldStage2___spec__1___rarg___boxed), 3, 0);
return x_6;
}
}
lean_object* l_Lean_SMap_foldStage2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 1);
x_8 = l_PersistentHashMap_foldlM___at_Lean_SMap_foldStage2___spec__1___rarg(x_4, x_7, x_5);
return x_8;
}
}
lean_object* l_Lean_SMap_foldStage2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_foldStage2___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_SMap_foldStage2___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___at_Lean_SMap_foldStage2___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_foldlMAux___main___at_Lean_SMap_foldStage2___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_PersistentHashMap_foldlM___at_Lean_SMap_foldStage2___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_foldlM___at_Lean_SMap_foldStage2___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_PersistentHashMap_foldlM___at_Lean_SMap_foldStage2___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_foldlM___at_Lean_SMap_foldStage2___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_SMap_foldStage2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_SMap_foldStage2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_SMap_size___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_nat_add(x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_SMap_size(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_SMap_size___rarg___boxed), 1, 0);
return x_5;
}
}
lean_object* l_Lean_SMap_size___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_size___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SMap_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SMap_size(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_SMap_stageSizes___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_SMap_stageSizes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_SMap_stageSizes___rarg___boxed), 1, 0);
return x_5;
}
}
lean_object* l_Lean_SMap_stageSizes___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_stageSizes___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SMap_stageSizes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SMap_stageSizes(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_SMap_numBuckets___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_HashMap_numBuckets___rarg(x_2);
return x_3;
}
}
lean_object* l_Lean_SMap_numBuckets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_SMap_numBuckets___rarg___boxed), 1, 0);
return x_5;
}
}
lean_object* l_Lean_SMap_numBuckets___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_numBuckets___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SMap_numBuckets___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SMap_numBuckets(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init_Data_HashMap(lean_object*);
lean_object* initialize_Init_Data_PersistentHashMap(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Data_SMap(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_HashMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_PersistentHashMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_SMap_find_x21___rarg___closed__1 = _init_l_Lean_SMap_find_x21___rarg___closed__1();
lean_mark_persistent(l_Lean_SMap_find_x21___rarg___closed__1);
l_Lean_SMap_find_x21___rarg___closed__2 = _init_l_Lean_SMap_find_x21___rarg___closed__2();
lean_mark_persistent(l_Lean_SMap_find_x21___rarg___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

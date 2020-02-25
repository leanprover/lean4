// Lean compiler output
// Module: Init.Data.HashSet
// Imports: Init.Data.HashMap
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
lean_object* l_HashSet_erase(lean_object*);
lean_object* l_HashSet_fold___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_isEmpty(lean_object*, lean_object*, lean_object*);
uint8_t l_HashSet_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_foldM___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_isEmpty___rarg___boxed(lean_object*);
lean_object* l_HashSet_find_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_fold___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_size___rarg___boxed(lean_object*);
lean_object* l_HashSet_Inhabited(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_contains(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_HashMapImp_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_size___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_foldM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_HashSet_isEmpty___rarg(lean_object*);
lean_object* l_HashSet_insert(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_HashSet_HasEmptyc___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_HashSet_fold___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_fold(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_HashSet_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashSet___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_size(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_fold___spec__2(lean_object*, lean_object*);
lean_object* l_HashMapImp_erase___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_HasEmptyc(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_HashSet_foldM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashSet___rarg(lean_object*);
lean_object* l_AssocList_foldlM___main___at_HashSet_foldM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_HashSet_find_x3f(lean_object*);
lean_object* l_AssocList_foldlM___main___at_HashSet_foldM___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_contains___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_empty(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_Inhabited___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_fold___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashSet(lean_object*, lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_foldM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_erase___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_size___rarg(lean_object*);
lean_object* l_HashMapImp_findEntry_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_HashSet_fold___spec__1(lean_object*, lean_object*);
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l_HashSet_fold___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_foldM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_empty___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_mkHashSet___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashSet(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_mkHashSet___rarg), 1, 0);
return x_4;
}
}
lean_object* l_mkHashSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_mkHashSet(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_HashSet_Inhabited(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashMap_Inhabited___closed__1;
return x_4;
}
}
lean_object* l_HashSet_Inhabited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashSet_Inhabited(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_HashSet_HasEmptyc(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashMap_Inhabited___closed__1;
return x_4;
}
}
lean_object* l_HashSet_HasEmptyc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashSet_HasEmptyc(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_HashSet_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_HashMapImp_insert___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_HashSet_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HashSet_insert___rarg), 4, 0);
return x_2;
}
}
lean_object* l_HashSet_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HashMapImp_erase___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_HashSet_erase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HashSet_erase___rarg), 4, 0);
return x_2;
}
}
lean_object* l_HashSet_find_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HashMapImp_findEntry_x3f___rarg(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
lean_object* l_HashSet_find_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HashSet_find_x3f___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_HashSet_find_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HashSet_find_x3f___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
uint8_t l_HashSet_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_HashMapImp_contains___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_HashSet_contains(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HashSet_contains___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_HashSet_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_HashSet_contains___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_HashSet_size___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_HashSet_size(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_HashSet_size___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_HashSet_size___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HashSet_size___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_HashSet_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashSet_size(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_HashSet_isEmpty___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
lean_object* l_HashSet_isEmpty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_HashSet_isEmpty___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_HashSet_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_HashSet_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_HashSet_isEmpty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashSet_isEmpty(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_HashSet_empty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashMap_Inhabited___closed__1;
return x_4;
}
}
lean_object* l_HashSet_empty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashSet_empty(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_AssocList_foldlM___main___at_HashSet_foldM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_AssocList_foldlM___main___at_HashSet_foldM___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_AssocList_foldlM___main___at_HashSet_foldM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_2);
x_11 = lean_apply_2(x_2, x_3, x_8);
x_12 = lean_alloc_closure((void*)(l_AssocList_foldlM___main___at_HashSet_foldM___spec__1___rarg___lambda__1), 4, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_9);
x_13 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
}
lean_object* l_AssocList_foldlM___main___at_HashSet_foldM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_AssocList_foldlM___main___at_HashSet_foldM___spec__1___rarg), 4, 0);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSet_foldM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_array_fget(x_4, x_5);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_AssocList_foldlM___main___at_HashSet_foldM___spec__1___rarg(x_1, x_2, x_6, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
x_17 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_HashSet_foldM___spec__2___rarg___boxed), 6, 5);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_4);
lean_closure_set(x_17, 4, x_16);
x_18 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_17);
return x_18;
}
}
}
lean_object* l_Array_iterateMAux___main___at_HashSet_foldM___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_HashSet_foldM___spec__2___rarg___boxed), 6, 0);
return x_4;
}
}
lean_object* l_HashSet_foldM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_iterateMAux___main___at_HashSet_foldM___spec__2___rarg(x_1, x_2, x_4, x_5, x_6, x_3);
return x_7;
}
}
lean_object* l_HashSet_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_HashSet_foldM___rarg), 4, 0);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSet_foldM___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_HashSet_foldM___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_HashSet_foldM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HashSet_foldM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_AssocList_foldlM___main___at_HashSet_fold___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_apply_2(x_1, x_2, x_4);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
}
}
lean_object* l_AssocList_foldlM___main___at_HashSet_fold___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_AssocList_foldlM___main___at_HashSet_fold___spec__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSet_fold___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = l_AssocList_foldlM___main___at_HashSet_fold___spec__1___rarg(x_1, x_5, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_HashSet_fold___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_HashSet_fold___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_HashSet_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at_HashSet_fold___spec__2___rarg(x_1, x_3, x_4, x_5, x_2);
return x_6;
}
}
lean_object* l_HashSet_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_HashSet_fold___rarg___boxed), 3, 0);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSet_fold___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_HashSet_fold___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_HashSet_fold___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashSet_fold___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_HashSet_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HashSet_fold(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init_Data_HashMap(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_HashSet(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_HashMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

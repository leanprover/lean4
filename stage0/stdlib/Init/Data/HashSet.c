// Lean compiler output
// Module: Init.Data.HashSet
// Imports: Init.Data.Array.Basic Init.Data.List.Control Init.Data.Option.Basic Init.Data.Hashable
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
lean_object* l_List_erase___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_isEmpty(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashSetImp___rarg(lean_object*);
lean_object* l_HashSet_numBuckets___rarg(lean_object*);
uint8_t l_HashSet_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_HashSet_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_reinsertAux(lean_object*);
uint8_t l_List_elem___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_isEmpty___rarg___boxed(lean_object*);
lean_object* l_HashSet_find_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_toArray(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_toArray___rarg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_toArray___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_HashSetImp_fold___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_HashSet_fold___spec__1(lean_object*, lean_object*);
lean_object* l_HashSet_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_fold___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_HashSet_toArray___spec__1(lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_foldM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_find_x3f(lean_object*);
lean_object* l_HashSet_size___rarg___boxed(lean_object*);
lean_object* l_HashSet_Inhabited(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_HashSet_contains(lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSetImp_fold___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_toArray___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_find_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l_HashSetImp_contains(lean_object*);
lean_object* l_HashSet_size___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_mkIdx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_foldM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_HashSet_isEmpty___rarg(lean_object*);
lean_object* l_HashSet_insert(lean_object*);
lean_object* l_HashSetImp_insert(lean_object*);
lean_object* l_HashSetImp_foldM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_HashSetImp_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_toArray___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_contains___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_HasEmptyc___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_expand___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetBucket_update___rarg(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_HashSetImp_fold___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_toList___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_reinsertAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_fold(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_HashSetImp_find_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkHashSetImp___rarg___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_HashSet_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldBucketsM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_toArray___rarg___boxed(lean_object*);
lean_object* l_mkHashSet___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldM___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_toList___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_foldM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_size(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_HashSet_toList___spec__1(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_toList___spec__2(lean_object*);
lean_object* l_HashSetImp_foldBuckets(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldBuckets___spec__2(lean_object*, lean_object*);
lean_object* l_HashSetImp_expand(lean_object*);
lean_object* l_HashSetImp_moveEntries___main(lean_object*);
lean_object* l_HashSet_toList___rarg___boxed(lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_fold___spec__2(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldBucketsM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_HasEmptyc(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_HashSetImp_fold___spec__1(lean_object*, lean_object*);
lean_object* l_HashSetImp_erase(lean_object*);
lean_object* l_mkHashSet___rarg(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_HashSetImp_foldBuckets___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_moveEntries(lean_object*);
lean_object* l_HashSetImp_foldM(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_HashSetImp_foldBuckets___spec__1(lean_object*, lean_object*);
lean_object* l_HashSet_Inhabited___closed__1;
lean_object* l_List_foldlM___main___at_HashSet_toArray___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_HashSet_numBuckets(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldBuckets___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_find_x3f(lean_object*);
lean_object* l_List_replace___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_foldBucketsM(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_fold(lean_object*, lean_object*);
lean_object* l_mkHashSetImp___rarg___closed__1;
lean_object* l_HashSetImp_moveEntries___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_HashSet_toList___spec__1___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_HashSet_contains___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_empty(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_Inhabited___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_toList___rarg(lean_object*);
lean_object* l_List_foldl___main___at_HashSetImp_moveEntries___main___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_HashSet_fold___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_fold___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_moveEntries___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_foldM___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_erase___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_HashSet_numBuckets___rarg___boxed(lean_object*);
lean_object* l_HashSetBucket_update(lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSetImp_fold___spec__2(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSet_toArray___spec__2(lean_object*);
lean_object* l_HashSetImp_foldBucketsM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_toList___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashSet(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetBucket_update___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_HashSetImp_foldBuckets___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_HashSet_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_fold___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_erase___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldBucketsM___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_size___rarg(lean_object*);
lean_object* l_HashSet_toList(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_numBuckets___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_foldBuckets___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_HashSetImp_mkIdx(lean_object*, lean_object*, size_t);
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldBuckets___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_HashSetImp_moveEntries___main___spec__1(lean_object*);
lean_object* l_Array_iterateMAux___main___at_HashSetImp_fold___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_fold___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSet_empty___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashSetImp(lean_object*);
lean_object* l_HashSet_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_HashSetBucket_update___rarg(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_uset(x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_HashSetBucket_update(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HashSetBucket_update___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_HashSetBucket_update___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_HashSetBucket_update___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* _init_l_mkHashSetImp___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_mkHashSetImp___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_mkHashSetImp___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_mkHashSetImp___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_mk_array(x_1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_mkHashSetImp___rarg___closed__2;
return x_7;
}
}
}
lean_object* l_mkHashSetImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_mkHashSetImp___rarg), 1, 0);
return x_2;
}
}
size_t l_HashSetImp_mkIdx(lean_object* x_1, lean_object* x_2, size_t x_3) {
_start:
{
size_t x_4; 
x_4 = lean_usize_modn(x_3, x_1);
return x_4;
}
}
lean_object* l_HashSetImp_mkIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_5 = l_HashSetImp_mkIdx(x_1, x_2, x_4);
lean_dec(x_1);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* l_HashSetImp_reinsertAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_array_get_size(x_2);
lean_inc(x_3);
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_2, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_array_uset(x_2, x_7, x_9);
return x_10;
}
}
lean_object* l_HashSetImp_reinsertAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HashSetImp_reinsertAux___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldBucketsM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_inc(x_3);
lean_inc(x_1);
x_14 = l_List_foldlM___main___rarg(x_1, lean_box(0), lean_box(0), x_3, x_6, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
x_17 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_HashSetImp_foldBucketsM___spec__1___rarg___boxed), 6, 5);
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
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldBucketsM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_HashSetImp_foldBucketsM___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
lean_object* l_HashSetImp_foldBucketsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_6 = l_Array_iterateMAux___main___at_HashSetImp_foldBucketsM___spec__1___rarg(x_1, x_2, x_4, x_2, x_5, x_3);
return x_6;
}
}
lean_object* l_HashSetImp_foldBucketsM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_HashSetImp_foldBucketsM___rarg), 4, 0);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldBucketsM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_HashSetImp_foldBucketsM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_List_foldlM___main___at_HashSetImp_foldBuckets___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_ctor_get(x_3, 1);
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
lean_object* l_List_foldlM___main___at_HashSetImp_foldBuckets___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldlM___main___at_HashSetImp_foldBuckets___spec__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldBuckets___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_2);
x_9 = l_List_foldlM___main___at_HashSetImp_foldBuckets___spec__1___rarg(x_2, x_5, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldBuckets___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_HashSetImp_foldBuckets___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_HashSetImp_foldBuckets___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___main___at_HashSetImp_foldBuckets___spec__2___rarg(x_1, x_3, x_1, x_4, x_2);
return x_5;
}
}
lean_object* l_HashSetImp_foldBuckets(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_HashSetImp_foldBuckets___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldBuckets___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_HashSetImp_foldBuckets___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_HashSetImp_foldBuckets___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashSetImp_foldBuckets___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_14 = l_List_foldlM___main___rarg(x_1, lean_box(0), lean_box(0), x_2, x_6, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
x_17 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_HashSetImp_foldM___spec__1___rarg___boxed), 6, 5);
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
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_HashSetImp_foldM___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
lean_object* l_HashSetImp_foldM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_iterateMAux___main___at_HashSetImp_foldM___spec__1___rarg(x_1, x_2, x_4, x_5, x_6, x_3);
return x_7;
}
}
lean_object* l_HashSetImp_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_HashSetImp_foldM___rarg), 4, 0);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSetImp_foldM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_HashSetImp_foldM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_List_foldlM___main___at_HashSetImp_fold___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_ctor_get(x_3, 1);
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
lean_object* l_List_foldlM___main___at_HashSetImp_fold___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldlM___main___at_HashSetImp_fold___spec__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSetImp_fold___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = l_List_foldlM___main___at_HashSetImp_fold___spec__1___rarg(x_1, x_5, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_HashSetImp_fold___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_HashSetImp_fold___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_HashSetImp_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at_HashSetImp_fold___spec__2___rarg(x_1, x_3, x_4, x_5, x_2);
return x_6;
}
}
lean_object* l_HashSetImp_fold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_HashSetImp_fold___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSetImp_fold___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_HashSetImp_fold___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_HashSetImp_fold___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashSetImp_fold___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_HashSetImp_find_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_array_get_size(x_5);
lean_inc(x_4);
x_7 = lean_apply_1(x_2, x_4);
x_8 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_apply_1(x_1, x_4);
x_11 = lean_array_uget(x_5, x_9);
x_12 = l_List_find_x3f___main___rarg(x_10, x_11);
return x_12;
}
}
lean_object* l_HashSetImp_find_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HashSetImp_find_x3f___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_HashSetImp_find_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HashSetImp_find_x3f___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
uint8_t l_HashSetImp_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_array_get_size(x_5);
lean_inc(x_4);
x_7 = lean_apply_1(x_2, x_4);
x_8 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_5, x_9);
x_11 = l_List_elem___main___rarg(x_1, x_4, x_10);
return x_11;
}
}
lean_object* l_HashSetImp_contains(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HashSetImp_contains___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_HashSetImp_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_HashSetImp_contains___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_List_foldl___main___at_HashSetImp_moveEntries___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_10 = lean_usize_modn(x_9, x_7);
lean_dec(x_7);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 1, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_17 = lean_apply_1(x_1, x_14);
x_18 = lean_unbox_usize(x_17);
lean_dec(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_2, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_uset(x_2, x_19, x_21);
x_2 = x_22;
x_3 = x_15;
goto _start;
}
}
}
}
lean_object* l_List_foldl___main___at_HashSetImp_moveEntries___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___main___at_HashSetImp_moveEntries___main___spec__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_HashSetImp_moveEntries___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_box(0);
x_9 = lean_array_fset(x_3, x_2, x_8);
lean_inc(x_1);
x_10 = l_List_foldl___main___at_HashSetImp_moveEntries___main___spec__1___rarg(x_1, x_4, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
x_2 = x_12;
x_3 = x_9;
x_4 = x_10;
goto _start;
}
}
}
lean_object* l_HashSetImp_moveEntries___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HashSetImp_moveEntries___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_HashSetImp_moveEntries___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HashSetImp_moveEntries___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_HashSetImp_moveEntries(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HashSetImp_moveEntries___rarg), 4, 0);
return x_2;
}
}
lean_object* l_HashSetImp_expand___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_mul(x_4, x_5);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_mk_array(x_6, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_HashSetImp_moveEntries___main___rarg(x_1, x_9, x_3, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
lean_object* l_HashSetImp_expand(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HashSetImp_expand___rarg), 3, 0);
return x_2;
}
}
lean_object* l_HashSetImp_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_array_get_size(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_9 = lean_apply_1(x_2, x_4);
x_10 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_11 = lean_usize_modn(x_10, x_8);
x_12 = lean_array_uget(x_7, x_11);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_List_elem___main___rarg(x_1, x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_12);
x_17 = lean_array_uset(x_7, x_11, x_16);
x_18 = lean_nat_dec_le(x_15, x_8);
lean_dec(x_8);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_3);
x_19 = l_HashSetImp_expand___rarg(x_2, x_15, x_17);
return x_19;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_2);
lean_inc(x_4);
x_20 = l_List_replace___main___rarg(x_1, x_12, x_4, x_4);
x_21 = lean_array_uset(x_7, x_11, x_20);
lean_ctor_set(x_3, 1, x_21);
return x_3;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = lean_array_get_size(x_23);
lean_inc(x_2);
lean_inc(x_4);
x_25 = lean_apply_1(x_2, x_4);
x_26 = lean_unbox_usize(x_25);
lean_dec(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
lean_inc(x_28);
lean_inc(x_4);
lean_inc(x_1);
x_29 = l_List_elem___main___rarg(x_1, x_4, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_1);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = lean_nat_dec_le(x_31, x_24);
lean_dec(x_24);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_HashSetImp_expand___rarg(x_2, x_31, x_33);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_24);
lean_dec(x_2);
lean_inc(x_4);
x_37 = l_List_replace___main___rarg(x_1, x_28, x_4, x_4);
x_38 = lean_array_uset(x_23, x_27, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l_HashSetImp_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HashSetImp_insert___rarg), 4, 0);
return x_2;
}
}
lean_object* l_HashSetImp_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_inc(x_4);
x_8 = lean_apply_1(x_2, x_4);
x_9 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_10 = lean_usize_modn(x_9, x_7);
lean_dec(x_7);
x_11 = lean_array_uget(x_6, x_10);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_1);
x_12 = l_List_elem___main___rarg(x_1, x_4, x_11);
if (x_12 == 0)
{
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_3, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_5, x_16);
lean_dec(x_5);
x_18 = l_List_erase___main___rarg(x_1, x_11, x_4);
x_19 = lean_array_uset(x_6, x_10, x_18);
lean_ctor_set(x_3, 1, x_19);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_5, x_20);
lean_dec(x_5);
x_22 = l_List_erase___main___rarg(x_1, x_11, x_4);
x_23 = lean_array_uset(x_6, x_10, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_HashSetImp_erase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HashSetImp_erase___rarg), 4, 0);
return x_2;
}
}
lean_object* l_mkHashSet___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashSetImp___rarg(x_1);
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
lean_object* _init_l_HashSet_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashSetImp___rarg(x_1);
return x_2;
}
}
lean_object* l_HashSet_Inhabited(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashSet_Inhabited___closed__1;
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
x_4 = l_HashSet_Inhabited___closed__1;
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
lean_object* x_5; 
x_5 = l_HashSetImp_insert___rarg(x_1, x_2, x_3, x_4);
return x_5;
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
x_5 = l_HashSetImp_erase___rarg(x_1, x_2, x_3, x_4);
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
x_5 = l_HashSetImp_find_x3f___rarg(x_1, x_2, x_3, x_4);
return x_5;
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
x_5 = l_HashSetImp_contains___rarg(x_1, x_2, x_3, x_4);
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
lean_object* l_Array_iterateMAux___main___at_HashSet_foldM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_14 = l_List_foldlM___main___rarg(x_1, lean_box(0), lean_box(0), x_2, x_6, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
x_17 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_HashSet_foldM___spec__1___rarg___boxed), 6, 5);
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
lean_object* l_Array_iterateMAux___main___at_HashSet_foldM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_HashSet_foldM___spec__1___rarg___boxed), 6, 0);
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
x_7 = l_Array_iterateMAux___main___at_HashSet_foldM___spec__1___rarg(x_1, x_2, x_4, x_5, x_6, x_3);
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
lean_object* l_Array_iterateMAux___main___at_HashSet_foldM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_HashSet_foldM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_List_foldlM___main___at_HashSet_fold___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_ctor_get(x_3, 1);
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
lean_object* l_List_foldlM___main___at_HashSet_fold___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldlM___main___at_HashSet_fold___spec__1___rarg), 3, 0);
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
x_9 = l_List_foldlM___main___at_HashSet_fold___spec__1___rarg(x_1, x_5, x_8);
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
x_4 = l_HashSet_Inhabited___closed__1;
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
lean_object* l_List_foldlM___main___at_HashSet_toList___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_ctor_set(x_2, 1, x_1);
x_1 = x_2;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
x_1 = x_8;
x_2 = x_7;
goto _start;
}
}
}
}
lean_object* l_List_foldlM___main___at_HashSet_toList___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldlM___main___at_HashSet_toList___spec__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSet_toList___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_List_foldlM___main___at_HashSet_toList___spec__1___rarg(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_HashSet_toList___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_HashSet_toList___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_HashSet_toList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___main___at_HashSet_toList___spec__2___rarg(x_1, x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_HashSet_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_HashSet_toList___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSet_toList___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_HashSet_toList___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_HashSet_toList___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HashSet_toList___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_HashSet_toList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashSet_toList(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_foldlM___main___at_HashSet_toArray___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_push(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_List_foldlM___main___at_HashSet_toArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldlM___main___at_HashSet_toArray___spec__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSet_toArray___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_List_foldlM___main___at_HashSet_toArray___spec__1___rarg(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_HashSet_toArray___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_HashSet_toArray___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_HashSet_toArray___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_empty___closed__1;
x_5 = l_Array_iterateMAux___main___at_HashSet_toArray___spec__2___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_HashSet_toArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_HashSet_toArray___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_HashSet_toArray___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_HashSet_toArray___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_HashSet_toArray___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HashSet_toArray___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_HashSet_toArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashSet_toArray(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_HashSet_numBuckets___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
lean_object* l_HashSet_numBuckets(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_HashSet_numBuckets___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_HashSet_numBuckets___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HashSet_numBuckets___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_HashSet_numBuckets___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HashSet_numBuckets(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Data_Array_Basic(lean_object*);
lean_object* initialize_Init_Data_List_Control(lean_object*);
lean_object* initialize_Init_Data_Option_Basic(lean_object*);
lean_object* initialize_Init_Data_Hashable(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_HashSet(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_mkHashSetImp___rarg___closed__1 = _init_l_mkHashSetImp___rarg___closed__1();
lean_mark_persistent(l_mkHashSetImp___rarg___closed__1);
l_mkHashSetImp___rarg___closed__2 = _init_l_mkHashSetImp___rarg___closed__2();
lean_mark_persistent(l_mkHashSetImp___rarg___closed__2);
l_HashSet_Inhabited___closed__1 = _init_l_HashSet_Inhabited___closed__1();
lean_mark_persistent(l_HashSet_Inhabited___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

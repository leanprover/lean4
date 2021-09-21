// Lean compiler output
// Module: Std.Data.BinomialHeap
// Imports: Init
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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_merge___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_hRank___rarg(lean_object*);
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeap_ofList___spec__1___at_Std_BinomialHeap_ofList___spec__2(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArray_go(lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_ofArray___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_singleton___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_head___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Std_BinomialHeapImp_toArrayUnordered_go___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_findMin(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_head_x3f(lean_object*);
lean_object* l_List_foldl___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_tail_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_isEmpty___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_insert(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_tail_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_instInhabitedHeap(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_combine___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_head_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_mergeNodes(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_head___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Std_BinomialHeapImp_toListUnordered___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_findMin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_insert___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_BinomialHeapImp_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeap_ofList___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_join___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_singleton(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toArrayUnordered___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_mergeNodes___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_BinomialHeap_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_head_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toList(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_head(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Std_BinomialHeapImp_toListUnordered___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___at_Std_BinomialHeap_ofArray___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toList___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArray___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_isEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_empty___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_tail_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_deleteMin___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toListUnordered___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArrayUnordered_go(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_deleteMin(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_merge___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_head(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toList(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArrayUnordered_go___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_deleteMin(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_singleton(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toListUnordered___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeapImp_deleteMin___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toArray___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Std_BinomialHeapImp_toListUnordered___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeapImp_deleteMin___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_mkBinomialHeap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_tail_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeap_ofList___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeap_ofList___spec__1___at_Std_BinomialHeap_ofList___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_head___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toListUnordered___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_ofList(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArrayUnordered___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Std_BinomialHeapImp_toArrayUnordered_go___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Std_BinomialHeapImp_toArrayUnordered_go___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toListUnordered(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_head_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toListUnordered(lean_object*);
static lean_object* l_Std_BinomialHeapImp_toArray___rarg___closed__1;
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeapImp_deleteMin___spec__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_eraseIdx___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArrayUnordered(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toList___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArray_go___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_hRank(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_merge(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_head___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Std_BinomialHeapImp_toListUnordered___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___at_Std_BinomialHeap_ofArray___spec__2___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_tail(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_tail___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___at_Std_BinomialHeap_ofArray___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_hRank___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_head_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkBinomialHeap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_isEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toArrayUnordered(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_isEmpty___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeap_ofList___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_merge(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_deleteMin___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_combine(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_ofArray___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_tail___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_singleton___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_singleton___rarg(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Std_BinomialHeapImp_toArrayUnordered_go___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeapImp_deleteMin___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_ofList___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_tail(lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toArrayUnordered___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_instInhabitedHeap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_hRank___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_hRank(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_hRank___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_hRank___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_BinomialHeapImp_hRank___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_BinomialHeapImp_isEmpty___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_isEmpty___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_BinomialHeapImp_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_singleton___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_singleton(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_singleton___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_combine___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_4);
x_10 = lean_apply_2(x_1, x_4, x_7);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_2, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_2, 0);
lean_dec(x_15);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_8, x_16);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_List_appendTR___rarg(x_9, x_20);
lean_ctor_set(x_2, 2, x_21);
lean_ctor_set(x_2, 1, x_17);
return x_2;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_8, x_22);
lean_dec(x_8);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_List_appendTR___rarg(x_9, x_26);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_3);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_3, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_3, 0);
lean_dec(x_32);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_5, x_33);
lean_dec(x_5);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_List_appendTR___rarg(x_6, x_37);
lean_ctor_set(x_3, 2, x_38);
lean_ctor_set(x_3, 1, x_34);
return x_3;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_3);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_5, x_39);
lean_dec(x_5);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_2);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_List_appendTR___rarg(x_6, x_43);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_combine(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_combine___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_mergeNodes___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = lean_nat_dec_lt(x_9, x_8);
lean_dec(x_8);
lean_dec(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_2);
lean_inc(x_1);
x_15 = l_Std_BinomialHeapImp_combine___rarg(x_1, x_4, x_6);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = l_Std_BinomialHeapImp_hRank___rarg(x_5);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Std_BinomialHeapImp_hRank___rarg(x_7);
x_20 = lean_nat_dec_eq(x_16, x_19);
lean_dec(x_19);
lean_dec(x_16);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l_Std_BinomialHeapImp_mergeNodes___rarg(x_1, x_5, x_7);
lean_ctor_set(x_3, 1, x_21);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_ctor_set(x_3, 1, x_5);
lean_ctor_set(x_3, 0, x_15);
x_2 = x_3;
x_3 = x_7;
goto _start;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Std_BinomialHeapImp_hRank___rarg(x_7);
x_24 = lean_nat_dec_eq(x_16, x_23);
lean_dec(x_23);
lean_dec(x_16);
if (x_24 == 0)
{
lean_ctor_set(x_3, 0, x_15);
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; 
x_26 = l_Std_BinomialHeapImp_mergeNodes___rarg(x_1, x_5, x_7);
lean_ctor_set(x_3, 1, x_26);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_5);
lean_dec(x_4);
x_27 = l_Std_BinomialHeapImp_mergeNodes___rarg(x_1, x_7, x_2);
lean_ctor_set(x_3, 1, x_27);
return x_3;
}
}
else
{
uint8_t x_28; 
lean_dec(x_3);
x_28 = lean_nat_dec_lt(x_9, x_8);
lean_dec(x_8);
lean_dec(x_9);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_2);
lean_inc(x_1);
x_29 = l_Std_BinomialHeapImp_combine___rarg(x_1, x_4, x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = l_Std_BinomialHeapImp_hRank___rarg(x_5);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Std_BinomialHeapImp_hRank___rarg(x_7);
x_34 = lean_nat_dec_eq(x_30, x_33);
lean_dec(x_33);
lean_dec(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Std_BinomialHeapImp_mergeNodes___rarg(x_1, x_5, x_7);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_5);
x_2 = x_37;
x_3 = x_7;
goto _start;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Std_BinomialHeapImp_hRank___rarg(x_7);
x_40 = lean_nat_dec_eq(x_30, x_39);
lean_dec(x_39);
lean_dec(x_30);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_7);
x_2 = x_5;
x_3 = x_41;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Std_BinomialHeapImp_mergeNodes___rarg(x_1, x_5, x_7);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_5);
lean_dec(x_4);
x_45 = l_Std_BinomialHeapImp_mergeNodes___rarg(x_1, x_7, x_2);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_6);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_inc(x_3);
x_47 = l_Std_BinomialHeapImp_mergeNodes___rarg(x_1, x_5, x_3);
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_3, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_3, 0);
lean_dec(x_50);
lean_ctor_set(x_3, 1, x_47);
lean_ctor_set(x_3, 0, x_4);
return x_3;
}
else
{
lean_object* x_51; 
lean_dec(x_3);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_mergeNodes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_mergeNodes___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_merge___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_BinomialHeapImp_mergeNodes___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_merge(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_merge___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_head_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_5 = lean_apply_2(x_1, x_2, x_4);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_dec(x_4);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_head_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_head_x3f___rarg___lambda__1), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_List_foldl___rarg(x_6, x_7, x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_head_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_head_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_head___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_BinomialHeapImp_head_x3f___rarg(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_head(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_head___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_head___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_BinomialHeapImp_head___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_findMin___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_10, x_11);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_5);
x_2 = x_6;
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_3, x_17);
lean_dec(x_3);
x_2 = x_6;
x_3 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_inc(x_1);
x_24 = lean_apply_2(x_1, x_22, x_23);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_3);
x_2 = x_6;
x_3 = x_27;
x_4 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_5);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_3, x_30);
lean_dec(x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
x_2 = x_6;
x_3 = x_31;
x_4 = x_32;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_findMin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_findMin___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeapImp_deleteMin___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_Std_BinomialHeapImp_mergeNodes___rarg(x_1, x_2, x_4);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeapImp_deleteMin___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_Std_BinomialHeapImp_deleteMin___spec__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeapImp_deleteMin___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_Std_BinomialHeapImp_mergeNodes___rarg(x_1, x_2, x_4);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeapImp_deleteMin___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_Std_BinomialHeapImp_deleteMin___spec__2___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_deleteMin___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_List_foldl___at_Std_BinomialHeapImp_deleteMin___spec__1___rarg(x_1, x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_21 = l_Std_BinomialHeapImp_findMin___rarg(x_1, x_4, x_20, x_19);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l_List_eraseIdx___rarg(x_2, x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_List_foldl___at_Std_BinomialHeapImp_deleteMin___spec__2___rarg(x_1, x_25, x_27);
lean_ctor_set(x_21, 1, x_28);
lean_ctor_set(x_21, 0, x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_21);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = l_List_eraseIdx___rarg(x_2, x_31);
lean_dec(x_31);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 2);
lean_inc(x_34);
lean_dec(x_30);
x_35 = l_List_foldl___at_Std_BinomialHeapImp_deleteMin___spec__2___rarg(x_1, x_32, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_deleteMin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_deleteMin___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_tail_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_BinomialHeapImp_deleteMin___rarg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_tail_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_tail_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_tail___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_BinomialHeapImp_deleteMin___rarg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_tail(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_tail___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Std_BinomialHeapImp_deleteMin___rarg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Std_BinomialHeapImp_toList___rarg(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_toList___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArray_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Std_BinomialHeapImp_deleteMin___rarg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_array_push(x_2, x_6);
x_2 = x_8;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArray_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_toArray_go___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Std_BinomialHeapImp_toArray___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_BinomialHeapImp_toArray___rarg___closed__1;
x_4 = l_Std_BinomialHeapImp_toArray_go___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_toArray___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Std_BinomialHeapImp_toListUnordered___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Std_BinomialHeapImp_toListUnordered___rarg(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Std_BinomialHeapImp_toListUnordered___rarg(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Std_BinomialHeapImp_toListUnordered___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mapTRAux___at_Std_BinomialHeapImp_toListUnordered___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Std_BinomialHeapImp_toListUnordered___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = l_List_mapTRAux___at_Std_BinomialHeapImp_toListUnordered___spec__1___rarg(x_8, x_9);
x_11 = l_List_join___rarg(x_10);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_7);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_6;
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = l_List_mapTRAux___at_Std_BinomialHeapImp_toListUnordered___spec__1___rarg(x_17, x_18);
x_20 = l_List_join___rarg(x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
x_1 = x_15;
x_2 = x_22;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Std_BinomialHeapImp_toListUnordered___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mapTRAux___at_Std_BinomialHeapImp_toListUnordered___spec__2___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toListUnordered___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_List_mapTRAux___at_Std_BinomialHeapImp_toListUnordered___spec__2___rarg(x_1, x_2);
x_4 = l_List_join___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toListUnordered(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_toListUnordered___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Std_BinomialHeapImp_toArrayUnordered_go___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_List_forIn_loop___at_Std_BinomialHeapImp_toArrayUnordered_go___spec__2___rarg(x_3, x_2);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Std_BinomialHeapImp_toArrayUnordered_go___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Std_BinomialHeapImp_toArrayUnordered_go___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Std_BinomialHeapImp_toArrayUnordered_go___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_array_push(x_2, x_5);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_List_forIn_loop___at_Std_BinomialHeapImp_toArrayUnordered_go___spec__1___rarg(x_7, x_6);
x_1 = x_4;
x_2 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Std_BinomialHeapImp_toArrayUnordered_go___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Std_BinomialHeapImp_toArrayUnordered_go___spec__2___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArrayUnordered_go___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_forIn_loop___at_Std_BinomialHeapImp_toArrayUnordered_go___spec__2___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArrayUnordered_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_toArrayUnordered_go___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArrayUnordered___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_BinomialHeapImp_toArray___rarg___closed__1;
x_3 = l_List_forIn_loop___at_Std_BinomialHeapImp_toArrayUnordered_go___spec__2___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeapImp_toArrayUnordered(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeapImp_toArrayUnordered___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkBinomialHeap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_mkBinomialHeap___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_mkBinomialHeap(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_empty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_BinomialHeap_empty(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_BinomialHeap_isEmpty___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Std_BinomialHeapImp_isEmpty___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_isEmpty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_BinomialHeap_isEmpty___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_BinomialHeap_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_isEmpty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_BinomialHeap_isEmpty(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_singleton___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_BinomialHeapImp_singleton___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_singleton(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_BinomialHeap_singleton___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_singleton___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_BinomialHeap_singleton(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_merge___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_BinomialHeapImp_mergeNodes___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_merge(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeap_merge___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_BinomialHeapImp_singleton___rarg(x_2);
x_5 = l_Std_BinomialHeapImp_mergeNodes___rarg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeap_insert___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeap_ofList___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
x_7 = lean_apply_2(x_2, x_5, x_3);
x_3 = x_7;
x_4 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeap_ofList___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_Std_BinomialHeap_ofList___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeap_ofList___spec__1___at_Std_BinomialHeap_ofList___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Std_BinomialHeapImp_singleton___rarg(x_4);
lean_inc(x_1);
x_7 = l_Std_BinomialHeapImp_mergeNodes___rarg(x_1, x_6, x_2);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeap_ofList___spec__1___at_Std_BinomialHeap_ofList___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_Std_BinomialHeap_ofList___spec__1___at_Std_BinomialHeap_ofList___spec__2___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_ofList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_foldl___at_Std_BinomialHeap_ofList___spec__1___at_Std_BinomialHeap_ofList___spec__2___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_ofList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeap_ofList___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_BinomialHeap_ofList___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldl___at_Std_BinomialHeap_ofList___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_4 == x_5;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_9 = lean_apply_2(x_2, x_8, x_6);
x_10 = 1;
x_11 = x_4 + x_10;
x_4 = x_11;
x_6 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___at_Std_BinomialHeap_ofArray___spec__2___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Std_BinomialHeapImp_singleton___rarg(x_7);
x_9 = 1;
x_10 = x_3 + x_9;
lean_inc(x_1);
x_11 = l_Std_BinomialHeapImp_mergeNodes___rarg(x_1, x_8, x_5);
x_3 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___at_Std_BinomialHeap_ofArray___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___at_Std_BinomialHeap_ofArray___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_ofArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_box(0);
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___at_Std_BinomialHeap_ofArray___spec__2___rarg(x_1, x_2, x_8, x_9, x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_ofArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeap_ofArray___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___at_Std_BinomialHeap_ofArray___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Std_BinomialHeap_ofArray___spec__1___at_Std_BinomialHeap_ofArray___spec__2___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_ofArray___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_BinomialHeap_ofArray___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_deleteMin___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_BinomialHeapImp_deleteMin___rarg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
if (lean_is_scalar(x_14)) {
 x_15 = lean_alloc_ctor(0, 2, 0);
} else {
 x_15 = x_14;
}
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_deleteMin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeap_deleteMin___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_head___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_BinomialHeapImp_head_x3f___rarg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_head(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeap_head___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_head___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_BinomialHeap_head___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_head_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_BinomialHeapImp_head_x3f___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_head_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeap_head_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_tail_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_BinomialHeapImp_deleteMin___rarg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_tail_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeap_tail_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_tail___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_BinomialHeapImp_deleteMin___rarg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_tail(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeap_tail___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_BinomialHeapImp_toList___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeap_toList___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_BinomialHeapImp_toArray___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_BinomialHeap_toArray___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toListUnordered___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_BinomialHeapImp_toListUnordered___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toListUnordered(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_BinomialHeap_toListUnordered___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toListUnordered___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_BinomialHeap_toListUnordered(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toArrayUnordered___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_BinomialHeapImp_toArrayUnordered___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toArrayUnordered(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_BinomialHeap_toArrayUnordered___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BinomialHeap_toArrayUnordered___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_BinomialHeap_toArrayUnordered(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_BinomialHeap(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_BinomialHeapImp_toArray___rarg___closed__1 = _init_l_Std_BinomialHeapImp_toArray___rarg___closed__1();
lean_mark_persistent(l_Std_BinomialHeapImp_toArray___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

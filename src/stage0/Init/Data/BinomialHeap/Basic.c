// Lean compiler output
// Module: Init.Data.BinomialHeap.Basic
// Imports: Init.Data.List.Default Init.Coe
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
lean_object* l_BinomialHeapImp_Inhabited(lean_object*);
lean_object* l_mkBinomialHeap(lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_findMin___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkBinomialHeap___boxed(lean_object*, lean_object*);
lean_object* l_BinomialHeap_singleton___rarg(lean_object*);
lean_object* l_BinomialHeap_isEmpty___boxed(lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_toList___rarg(lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_headOpt(lean_object*);
lean_object* l_BinomialHeapImp_tail___rarg(lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_combine___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_tail(lean_object*);
lean_object* l_BinomialHeap_headOpt(lean_object*);
lean_object* l_BinomialHeapImp_headOpt___rarg(lean_object*, lean_object*);
lean_object* l_BinomialHeap_head___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BinomialHeap_merge(lean_object*);
lean_object* l_BinomialHeapImp_mergeNodes___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_singleton___rarg(lean_object*);
uint8_t l_BinomialHeap_isEmpty___rarg(lean_object*);
lean_object* l_BinomialHeap_tail___rarg(lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_hRank(lean_object*);
lean_object* l_BinomialHeapImp_mergeNodes(lean_object*);
lean_object* l_List_foldl___main___at_BinomialHeapImp_headOpt___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_findMin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_head___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_BinomialHeapImp_head___spec__1(lean_object*);
lean_object* l_BinomialHeapImp_singleton(lean_object*);
lean_object* l_BinomialHeap_head___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_BinomialHeap_insert(lean_object*);
lean_object* l_BinomialHeapImp_findMin(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_mergeNodes___main(lean_object*);
lean_object* l_List_foldl___main___at_BinomialHeapImp_tail___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_BinomialHeap_toList(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_toList(lean_object*);
lean_object* l_BinomialHeap_empty(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_BinomialHeap_singleton(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_BinomialHeap_merge___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_BinomialHeapImp_isEmpty___rarg(lean_object*);
lean_object* l_List_foldl___main___at_BinomialHeapImp_tail___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_BinomialHeapImp_tail___spec__1(lean_object*);
lean_object* l_BinomialHeapImp_head(lean_object*);
lean_object* l_BinomialHeap_empty___boxed(lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_head___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BinomialHeap_insert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_BinomialHeapImp_tail___spec__2(lean_object*);
lean_object* l_BinomialHeap_isEmpty(lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_merge(lean_object*);
lean_object* l_List_foldl___main___at_BinomialHeapImp_headOpt___spec__1(lean_object*);
lean_object* l_BinomialHeapImp_isEmpty(lean_object*);
lean_object* l_BinomialHeap_headOpt___rarg(lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_hRank___rarg___boxed(lean_object*);
lean_object* l_BinomialHeapImp_toList___main(lean_object*);
lean_object* l_BinomialHeapImp_mergeNodes___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_combine(lean_object*);
lean_object* l_BinomialHeap_isEmpty___rarg___boxed(lean_object*);
lean_object* l_BinomialHeapImp_findMin___main(lean_object*);
lean_object* l_BinomialHeap_head(lean_object*);
lean_object* l_List_foldl___main___at_BinomialHeapImp_head___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_isEmpty___rarg___boxed(lean_object*);
lean_object* l_BinomialHeap_toList___rarg(lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_toList___main___rarg(lean_object*, lean_object*);
lean_object* l_List_eraseIdx___main___rarg(lean_object*, lean_object*);
lean_object* l_BinomialHeap_singleton___boxed(lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_merge___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_BinomialHeapImp_hRank___rarg(lean_object*);
lean_object* l_BinomialHeap_tail(lean_object*);
lean_object* l_BinomialHeapImp_Inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_BinomialHeapImp_hRank___rarg(lean_object* x_1) {
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
lean_object* l_BinomialHeapImp_hRank(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeapImp_hRank___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_BinomialHeapImp_hRank___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BinomialHeapImp_hRank___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_BinomialHeapImp_isEmpty___rarg(lean_object* x_1) {
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
lean_object* l_BinomialHeapImp_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeapImp_isEmpty___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_BinomialHeapImp_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_BinomialHeapImp_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_BinomialHeapImp_singleton___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
lean_object* l_BinomialHeapImp_singleton(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeapImp_singleton___rarg), 1, 0);
return x_2;
}
}
lean_object* l_BinomialHeapImp_combine___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
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
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = l_List_append___rarg(x_9, x_21);
lean_ctor_set(x_2, 2, x_22);
lean_ctor_set(x_2, 1, x_17);
return x_2;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_8, x_23);
lean_dec(x_8);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
x_29 = l_List_append___rarg(x_9, x_28);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_3);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_3, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_3, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_3, 0);
lean_dec(x_34);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_5, x_35);
lean_dec(x_5);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_41 = l_List_append___rarg(x_6, x_40);
lean_ctor_set(x_3, 2, x_41);
lean_ctor_set(x_3, 1, x_36);
return x_3;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_5, x_42);
lean_dec(x_5);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_2);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
x_48 = l_List_append___rarg(x_6, x_47);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_4);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_49, 2, x_48);
return x_49;
}
}
}
}
lean_object* l_BinomialHeapImp_combine(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeapImp_combine___rarg), 3, 0);
return x_2;
}
}
lean_object* l_BinomialHeapImp_mergeNodes___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_15 = l_BinomialHeapImp_combine___rarg(x_1, x_4, x_6);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = l_BinomialHeapImp_hRank___rarg(x_5);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_BinomialHeapImp_hRank___rarg(x_7);
x_20 = lean_nat_dec_eq(x_16, x_19);
lean_dec(x_19);
lean_dec(x_16);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_5, x_7);
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
x_23 = l_BinomialHeapImp_hRank___rarg(x_7);
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
x_26 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_5, x_7);
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
x_27 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_7, x_2);
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
x_29 = l_BinomialHeapImp_combine___rarg(x_1, x_4, x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = l_BinomialHeapImp_hRank___rarg(x_5);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_BinomialHeapImp_hRank___rarg(x_7);
x_34 = lean_nat_dec_eq(x_30, x_33);
lean_dec(x_33);
lean_dec(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_5, x_7);
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
x_39 = l_BinomialHeapImp_hRank___rarg(x_7);
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
x_43 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_5, x_7);
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
x_45 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_7, x_2);
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
x_47 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_5, x_3);
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
lean_object* l_BinomialHeapImp_mergeNodes___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeapImp_mergeNodes___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_BinomialHeapImp_mergeNodes___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_BinomialHeapImp_mergeNodes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeapImp_mergeNodes___rarg), 3, 0);
return x_2;
}
}
lean_object* l_BinomialHeapImp_merge___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_4, x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_4, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
}
lean_object* l_BinomialHeapImp_merge(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeapImp_merge___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_foldl___main___at_BinomialHeapImp_headOpt___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_13);
lean_inc(x_12);
x_14 = lean_apply_2(x_1, x_12, x_13);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_12);
lean_ctor_set(x_2, 0, x_13);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_13);
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_19);
lean_inc(x_18);
x_20 = lean_apply_2(x_1, x_18, x_19);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_2 = x_22;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_24; 
lean_dec(x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_18);
x_2 = x_24;
x_3 = x_10;
goto _start;
}
}
}
}
}
}
lean_object* l_List_foldl___main___at_BinomialHeapImp_headOpt___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___main___at_BinomialHeapImp_headOpt___spec__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_BinomialHeapImp_headOpt___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = l_List_foldl___main___at_BinomialHeapImp_headOpt___spec__1___rarg(x_1, x_5, x_4);
return x_6;
}
}
}
lean_object* l_BinomialHeapImp_headOpt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeapImp_headOpt___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_foldl___main___at_BinomialHeapImp_head___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_2, x_6);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_2);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
else
{
lean_dec(x_6);
x_3 = x_5;
goto _start;
}
}
}
}
lean_object* l_List_foldl___main___at_BinomialHeapImp_head___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___main___at_BinomialHeapImp_head___spec__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_BinomialHeapImp_head___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_List_foldl___main___at_BinomialHeapImp_head___spec__1___rarg(x_2, x_7, x_6);
return x_8;
}
}
}
}
lean_object* l_BinomialHeapImp_head(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeapImp_head___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_BinomialHeapImp_head___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BinomialHeapImp_head___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_BinomialHeapImp_findMin___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_8, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_2 = x_6;
x_3 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_4, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_5);
x_2 = x_6;
x_3 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_3);
x_2 = x_6;
x_3 = x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
lean_object* l_BinomialHeapImp_findMin___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeapImp_findMin___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_BinomialHeapImp_findMin___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_BinomialHeapImp_findMin___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_BinomialHeapImp_findMin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeapImp_findMin___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_foldl___main___at_BinomialHeapImp_tail___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_BinomialHeapImp_merge___rarg(x_1, x_2, x_4);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
}
}
lean_object* l_List_foldl___main___at_BinomialHeapImp_tail___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___main___at_BinomialHeapImp_tail___spec__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_foldl___main___at_BinomialHeapImp_tail___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_BinomialHeapImp_merge___rarg(x_1, x_2, x_4);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
}
}
lean_object* l_List_foldl___main___at_BinomialHeapImp_tail___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___main___at_BinomialHeapImp_tail___spec__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_BinomialHeapImp_tail___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_free_object(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_free_object(x_2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_List_foldl___main___at_BinomialHeapImp_tail___spec__1___rarg(x_1, x_10, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_17 = l_BinomialHeapImp_findMin___main___rarg(x_1, x_6, x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_List_eraseIdx___main___rarg(x_4, x_19);
lean_dec(x_19);
lean_ctor_set(x_2, 0, x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_List_foldl___main___at_BinomialHeapImp_tail___spec__2___rarg(x_1, x_2, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = lean_box(0);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_1);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_List_foldl___main___at_BinomialHeapImp_tail___spec__1___rarg(x_1, x_29, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_36 = l_BinomialHeapImp_findMin___main___rarg(x_1, x_25, x_35, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_List_eraseIdx___main___rarg(x_23, x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_ctor_get(x_37, 2);
lean_inc(x_41);
lean_dec(x_37);
x_42 = l_List_foldl___main___at_BinomialHeapImp_tail___spec__2___rarg(x_1, x_40, x_41);
return x_42;
}
}
}
}
}
}
lean_object* l_BinomialHeapImp_tail(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeapImp_tail___rarg), 2, 0);
return x_2;
}
}
lean_object* l_BinomialHeapImp_toList___main___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_BinomialHeapImp_headOpt___rarg(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_1);
x_7 = l_BinomialHeapImp_tail___rarg(x_1, x_2);
x_8 = l_BinomialHeapImp_toList___main___rarg(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
lean_object* l_BinomialHeapImp_toList___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeapImp_toList___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l_BinomialHeapImp_toList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BinomialHeapImp_toList___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_BinomialHeapImp_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeapImp_toList___rarg), 2, 0);
return x_2;
}
}
lean_object* l_mkBinomialHeap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
lean_object* l_mkBinomialHeap___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_mkBinomialHeap(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_BinomialHeap_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
lean_object* l_BinomialHeap_empty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BinomialHeap_empty(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_BinomialHeap_isEmpty___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_BinomialHeapImp_isEmpty___rarg(x_1);
return x_2;
}
}
lean_object* l_BinomialHeap_isEmpty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BinomialHeap_isEmpty___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_BinomialHeap_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_BinomialHeap_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_BinomialHeap_isEmpty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BinomialHeap_isEmpty(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_BinomialHeap_singleton___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BinomialHeapImp_singleton___rarg(x_1);
return x_2;
}
}
lean_object* l_BinomialHeap_singleton(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BinomialHeap_singleton___rarg), 1, 0);
return x_3;
}
}
lean_object* l_BinomialHeap_singleton___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BinomialHeap_singleton(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_BinomialHeap_merge___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BinomialHeapImp_merge___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_BinomialHeap_merge(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeap_merge___rarg), 3, 0);
return x_2;
}
}
lean_object* l_BinomialHeap_head___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BinomialHeapImp_head___rarg(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_BinomialHeap_head(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeap_head___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_BinomialHeap_head___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BinomialHeap_head___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_BinomialHeap_headOpt___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BinomialHeapImp_headOpt___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_BinomialHeap_headOpt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeap_headOpt___rarg), 2, 0);
return x_2;
}
}
lean_object* l_BinomialHeap_tail___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BinomialHeapImp_tail___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_BinomialHeap_tail(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeap_tail___rarg), 2, 0);
return x_2;
}
}
lean_object* l_BinomialHeap_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_BinomialHeapImp_singleton___rarg(x_2);
x_5 = l_BinomialHeapImp_merge___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_BinomialHeap_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeap_insert___rarg), 3, 0);
return x_2;
}
}
lean_object* l_BinomialHeap_toList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BinomialHeapImp_toList___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_BinomialHeap_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BinomialHeap_toList___rarg), 2, 0);
return x_2;
}
}
lean_object* initialize_Init_Data_List_Default(lean_object*);
lean_object* initialize_Init_Coe(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_BinomialHeap_Basic(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_List_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Coe(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif

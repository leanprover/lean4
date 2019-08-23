// Lean compiler output
// Module: init.data.binomialheap.basic
// Imports: init.data.list.default init.coe
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
extern "C" {
obj* l_BinomialHeapImp_Inhabited(obj*);
obj* l_mkBinomialHeap(obj*, obj*);
obj* l_BinomialHeapImp_findMin___main___rarg(obj*, obj*, obj*, obj*);
obj* l_mkBinomialHeap___boxed(obj*, obj*);
obj* l_BinomialHeap_singleton___rarg(obj*);
obj* l_BinomialHeap_isEmpty___boxed(obj*, obj*);
obj* l_BinomialHeapImp_toList___rarg(obj*, obj*);
obj* l_BinomialHeapImp_headOpt(obj*);
obj* l_BinomialHeapImp_tail___rarg(obj*, obj*);
obj* l_BinomialHeapImp_combine___rarg(obj*, obj*, obj*);
obj* l_BinomialHeapImp_tail(obj*);
obj* l_BinomialHeap_headOpt(obj*);
obj* l_BinomialHeapImp_headOpt___rarg(obj*, obj*);
obj* l_BinomialHeap_head___rarg___boxed(obj*, obj*, obj*);
obj* l_BinomialHeap_merge(obj*);
obj* l_BinomialHeapImp_mergeNodes___main___rarg(obj*, obj*, obj*);
obj* l_BinomialHeapImp_singleton___rarg(obj*);
uint8 l_BinomialHeap_isEmpty___rarg(obj*);
obj* l_BinomialHeap_tail___rarg(obj*, obj*);
obj* l_BinomialHeapImp_hRank(obj*);
obj* l_BinomialHeapImp_mergeNodes(obj*);
obj* l_List_foldl___main___at_BinomialHeapImp_headOpt___spec__1___rarg(obj*, obj*, obj*);
obj* l_BinomialHeapImp_findMin___rarg(obj*, obj*, obj*, obj*);
obj* l_BinomialHeapImp_head___rarg(obj*, obj*, obj*);
obj* l_List_foldl___main___at_BinomialHeapImp_head___spec__1(obj*);
obj* l_BinomialHeapImp_singleton(obj*);
obj* l_BinomialHeap_head___rarg(obj*, obj*, obj*);
obj* l_BinomialHeap_insert(obj*);
obj* l_BinomialHeapImp_findMin(obj*);
uint8 lean_nat_dec_lt(obj*, obj*);
obj* l_BinomialHeapImp_mergeNodes___main(obj*);
obj* l_List_foldl___main___at_BinomialHeapImp_tail___spec__1___rarg(obj*, obj*, obj*);
obj* l_BinomialHeap_toList(obj*);
obj* l_List_append___rarg(obj*, obj*);
obj* l_BinomialHeapImp_toList(obj*);
obj* l_BinomialHeap_empty(obj*, obj*);
obj* lean_nat_add(obj*, obj*);
obj* l_BinomialHeap_singleton(obj*, obj*);
uint8 lean_nat_dec_eq(obj*, obj*);
obj* l_BinomialHeap_merge___rarg(obj*, obj*, obj*);
uint8 l_BinomialHeapImp_isEmpty___rarg(obj*);
obj* l_List_foldl___main___at_BinomialHeapImp_tail___spec__2___rarg(obj*, obj*, obj*);
obj* l_List_foldl___main___at_BinomialHeapImp_tail___spec__1(obj*);
obj* l_BinomialHeapImp_head(obj*);
obj* l_BinomialHeap_empty___boxed(obj*, obj*);
obj* l_BinomialHeapImp_head___rarg___boxed(obj*, obj*, obj*);
obj* l_BinomialHeap_insert___rarg(obj*, obj*, obj*);
obj* l_List_foldl___main___at_BinomialHeapImp_tail___spec__2(obj*);
obj* l_BinomialHeap_isEmpty(obj*, obj*);
obj* l_BinomialHeapImp_merge(obj*);
obj* l_List_foldl___main___at_BinomialHeapImp_headOpt___spec__1(obj*);
obj* l_BinomialHeapImp_isEmpty(obj*);
obj* l_BinomialHeap_headOpt___rarg(obj*, obj*);
obj* l_BinomialHeapImp_hRank___rarg___boxed(obj*);
obj* l_BinomialHeapImp_toList___main(obj*);
obj* l_BinomialHeapImp_mergeNodes___rarg(obj*, obj*, obj*);
obj* l_BinomialHeapImp_combine(obj*);
obj* l_BinomialHeap_isEmpty___rarg___boxed(obj*);
obj* l_BinomialHeapImp_findMin___main(obj*);
obj* l_BinomialHeap_head(obj*);
obj* l_List_foldl___main___at_BinomialHeapImp_head___spec__1___rarg(obj*, obj*, obj*);
obj* l_BinomialHeapImp_isEmpty___rarg___boxed(obj*);
obj* l_BinomialHeap_toList___rarg(obj*, obj*);
obj* l_BinomialHeapImp_toList___main___rarg(obj*, obj*);
obj* l_List_eraseIdx___main___rarg(obj*, obj*);
obj* l_BinomialHeap_singleton___boxed(obj*, obj*);
obj* l_BinomialHeapImp_merge___rarg(obj*, obj*, obj*);
obj* l_BinomialHeapImp_hRank___rarg(obj*);
obj* l_BinomialHeap_tail(obj*);
obj* l_BinomialHeapImp_Inhabited(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_BinomialHeapImp_hRank___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::mk_nat_obj(0u);
return x_2;
}
else
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
return x_4;
}
}
}
obj* l_BinomialHeapImp_hRank(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeapImp_hRank___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_BinomialHeapImp_hRank___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_BinomialHeapImp_hRank___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l_BinomialHeapImp_isEmpty___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
}
obj* l_BinomialHeapImp_isEmpty(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeapImp_isEmpty___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_BinomialHeapImp_isEmpty___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_BinomialHeapImp_isEmpty___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_BinomialHeapImp_singleton___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set(x_4, 2, x_2);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* l_BinomialHeapImp_singleton(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeapImp_singleton___rarg), 1, 0);
return x_2;
}
}
obj* l_BinomialHeapImp_combine___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_2, 2);
lean::inc(x_9);
lean::inc(x_7);
lean::inc(x_4);
x_10 = lean::apply_2(x_1, x_4, x_7);
x_11 = lean::unbox(x_10);
lean::dec(x_10);
if (x_11 == 0)
{
uint8 x_12; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
x_12 = !lean::is_exclusive(x_2);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_13 = lean::cnstr_get(x_2, 2);
lean::dec(x_13);
x_14 = lean::cnstr_get(x_2, 1);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_2, 0);
lean::dec(x_15);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean_nat_add(x_8, x_16);
lean::dec(x_8);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_3);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_18);
x_22 = l_List_append___rarg(x_9, x_21);
lean::cnstr_set(x_2, 2, x_22);
lean::cnstr_set(x_2, 1, x_17);
return x_2;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_2);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean_nat_add(x_8, x_23);
lean::dec(x_8);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_3);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_25);
x_29 = l_List_append___rarg(x_9, x_28);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_7);
lean::cnstr_set(x_30, 1, x_24);
lean::cnstr_set(x_30, 2, x_29);
return x_30;
}
}
else
{
uint8 x_31; 
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_7);
x_31 = !lean::is_exclusive(x_3);
if (x_31 == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_32 = lean::cnstr_get(x_3, 2);
lean::dec(x_32);
x_33 = lean::cnstr_get(x_3, 1);
lean::dec(x_33);
x_34 = lean::cnstr_get(x_3, 0);
lean::dec(x_34);
x_35 = lean::mk_nat_obj(1u);
x_36 = lean_nat_add(x_5, x_35);
lean::dec(x_5);
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_2);
lean::cnstr_set(x_38, 1, x_37);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_37);
x_41 = l_List_append___rarg(x_6, x_40);
lean::cnstr_set(x_3, 2, x_41);
lean::cnstr_set(x_3, 1, x_36);
return x_3;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_3);
x_42 = lean::mk_nat_obj(1u);
x_43 = lean_nat_add(x_5, x_42);
lean::dec(x_5);
x_44 = lean::box(0);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_2);
lean::cnstr_set(x_45, 1, x_44);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_44);
x_48 = l_List_append___rarg(x_6, x_47);
x_49 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_49, 0, x_4);
lean::cnstr_set(x_49, 1, x_43);
lean::cnstr_set(x_49, 2, x_48);
return x_49;
}
}
}
}
obj* l_BinomialHeapImp_combine(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeapImp_combine___rarg), 3, 0);
return x_2;
}
}
obj* l_BinomialHeapImp_mergeNodes___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
return x_3;
}
else
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_3);
if (x_11 == 0)
{
obj* x_12; obj* x_13; uint8 x_14; 
x_12 = lean::cnstr_get(x_3, 1);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_3, 0);
lean::dec(x_13);
x_14 = lean_nat_dec_lt(x_9, x_8);
lean::dec(x_8);
lean::dec(x_9);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
lean::dec(x_2);
lean::inc(x_1);
x_15 = l_BinomialHeapImp_combine___rarg(x_1, x_4, x_6);
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
x_17 = l_BinomialHeapImp_hRank___rarg(x_5);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_19; uint8 x_20; 
x_19 = l_BinomialHeapImp_hRank___rarg(x_7);
x_20 = lean_nat_dec_eq(x_16, x_19);
lean::dec(x_19);
lean::dec(x_16);
if (x_20 == 0)
{
obj* x_21; 
x_21 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_5, x_7);
lean::cnstr_set(x_3, 1, x_21);
lean::cnstr_set(x_3, 0, x_15);
return x_3;
}
else
{
lean::cnstr_set(x_3, 1, x_5);
lean::cnstr_set(x_3, 0, x_15);
x_2 = x_3;
x_3 = x_7;
goto _start;
}
}
else
{
obj* x_23; uint8 x_24; 
x_23 = l_BinomialHeapImp_hRank___rarg(x_7);
x_24 = lean_nat_dec_eq(x_16, x_23);
lean::dec(x_23);
lean::dec(x_16);
if (x_24 == 0)
{
lean::cnstr_set(x_3, 0, x_15);
x_2 = x_5;
goto _start;
}
else
{
obj* x_26; 
x_26 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_5, x_7);
lean::cnstr_set(x_3, 1, x_26);
lean::cnstr_set(x_3, 0, x_15);
return x_3;
}
}
}
else
{
obj* x_27; 
lean::dec(x_5);
lean::dec(x_4);
x_27 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_7, x_2);
lean::cnstr_set(x_3, 1, x_27);
return x_3;
}
}
else
{
uint8 x_28; 
lean::dec(x_3);
x_28 = lean_nat_dec_lt(x_9, x_8);
lean::dec(x_8);
lean::dec(x_9);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
lean::dec(x_2);
lean::inc(x_1);
x_29 = l_BinomialHeapImp_combine___rarg(x_1, x_4, x_6);
x_30 = lean::cnstr_get(x_29, 1);
lean::inc(x_30);
x_31 = l_BinomialHeapImp_hRank___rarg(x_5);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean::dec(x_31);
if (x_32 == 0)
{
obj* x_33; uint8 x_34; 
x_33 = l_BinomialHeapImp_hRank___rarg(x_7);
x_34 = lean_nat_dec_eq(x_30, x_33);
lean::dec(x_33);
lean::dec(x_30);
if (x_34 == 0)
{
obj* x_35; obj* x_36; 
x_35 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_5, x_7);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_29);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_29);
lean::cnstr_set(x_37, 1, x_5);
x_2 = x_37;
x_3 = x_7;
goto _start;
}
}
else
{
obj* x_39; uint8 x_40; 
x_39 = l_BinomialHeapImp_hRank___rarg(x_7);
x_40 = lean_nat_dec_eq(x_30, x_39);
lean::dec(x_39);
lean::dec(x_30);
if (x_40 == 0)
{
obj* x_41; 
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_29);
lean::cnstr_set(x_41, 1, x_7);
x_2 = x_5;
x_3 = x_41;
goto _start;
}
else
{
obj* x_43; obj* x_44; 
x_43 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_5, x_7);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_29);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
obj* x_45; obj* x_46; 
lean::dec(x_5);
lean::dec(x_4);
x_45 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_7, x_2);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_6);
lean::cnstr_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
obj* x_47; uint8 x_48; 
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_2);
lean::inc(x_3);
x_47 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_5, x_3);
x_48 = !lean::is_exclusive(x_3);
if (x_48 == 0)
{
obj* x_49; obj* x_50; 
x_49 = lean::cnstr_get(x_3, 1);
lean::dec(x_49);
x_50 = lean::cnstr_get(x_3, 0);
lean::dec(x_50);
lean::cnstr_set(x_3, 1, x_47);
lean::cnstr_set(x_3, 0, x_4);
return x_3;
}
else
{
obj* x_51; 
lean::dec(x_3);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_4);
lean::cnstr_set(x_51, 1, x_47);
return x_51;
}
}
}
}
}
}
obj* l_BinomialHeapImp_mergeNodes___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeapImp_mergeNodes___main___rarg), 3, 0);
return x_2;
}
}
obj* l_BinomialHeapImp_mergeNodes___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_BinomialHeapImp_mergeNodes(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeapImp_mergeNodes___rarg), 3, 0);
return x_2;
}
}
obj* l_BinomialHeapImp_merge___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
return x_3;
}
else
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_4, x_6);
lean::cnstr_set(x_3, 0, x_7);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_9 = l_BinomialHeapImp_mergeNodes___main___rarg(x_1, x_4, x_8);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
}
}
}
obj* l_BinomialHeapImp_merge(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeapImp_merge___rarg), 3, 0);
return x_2;
}
}
obj* l_List_foldl___main___at_BinomialHeapImp_headOpt___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
else
{
obj* x_9; obj* x_10; uint8 x_11; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_11 = !lean::is_exclusive(x_2);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; uint8 x_15; 
x_12 = lean::cnstr_get(x_2, 0);
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
lean::dec(x_9);
lean::inc(x_1);
lean::inc(x_13);
lean::inc(x_12);
x_14 = lean::apply_2(x_1, x_12, x_13);
x_15 = lean::unbox(x_14);
lean::dec(x_14);
if (x_15 == 0)
{
lean::dec(x_12);
lean::cnstr_set(x_2, 0, x_13);
x_3 = x_10;
goto _start;
}
else
{
lean::dec(x_13);
x_3 = x_10;
goto _start;
}
}
else
{
obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
x_18 = lean::cnstr_get(x_2, 0);
lean::inc(x_18);
lean::dec(x_2);
x_19 = lean::cnstr_get(x_9, 0);
lean::inc(x_19);
lean::dec(x_9);
lean::inc(x_1);
lean::inc(x_19);
lean::inc(x_18);
x_20 = lean::apply_2(x_1, x_18, x_19);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_22; 
lean::dec(x_18);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
x_2 = x_22;
x_3 = x_10;
goto _start;
}
else
{
obj* x_24; 
lean::dec(x_19);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_18);
x_2 = x_24;
x_3 = x_10;
goto _start;
}
}
}
}
}
}
obj* l_List_foldl___main___at_BinomialHeapImp_headOpt___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_BinomialHeapImp_headOpt___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_BinomialHeapImp_headOpt___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = l_List_foldl___main___at_BinomialHeapImp_headOpt___spec__1___rarg(x_1, x_5, x_4);
return x_6;
}
}
}
obj* l_BinomialHeapImp_headOpt(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeapImp_headOpt___rarg), 2, 0);
return x_2;
}
}
obj* l_List_foldl___main___at_BinomialHeapImp_head___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
lean::inc(x_1);
lean::inc(x_6);
lean::inc(x_2);
x_7 = lean::apply_2(x_1, x_2, x_6);
x_8 = lean::unbox(x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_2);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
else
{
lean::dec(x_6);
x_3 = x_5;
goto _start;
}
}
}
}
obj* l_List_foldl___main___at_BinomialHeapImp_head___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_BinomialHeapImp_head___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_BinomialHeapImp_head___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
x_8 = l_List_foldl___main___at_BinomialHeapImp_head___spec__1___rarg(x_2, x_7, x_6);
return x_8;
}
}
}
}
obj* l_BinomialHeapImp_head(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeapImp_head___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_BinomialHeapImp_head___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_BinomialHeapImp_head___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_BinomialHeapImp_findMin___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
lean::dec(x_7);
lean::inc(x_1);
x_10 = lean::apply_2(x_1, x_8, x_9);
x_11 = lean::unbox(x_10);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
lean::dec(x_5);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean_nat_add(x_3, x_12);
lean::dec(x_3);
x_2 = x_6;
x_3 = x_13;
goto _start;
}
else
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_4);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_4, 1);
lean::dec(x_16);
x_17 = lean::cnstr_get(x_4, 0);
lean::dec(x_17);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean_nat_add(x_3, x_18);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set(x_4, 0, x_5);
x_2 = x_6;
x_3 = x_19;
goto _start;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_4);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean_nat_add(x_3, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_5);
lean::cnstr_set(x_23, 1, x_3);
x_2 = x_6;
x_3 = x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
obj* l_BinomialHeapImp_findMin___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeapImp_findMin___main___rarg), 4, 0);
return x_2;
}
}
obj* l_BinomialHeapImp_findMin___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_BinomialHeapImp_findMin___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_BinomialHeapImp_findMin(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeapImp_findMin___rarg), 4, 0);
return x_2;
}
}
obj* l_List_foldl___main___at_BinomialHeapImp_tail___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
lean::inc(x_1);
x_6 = l_BinomialHeapImp_merge___rarg(x_1, x_2, x_4);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
}
}
obj* l_List_foldl___main___at_BinomialHeapImp_tail___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_BinomialHeapImp_tail___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_List_foldl___main___at_BinomialHeapImp_tail___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
lean::inc(x_1);
x_6 = l_BinomialHeapImp_merge___rarg(x_1, x_2, x_4);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
}
}
obj* l_List_foldl___main___at_BinomialHeapImp_tail___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_BinomialHeapImp_tail___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_BinomialHeapImp_tail___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
lean::free_heap_obj(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; 
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; 
lean::free_heap_obj(x_2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_8 = lean::cnstr_get(x_7, 2);
lean::inc(x_8);
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
lean::dec(x_1);
x_9 = lean::box(0);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_12 = l_List_foldl___main___at_BinomialHeapImp_tail___spec__1___rarg(x_1, x_10, x_11);
return x_12;
}
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
x_14 = lean::mk_nat_obj(0u);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::mk_nat_obj(1u);
lean::inc(x_1);
x_17 = l_BinomialHeapImp_findMin___main___rarg(x_1, x_6, x_16, x_15);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_17, 1);
lean::inc(x_19);
lean::dec(x_17);
x_20 = l_List_eraseIdx___main___rarg(x_4, x_19);
lean::dec(x_19);
lean::cnstr_set(x_2, 0, x_20);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::dec(x_18);
x_22 = l_List_foldl___main___at_BinomialHeapImp_tail___spec__2___rarg(x_1, x_2, x_21);
return x_22;
}
}
}
else
{
obj* x_23; 
x_23 = lean::cnstr_get(x_2, 0);
lean::inc(x_23);
lean::dec(x_2);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; 
lean::dec(x_1);
x_24 = lean::box(0);
return x_24;
}
else
{
obj* x_25; 
x_25 = lean::cnstr_get(x_23, 1);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; 
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
lean::dec(x_23);
x_27 = lean::cnstr_get(x_26, 2);
lean::inc(x_27);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; 
lean::dec(x_1);
x_28 = lean::box(0);
return x_28;
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_27, 0);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
x_31 = l_List_foldl___main___at_BinomialHeapImp_tail___spec__1___rarg(x_1, x_29, x_30);
return x_31;
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_32 = lean::cnstr_get(x_23, 0);
lean::inc(x_32);
x_33 = lean::mk_nat_obj(0u);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::mk_nat_obj(1u);
lean::inc(x_1);
x_36 = l_BinomialHeapImp_findMin___main___rarg(x_1, x_25, x_35, x_34);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_36, 1);
lean::inc(x_38);
lean::dec(x_36);
x_39 = l_List_eraseIdx___main___rarg(x_23, x_38);
lean::dec(x_38);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
x_41 = lean::cnstr_get(x_37, 2);
lean::inc(x_41);
lean::dec(x_37);
x_42 = l_List_foldl___main___at_BinomialHeapImp_tail___spec__2___rarg(x_1, x_40, x_41);
return x_42;
}
}
}
}
}
}
obj* l_BinomialHeapImp_tail(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeapImp_tail___rarg), 2, 0);
return x_2;
}
}
obj* l_BinomialHeapImp_toList___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; 
lean::inc(x_2);
lean::inc(x_1);
x_4 = l_BinomialHeapImp_headOpt___rarg(x_1, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
lean::inc(x_1);
x_7 = l_BinomialHeapImp_tail___rarg(x_1, x_2);
x_8 = l_BinomialHeapImp_toList___main___rarg(x_1, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
}
obj* l_BinomialHeapImp_toList___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeapImp_toList___main___rarg), 2, 0);
return x_2;
}
}
obj* l_BinomialHeapImp_toList___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_BinomialHeapImp_toList___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_BinomialHeapImp_toList(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeapImp_toList___rarg), 2, 0);
return x_2;
}
}
obj* l_mkBinomialHeap(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_mkBinomialHeap___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_mkBinomialHeap(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_BinomialHeap_empty(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_BinomialHeap_empty___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_BinomialHeap_empty(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
uint8 l_BinomialHeap_isEmpty___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_BinomialHeapImp_isEmpty___rarg(x_1);
return x_2;
}
}
obj* l_BinomialHeap_isEmpty(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeap_isEmpty___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_BinomialHeap_isEmpty___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_BinomialHeap_isEmpty___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_BinomialHeap_isEmpty___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_BinomialHeap_isEmpty(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_BinomialHeap_singleton___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_BinomialHeapImp_singleton___rarg(x_1);
return x_2;
}
}
obj* l_BinomialHeap_singleton(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeap_singleton___rarg), 1, 0);
return x_3;
}
}
obj* l_BinomialHeap_singleton___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_BinomialHeap_singleton(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_BinomialHeap_merge___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_BinomialHeapImp_merge___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_BinomialHeap_merge(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeap_merge___rarg), 3, 0);
return x_2;
}
}
obj* l_BinomialHeap_head___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_BinomialHeapImp_head___rarg(x_2, x_1, x_3);
return x_4;
}
}
obj* l_BinomialHeap_head(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeap_head___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_BinomialHeap_head___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_BinomialHeap_head___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_BinomialHeap_headOpt___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_BinomialHeapImp_headOpt___rarg(x_1, x_2);
return x_3;
}
}
obj* l_BinomialHeap_headOpt(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeap_headOpt___rarg), 2, 0);
return x_2;
}
}
obj* l_BinomialHeap_tail___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_BinomialHeapImp_tail___rarg(x_1, x_2);
return x_3;
}
}
obj* l_BinomialHeap_tail(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeap_tail___rarg), 2, 0);
return x_2;
}
}
obj* l_BinomialHeap_insert___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_BinomialHeapImp_singleton___rarg(x_2);
x_5 = l_BinomialHeapImp_merge___rarg(x_1, x_4, x_3);
return x_5;
}
}
obj* l_BinomialHeap_insert(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeap_insert___rarg), 3, 0);
return x_2;
}
}
obj* l_BinomialHeap_toList___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_BinomialHeapImp_toList___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_BinomialHeap_toList(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_BinomialHeap_toList___rarg), 2, 0);
return x_2;
}
}
obj* initialize_init_data_list_default(obj*);
obj* initialize_init_coe(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_binomialheap_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_list_default(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_coe(w);
if (lean::io_result_is_error(w)) return w;
return w;
}
}

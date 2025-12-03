// Lean compiler output
// Module: Init.Data.Slice.List.Iterator
// Imports: public import Init.Data.Slice.List.Basic public import Init.Data.Iterators.Producers.List public import Init.Data.Iterators.Combinators.Take import all Init.Data.Range.Polymorphic.Basic public import Init.Data.Range.Polymorphic.Iterators public import Init.Data.Slice.Operations import Init.Omega
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
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ListSlice_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ListSlice_instToIterator(lean_object*);
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_instIteratorListIteratorOfPure___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ListSlice_instToIterator___lam__0(lean_object*);
static lean_object* l_instSliceSizeListSliceData___closed__0;
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg(lean_object*);
static lean_object* l_List_instAppendListSlice___lam__4___closed__0;
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__0___boxed(lean_object*);
static lean_object* l_List_instToStringListSlice___redArg___lam__2___closed__0;
lean_object* l_List_toSlice___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__1(lean_object*);
static lean_object* l_instSliceSizeListSliceData___closed__2;
static lean_object* l_instSliceSizeListSliceData___closed__4;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ListSlice_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__0(lean_object*, lean_object*);
static lean_object* l_List_ListSlice_repr___redArg___closed__2;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_ListSlice_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instReprListSlice(lean_object*, lean_object*);
static lean_object* l_instSliceSizeListSliceData___closed__7;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_instSliceSizeListSliceData___closed__3;
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__0(lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_List_ListSlice_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instSliceSizeListSliceData___closed__10;
static lean_object* l_instSliceSizeListSliceData___closed__8;
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instAppendListSlice(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instSliceSizeListSliceData___closed__9;
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instToStringListSlice(lean_object*, lean_object*);
static lean_object* l_instSliceSizeListSliceData___closed__5;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instSliceSizeListSliceData___closed__1;
lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_ListSlice_repr___redArg___closed__0;
lean_object* l_Std_Iterators_Take_instIterator___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_instSliceSizeListSliceData___closed__6;
lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_ListSlice_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l_ListSlice_instToIterator___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
lean_inc_ref(x_2);
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec_ref(x_2);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_17, x_18);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_ListSlice_instToIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ListSlice_instToIterator___lam__0), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_11; 
x_11 = lean_ctor_get(x_5, 1);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_5, 1, x_13);
lean_ctor_set(x_5, 0, x_15);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_6 = x_18;
goto block_10;
}
}
else
{
uint8_t x_19; 
lean_inc_ref(x_11);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec_ref(x_11);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_22, x_23);
lean_dec(x_22);
lean_ctor_set(x_5, 1, x_20);
lean_ctor_set(x_5, 0, x_24);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
lean_dec(x_5);
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
lean_dec_ref(x_11);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_26, x_27);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
x_6 = x_29;
goto block_10;
}
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_1);
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_Take_instIterator___lam__1), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_8, x_1, x_3, x_6, x_7, x_4);
return x_9;
}
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instSliceSizeListSliceData___closed__1;
x_2 = l_instSliceSizeListSliceData___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_instSliceSizeListSliceData___closed__5;
x_2 = l_instSliceSizeListSliceData___closed__4;
x_3 = l_instSliceSizeListSliceData___closed__3;
x_4 = l_instSliceSizeListSliceData___closed__2;
x_5 = l_instSliceSizeListSliceData___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instSliceSizeListSliceData___closed__6;
x_2 = l_instSliceSizeListSliceData___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instSliceSizeListSliceData___closed__2;
x_2 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorListIteratorOfPure___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instSliceSizeListSliceData___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_alloc_closure((void*)(l_instSliceSizeListSliceData___lam__0), 4, 0);
x_3 = lean_alloc_closure((void*)(l_instSliceSizeListSliceData___lam__1___boxed), 3, 0);
x_4 = l_instSliceSizeListSliceData___closed__9;
x_5 = l_instSliceSizeListSliceData___closed__10;
x_6 = lean_alloc_closure((void*)(l_instSliceSizeListSliceData___lam__2), 5, 4);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instForInListSliceOfMonad___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_2, x_4, x_6);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_17; 
x_17 = lean_ctor_get(x_7, 1);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_dec(x_20);
x_21 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_7, 1, x_19);
lean_ctor_set(x_7, 0, x_21);
x_10 = x_7;
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_10 = x_24;
goto block_16;
}
}
else
{
uint8_t x_25; 
lean_inc_ref(x_17);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec_ref(x_17);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_28, x_29);
lean_dec(x_28);
lean_ctor_set(x_7, 1, x_26);
lean_ctor_set(x_7, 0, x_30);
x_10 = x_7;
goto block_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_7, 0);
lean_inc(x_31);
lean_dec(x_7);
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec_ref(x_17);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_32, x_33);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
x_10 = x_35;
goto block_16;
}
}
block_16:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_13 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__2), 6, 3);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_2);
x_14 = lean_alloc_closure((void*)(l_Std_Iterators_Take_instIterator___lam__1), 3, 2);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_4);
x_15 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_14, x_1, x_5, x_10, x_8, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__0___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__1), 4, 0);
x_4 = l_instSliceSizeListSliceData___closed__9;
x_5 = l_instSliceSizeListSliceData___closed__10;
x_6 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__3), 9, 5);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
lean_closure_set(x_6, 4, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instForInListSliceOfMonad___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_List_instAppendListSlice___lam__4___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_45; 
x_45 = lean_ctor_get(x_7, 1);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_7);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
lean_dec(x_48);
x_49 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_7, 1, x_47);
lean_ctor_set(x_7, 0, x_49);
x_20 = x_7;
goto block_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_7, 0);
lean_inc(x_50);
lean_dec(x_7);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_20 = x_52;
goto block_44;
}
}
else
{
uint8_t x_53; 
lean_inc_ref(x_45);
x_53 = !lean_is_exclusive(x_7);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_45, 0);
lean_inc(x_56);
lean_dec_ref(x_45);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_56, x_57);
lean_dec(x_56);
lean_ctor_set(x_7, 1, x_54);
lean_ctor_set(x_7, 0, x_58);
x_20 = x_7;
goto block_44;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_7, 0);
lean_inc(x_59);
lean_dec(x_7);
x_60 = lean_ctor_get(x_45, 0);
lean_inc(x_60);
lean_dec_ref(x_45);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_60, x_61);
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
x_20 = x_63;
goto block_44;
}
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_11, x_1, x_2, x_3, x_13, x_12);
x_15 = lean_array_to_list(x_14);
x_16 = l_List_appendTR___redArg(x_9, x_15);
x_17 = l_List_lengthTR___redArg(x_16);
x_18 = l_List_toSlice___redArg(x_16, x_10, x_17);
lean_dec(x_17);
lean_dec(x_16);
return x_18;
}
block_44:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_3);
x_24 = lean_alloc_closure((void*)(l_Std_Iterators_Take_instIterator___lam__1), 3, 2);
lean_closure_set(x_24, 0, x_3);
lean_closure_set(x_24, 1, x_4);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_List_instAppendListSlice___lam__4___closed__0;
lean_inc_ref(x_3);
lean_inc_ref(x_24);
x_27 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_24, x_5, x_6, x_3, x_20, x_26);
x_28 = lean_array_to_list(x_27);
if (lean_obj_tag(x_23) == 0)
{
lean_ctor_set(x_8, 1, x_22);
lean_ctor_set(x_8, 0, x_25);
x_9 = x_28;
x_10 = x_25;
x_11 = x_24;
x_12 = x_26;
x_13 = x_8;
goto block_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec_ref(x_23);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_29, x_30);
lean_dec(x_29);
lean_ctor_set(x_8, 1, x_22);
lean_ctor_set(x_8, 0, x_31);
x_9 = x_28;
x_10 = x_25;
x_11 = x_24;
x_12 = x_26;
x_13 = x_8;
goto block_19;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
lean_inc_ref(x_3);
x_34 = lean_alloc_closure((void*)(l_Std_Iterators_Take_instIterator___lam__1), 3, 2);
lean_closure_set(x_34, 0, x_3);
lean_closure_set(x_34, 1, x_4);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_List_instAppendListSlice___lam__4___closed__0;
lean_inc_ref(x_3);
lean_inc_ref(x_34);
x_37 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_34, x_5, x_6, x_3, x_20, x_36);
x_38 = lean_array_to_list(x_37);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_32);
x_9 = x_38;
x_10 = x_35;
x_11 = x_34;
x_12 = x_36;
x_13 = x_39;
goto block_19;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec_ref(x_33);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_40, x_41);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_32);
x_9 = x_38;
x_10 = x_35;
x_11 = x_34;
x_12 = x_36;
x_13 = x_43;
goto block_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_instAppendListSlice___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_instAppendListSlice___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_alloc_closure((void*)(l_List_instAppendListSlice___lam__0___boxed), 2, 0);
x_3 = lean_alloc_closure((void*)(l_List_instAppendListSlice___lam__1___boxed), 1, 0);
x_4 = l_instSliceSizeListSliceData___closed__9;
x_5 = l_instSliceSizeListSliceData___closed__10;
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_6 = lean_alloc_closure((void*)(l_List_instAppendListSlice___lam__4), 8, 6);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
lean_closure_set(x_6, 4, x_2);
lean_closure_set(x_6, 5, x_3);
return x_6;
}
}
static lean_object* _init_l_List_ListSlice_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_instAppendListSlice___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_List_ListSlice_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_instAppendListSlice___lam__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_List_ListSlice_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instSliceSizeListSliceData___closed__10;
x_2 = l_instSliceSizeListSliceData___closed__9;
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_Take_instIterator___lam__1), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_List_ListSlice_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".toSlice 0 ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_List_ListSlice_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_ListSlice_repr___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_ListSlice_repr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_instSliceSizeListSliceData___closed__9;
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_7 = l_List_ListSlice_repr___redArg___closed__0;
x_8 = l_List_ListSlice_repr___redArg___closed__1;
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
x_9 = x_23;
goto block_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec_ref(x_5);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_24, x_25);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
x_9 = x_27;
goto block_21;
}
block_21:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = l_List_ListSlice_repr___redArg___closed__2;
x_11 = l_List_instAppendListSlice___lam__4___closed__0;
x_12 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_10, x_7, x_8, x_3, x_9, x_11);
x_13 = lean_array_to_list(x_12);
lean_inc(x_13);
x_14 = l_List_repr___redArg(x_1, x_13);
x_15 = l_List_ListSlice_repr___redArg___closed__4;
if (lean_is_scalar(x_6)) {
 x_16 = lean_alloc_ctor(5, 2, 0);
} else {
 x_16 = x_6;
 lean_ctor_set_tag(x_16, 5);
}
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_List_lengthTR___redArg(x_13);
lean_dec(x_13);
x_18 = l_Nat_reprFast(x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_List_ListSlice_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_ListSlice_repr___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_ListSlice_repr___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_instReprListSlice___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_instReprListSlice___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instReprListSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_instReprListSlice___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_List_instToStringListSlice___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_16; 
x_16 = lean_ctor_get(x_6, 1);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_dec(x_19);
x_20 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_6, 1, x_18);
lean_ctor_set(x_6, 0, x_20);
x_7 = x_6;
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_7 = x_23;
goto block_15;
}
}
else
{
uint8_t x_24; 
lean_inc_ref(x_16);
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec_ref(x_16);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_27, x_28);
lean_dec(x_27);
lean_ctor_set(x_6, 1, x_25);
lean_ctor_set(x_6, 0, x_29);
x_7 = x_6;
goto block_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_6, 0);
lean_inc(x_30);
lean_dec(x_6);
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
lean_dec_ref(x_16);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_31, x_32);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
x_7 = x_34;
goto block_15;
}
}
block_15:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc_ref(x_1);
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_Take_instIterator___lam__1), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_List_instAppendListSlice___lam__4___closed__0;
x_10 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_8, x_3, x_4, x_1, x_7, x_9);
x_11 = l_List_instToStringListSlice___redArg___lam__2___closed__0;
x_12 = lean_array_to_list(x_10);
x_13 = l_List_toString___redArg(x_5, x_12);
x_14 = lean_string_append(x_11, x_13);
lean_dec_ref(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_List_ListSlice_repr___redArg___closed__0;
x_3 = l_List_ListSlice_repr___redArg___closed__1;
x_4 = l_instSliceSizeListSliceData___closed__9;
x_5 = l_instSliceSizeListSliceData___closed__10;
x_6 = lean_alloc_closure((void*)(l_List_instToStringListSlice___redArg___lam__2), 6, 5);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
lean_closure_set(x_6, 4, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_instToStringListSlice___redArg(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_Slice_List_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Producers_List(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Operations(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_List_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Slice_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Producers_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instSliceSizeListSliceData___closed__0 = _init_l_instSliceSizeListSliceData___closed__0();
lean_mark_persistent(l_instSliceSizeListSliceData___closed__0);
l_instSliceSizeListSliceData___closed__1 = _init_l_instSliceSizeListSliceData___closed__1();
lean_mark_persistent(l_instSliceSizeListSliceData___closed__1);
l_instSliceSizeListSliceData___closed__2 = _init_l_instSliceSizeListSliceData___closed__2();
lean_mark_persistent(l_instSliceSizeListSliceData___closed__2);
l_instSliceSizeListSliceData___closed__3 = _init_l_instSliceSizeListSliceData___closed__3();
lean_mark_persistent(l_instSliceSizeListSliceData___closed__3);
l_instSliceSizeListSliceData___closed__4 = _init_l_instSliceSizeListSliceData___closed__4();
lean_mark_persistent(l_instSliceSizeListSliceData___closed__4);
l_instSliceSizeListSliceData___closed__5 = _init_l_instSliceSizeListSliceData___closed__5();
lean_mark_persistent(l_instSliceSizeListSliceData___closed__5);
l_instSliceSizeListSliceData___closed__6 = _init_l_instSliceSizeListSliceData___closed__6();
lean_mark_persistent(l_instSliceSizeListSliceData___closed__6);
l_instSliceSizeListSliceData___closed__7 = _init_l_instSliceSizeListSliceData___closed__7();
lean_mark_persistent(l_instSliceSizeListSliceData___closed__7);
l_instSliceSizeListSliceData___closed__8 = _init_l_instSliceSizeListSliceData___closed__8();
lean_mark_persistent(l_instSliceSizeListSliceData___closed__8);
l_instSliceSizeListSliceData___closed__9 = _init_l_instSliceSizeListSliceData___closed__9();
lean_mark_persistent(l_instSliceSizeListSliceData___closed__9);
l_instSliceSizeListSliceData___closed__10 = _init_l_instSliceSizeListSliceData___closed__10();
lean_mark_persistent(l_instSliceSizeListSliceData___closed__10);
l_List_instAppendListSlice___lam__4___closed__0 = _init_l_List_instAppendListSlice___lam__4___closed__0();
lean_mark_persistent(l_List_instAppendListSlice___lam__4___closed__0);
l_List_ListSlice_repr___redArg___closed__0 = _init_l_List_ListSlice_repr___redArg___closed__0();
lean_mark_persistent(l_List_ListSlice_repr___redArg___closed__0);
l_List_ListSlice_repr___redArg___closed__1 = _init_l_List_ListSlice_repr___redArg___closed__1();
lean_mark_persistent(l_List_ListSlice_repr___redArg___closed__1);
l_List_ListSlice_repr___redArg___closed__2 = _init_l_List_ListSlice_repr___redArg___closed__2();
lean_mark_persistent(l_List_ListSlice_repr___redArg___closed__2);
l_List_ListSlice_repr___redArg___closed__3 = _init_l_List_ListSlice_repr___redArg___closed__3();
lean_mark_persistent(l_List_ListSlice_repr___redArg___closed__3);
l_List_ListSlice_repr___redArg___closed__4 = _init_l_List_ListSlice_repr___redArg___closed__4();
lean_mark_persistent(l_List_ListSlice_repr___redArg___closed__4);
l_List_instToStringListSlice___redArg___lam__2___closed__0 = _init_l_List_instToStringListSlice___redArg___lam__2___closed__0();
lean_mark_persistent(l_List_instToStringListSlice___redArg___lam__2___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

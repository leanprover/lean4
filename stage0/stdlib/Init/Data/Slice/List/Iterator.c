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
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_instAppendListSlice___lam__2___closed__0;
LEAN_EXPORT lean_object* l_List_ListSlice_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__1(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ListSlice_instToIterator(lean_object*);
LEAN_EXPORT lean_object* l_ListSlice_instToIterator___lam__0(lean_object*);
static lean_object* l_instSliceSizeListSliceData___closed__0;
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toSlice___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ListSlice_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_instToStringListSlice___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l_List_instReprListSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instAppendListSlice(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_List_instAppendListSlice___closed__0;
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instToStringListSlice(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_ListSlice_instToIterator___closed__0;
static lean_object* l_instSliceSizeListSliceData___closed__1;
static lean_object* l_List_ListSlice_repr___redArg___closed__0;
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_instAppendListSlice___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
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
static lean_object* _init_l_ListSlice_instToIterator___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ListSlice_instToIterator___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ListSlice_instToIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ListSlice_instToIterator___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
if (lean_obj_tag(x_7) == 0)
{
lean_free_object(x_1);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_nat_sub(x_6, x_8);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_11);
x_12 = lean_nat_add(x_2, x_8);
x_13 = lean_apply_4(x_4, x_1, x_12, lean_box(0), lean_box(0));
return x_13;
}
}
else
{
lean_free_object(x_1);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_dec_eq(x_14, x_16);
if (x_17 == 0)
{
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_14);
lean_dec_ref(x_4);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = lean_nat_sub(x_14, x_16);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_nat_add(x_2, x_16);
x_22 = lean_apply_4(x_4, x_20, x_21, lean_box(0), lean_box(0));
return x_22;
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_inc(x_2);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instSliceSizeListSliceData___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
x_11 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_11);
x_3 = x_2;
goto block_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_3 = x_14;
goto block_6;
}
}
else
{
uint8_t x_15; 
lean_inc_ref(x_7);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec_ref(x_7);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_18, x_19);
lean_dec(x_18);
lean_ctor_set(x_2, 1, x_16);
lean_ctor_set(x_2, 0, x_20);
x_3 = x_2;
goto block_6;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec_ref(x_7);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_22, x_23);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_3 = x_25;
goto block_6;
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_WellFounded_opaqueFix_u2083___redArg(x_1, x_3, x_4, lean_box(0));
return x_5;
}
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instSliceSizeListSliceData___lam__0___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instSliceSizeListSliceData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instSliceSizeListSliceData___closed__0;
x_2 = lean_alloc_closure((void*)(l_instSliceSizeListSliceData___lam__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instSliceSizeListSliceData___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_apply_4(x_2, x_3, x_7, lean_box(0), lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_10, x_12);
if (x_13 == 0)
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_14; 
lean_free_object(x_5);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_2(x_1, lean_box(0), x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_nat_sub(x_10, x_12);
lean_dec(x_10);
lean_ctor_set(x_5, 1, x_16);
lean_ctor_set(x_5, 0, x_17);
x_18 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_8);
lean_closure_set(x_18, 2, x_5);
x_19 = lean_apply_2(x_2, x_15, x_6);
lean_inc(x_3);
x_20 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_19, x_4);
x_21 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_20, x_18);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_apply_2(x_1, lean_box(0), x_6);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_dec_eq(x_23, x_25);
if (x_26 == 0)
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_apply_2(x_1, lean_box(0), x_6);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec_ref(x_24);
x_30 = lean_nat_sub(x_23, x_25);
lean_dec(x_23);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(x_32, 0, x_1);
lean_closure_set(x_32, 1, x_8);
lean_closure_set(x_32, 2, x_31);
x_33 = lean_apply_2(x_2, x_28, x_6);
lean_inc(x_3);
x_34 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_33, x_4);
x_35 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_34, x_32);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_apply_2(x_1, lean_box(0), x_6);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_14; 
x_14 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_dec(x_17);
x_18 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_18);
x_6 = x_3;
goto block_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_6 = x_21;
goto block_13;
}
}
else
{
uint8_t x_22; 
lean_inc_ref(x_14);
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec_ref(x_14);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_25);
lean_ctor_set(x_3, 1, x_23);
lean_ctor_set(x_3, 0, x_27);
x_6 = x_3;
goto block_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
lean_dec_ref(x_14);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_29, x_30);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_6 = x_32;
goto block_13;
}
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__2), 8, 4);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_8);
lean_closure_set(x_11, 3, x_10);
x_12 = l_WellFounded_opaqueFix_u2083___redArg(x_11, x_6, x_4, lean_box(0));
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instForInListSliceOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instForInListSliceOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_free_object(x_1);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec_ref(x_6);
x_11 = lean_nat_sub(x_5, x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_11);
x_12 = lean_array_push(x_2, x_9);
x_13 = lean_apply_3(x_3, x_1, x_12, lean_box(0));
return x_13;
}
}
else
{
lean_free_object(x_1);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_2;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_dec_eq(x_14, x_16);
if (x_17 == 0)
{
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_14);
lean_dec_ref(x_3);
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec_ref(x_15);
x_20 = lean_nat_sub(x_14, x_16);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_array_push(x_2, x_18);
x_23 = lean_apply_3(x_3, x_21, x_22, lean_box(0));
return x_23;
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_3);
return x_2;
}
}
}
}
static lean_object* _init_l_List_instAppendListSlice___lam__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; lean_object* x_38; 
x_38 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_3);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
lean_dec(x_41);
x_42 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_3, 0, x_42);
x_15 = x_3;
goto block_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_15 = x_45;
goto block_37;
}
}
else
{
uint8_t x_46; 
lean_inc_ref(x_38);
x_46 = !lean_is_exclusive(x_3);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
lean_dec(x_48);
x_49 = lean_ctor_get(x_38, 0);
lean_inc(x_49);
lean_dec_ref(x_38);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_49, x_50);
lean_dec(x_49);
lean_ctor_set(x_3, 1, x_47);
lean_ctor_set(x_3, 0, x_51);
x_15 = x_3;
goto block_37;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_3, 0);
lean_inc(x_52);
lean_dec(x_3);
x_53 = lean_ctor_get(x_38, 0);
lean_inc(x_53);
lean_dec_ref(x_38);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_53, x_54);
lean_dec(x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
x_15 = x_56;
goto block_37;
}
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_1, x_8, x_5);
x_10 = lean_array_to_list(x_9);
x_11 = l_List_appendTR___redArg(x_6, x_10);
x_12 = l_List_lengthTR___redArg(x_11);
x_13 = l_List_toSlice___redArg(x_11, x_7, x_12);
lean_dec(x_12);
lean_dec(x_11);
return x_13;
}
block_37:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_List_instAppendListSlice___lam__2___closed__0;
x_21 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_2, x_15, x_20);
x_22 = lean_array_to_list(x_21);
if (lean_obj_tag(x_18) == 0)
{
lean_ctor_set(x_4, 1, x_17);
lean_ctor_set(x_4, 0, x_19);
x_5 = x_20;
x_6 = x_22;
x_7 = x_19;
x_8 = x_4;
goto block_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec_ref(x_18);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_23, x_24);
lean_dec(x_23);
lean_ctor_set(x_4, 1, x_17);
lean_ctor_set(x_4, 0, x_25);
x_5 = x_20;
x_6 = x_22;
x_7 = x_19;
x_8 = x_4;
goto block_14;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_List_instAppendListSlice___lam__2___closed__0;
x_30 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_2, x_15, x_29);
x_31 = lean_array_to_list(x_30);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_26);
x_5 = x_29;
x_6 = x_31;
x_7 = x_28;
x_8 = x_32;
goto block_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec_ref(x_27);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_33, x_34);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
x_5 = x_29;
x_6 = x_31;
x_7 = x_28;
x_8 = x_36;
goto block_14;
}
}
}
}
}
static lean_object* _init_l_List_instAppendListSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_instAppendListSlice___lam__0), 3, 0);
return x_1;
}
}
static lean_object* _init_l_List_instAppendListSlice___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_instAppendListSlice___closed__0;
x_2 = lean_alloc_closure((void*)(l_List_instAppendListSlice___lam__2), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_instAppendListSlice___closed__1;
return x_2;
}
}
static lean_object* _init_l_List_ListSlice_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".toSlice 0 ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_List_ListSlice_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_ListSlice_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_ListSlice_repr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_5 = x_2;
} else {
 lean_dec_ref(x_2);
 x_5 = lean_box(0);
}
x_6 = l_List_instAppendListSlice___closed__0;
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
x_7 = x_20;
goto block_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec_ref(x_4);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
x_7 = x_24;
goto block_18;
}
block_18:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = l_List_instAppendListSlice___lam__2___closed__0;
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_6, x_7, x_8);
x_10 = lean_array_to_list(x_9);
lean_inc(x_10);
x_11 = l_List_repr___redArg(x_1, x_10);
x_12 = l_List_ListSlice_repr___redArg___closed__1;
if (lean_is_scalar(x_5)) {
 x_13 = lean_alloc_ctor(5, 2, 0);
} else {
 x_13 = x_5;
 lean_ctor_set_tag(x_13, 5);
}
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_List_lengthTR___redArg(x_10);
lean_dec(x_10);
x_15 = l_Nat_reprFast(x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
return x_17;
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
x_3 = lean_alloc_closure((void*)(l_List_instReprListSlice___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_List_instToStringListSlice___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_dec(x_15);
x_16 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_3, 0, x_16);
x_4 = x_3;
goto block_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_4 = x_19;
goto block_11;
}
}
else
{
uint8_t x_20; 
lean_inc_ref(x_12);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec_ref(x_12);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_23, x_24);
lean_dec(x_23);
lean_ctor_set(x_3, 1, x_21);
lean_ctor_set(x_3, 0, x_25);
x_4 = x_3;
goto block_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
lean_dec_ref(x_12);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_27, x_28);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
x_4 = x_30;
goto block_11;
}
}
block_11:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_List_instAppendListSlice___lam__2___closed__0;
x_6 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_1, x_4, x_5);
x_7 = l_List_instToStringListSlice___redArg___lam__1___closed__0;
x_8 = lean_array_to_list(x_6);
x_9 = l_List_toString___redArg(x_2, x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec_ref(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_List_instAppendListSlice___closed__0;
x_3 = lean_alloc_closure((void*)(l_List_instToStringListSlice___redArg___lam__1), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
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
l_ListSlice_instToIterator___closed__0 = _init_l_ListSlice_instToIterator___closed__0();
lean_mark_persistent(l_ListSlice_instToIterator___closed__0);
l_instSliceSizeListSliceData___closed__0 = _init_l_instSliceSizeListSliceData___closed__0();
lean_mark_persistent(l_instSliceSizeListSliceData___closed__0);
l_instSliceSizeListSliceData___closed__1 = _init_l_instSliceSizeListSliceData___closed__1();
lean_mark_persistent(l_instSliceSizeListSliceData___closed__1);
l_List_instAppendListSlice___lam__2___closed__0 = _init_l_List_instAppendListSlice___lam__2___closed__0();
lean_mark_persistent(l_List_instAppendListSlice___lam__2___closed__0);
l_List_instAppendListSlice___closed__0 = _init_l_List_instAppendListSlice___closed__0();
lean_mark_persistent(l_List_instAppendListSlice___closed__0);
l_List_instAppendListSlice___closed__1 = _init_l_List_instAppendListSlice___closed__1();
lean_mark_persistent(l_List_instAppendListSlice___closed__1);
l_List_ListSlice_repr___redArg___closed__0 = _init_l_List_ListSlice_repr___redArg___closed__0();
lean_mark_persistent(l_List_ListSlice_repr___redArg___closed__0);
l_List_ListSlice_repr___redArg___closed__1 = _init_l_List_ListSlice_repr___redArg___closed__1();
lean_mark_persistent(l_List_ListSlice_repr___redArg___closed__1);
l_List_instToStringListSlice___redArg___lam__1___closed__0 = _init_l_List_instToStringListSlice___redArg___lam__1___closed__0();
lean_mark_persistent(l_List_instToStringListSlice___redArg___lam__1___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

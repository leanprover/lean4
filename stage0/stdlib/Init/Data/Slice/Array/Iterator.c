// Lean compiler output
// Module: Init.Data.Slice.Array.Iterator
// Imports: public import Init.Data.Slice.Array.Basic public import Init.Data.Slice.Operations import Init.Data.Iterators.Combinators.Attach public import Init.Data.Iterators.Combinators.ULift import all Init.Data.Range.Polymorphic.Basic public import Init.Data.Range.Polymorphic.Iterators public import Init.Data.Slice.Operations import Init.Omega import Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap
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
LEAN_EXPORT lean_object* l_Array_Subarray_repr(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldl___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_instCoeSubarrayArray___closed__0;
LEAN_EXPORT lean_object* l_Subarray_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_Subarray_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instToIterator___lam__0___boxed(lean_object*);
lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopOfFiniteId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_toArray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_instToIterator___closed__0;
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SubarrayIterator_step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instCoeSubarrayArray(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_copy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeSubarrayData___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_copy___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeSubarrayData___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg___lam__1(lean_object*, lean_object*);
static lean_object* l_Array_instAppendSubarray___closed__0;
LEAN_EXPORT lean_object* l_Array_ofSubarray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation(lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeSubarrayData(lean_object*);
LEAN_EXPORT lean_object* l_Array_instToStringSubarray(lean_object*, lean_object*);
lean_object* l_Array_Array_repr___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppendSubarray(lean_object*);
static lean_object* l_Array_instToStringSubarray___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_toArray_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_toArray___redArg___closed__0;
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad(lean_object*, lean_object*, lean_object*);
static lean_object* l_instSliceSizeSubarrayData___closed__0;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instToIterator(lean_object*);
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Array_Subarray_repr___redArg___closed__0;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_Subarray_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l_Subarray_instToIterator___lam__0(lean_object*);
static lean_object* l_Subarray_foldlM___redArg___closed__0;
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad___redArg(lean_object*);
static lean_object* l_instIteratorSubarrayIteratorId___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SubarrayIterator_step___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_SubarrayIterator_step___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_7 = lean_box(2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_4, x_8);
lean_inc_ref(x_3);
lean_ctor_set(x_1, 1, x_9);
x_10 = lean_array_fget(x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_16 = lean_box(2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_inc_ref(x_12);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_14);
x_20 = lean_array_fget(x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_SubarrayIterator_step(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_free_object(x_3);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_9 = lean_box(2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_inc_ref(x_5);
lean_ctor_set(x_3, 1, x_11);
x_12 = lean_array_fget(x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
x_18 = lean_box(2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_15, x_19);
lean_inc_ref(x_14);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_16);
x_22 = lean_array_fget(x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_7 = lean_box(2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_4, x_8);
lean_inc_ref(x_3);
lean_ctor_set(x_1, 1, x_9);
x_10 = lean_array_fget(x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_16 = lean_box(2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_inc_ref(x_12);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_14);
x_20 = lean_array_fget(x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_instIteratorSubarrayIteratorId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instIteratorSubarrayIteratorId___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instIteratorSubarrayIteratorId___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_apply_3(x_3, x_8, lean_box(0), x_4);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec_ref(x_6);
x_13 = lean_apply_4(x_2, x_12, x_4, lean_box(0), lean_box(0));
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_2(x_1, lean_box(0), x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 2);
x_13 = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_8);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_6);
lean_closure_set(x_13, 4, x_3);
x_14 = lean_nat_dec_lt(x_11, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_15 = lean_box(2);
x_16 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_13, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_11, x_17);
lean_inc_ref(x_10);
lean_ctor_set(x_5, 1, x_18);
x_19 = lean_array_fget(x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_13, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
x_24 = lean_ctor_get(x_5, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_25 = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_8);
lean_closure_set(x_25, 2, x_2);
lean_closure_set(x_25, 3, x_6);
lean_closure_set(x_25, 4, x_3);
x_26 = lean_nat_dec_lt(x_23, x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
x_27 = lean_box(2);
x_28 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_25, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_23, x_29);
lean_inc_ref(x_22);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_24);
x_32 = lean_array_fget(x_22, x_23);
lean_dec(x_23);
lean_dec_ref(x_22);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_25, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2), 8, 4);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_2);
x_12 = l_WellFounded_opaqueFix_u2083___redArg(x_11, x_5, x_6, lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Subarray_instToIterator___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Subarray_instToIterator___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Subarray_instToIterator___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Subarray_instToIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Subarray_instToIterator___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeSubarrayData___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_sub(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeSubarrayData___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instSliceSizeSubarrayData___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_instSliceSizeSubarrayData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instSliceSizeSubarrayData___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeSubarrayData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instSliceSizeSubarrayData___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Subarray_instToIterator___closed__0;
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopOfFiniteId___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instForInSubarrayOfMonad___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
x_14 = lean_ctor_get(x_7, 2);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_free_object(x_7);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_16 = lean_apply_2(x_1, lean_box(0), x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec_ref(x_2);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_13, x_18);
lean_inc_ref(x_12);
lean_ctor_set(x_7, 1, x_19);
x_20 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__2), 4, 3);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_10);
lean_closure_set(x_20, 2, x_7);
x_21 = lean_array_fget(x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
x_22 = lean_apply_2(x_3, x_8, x_21);
x_23 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_4, x_22);
lean_inc(x_5);
x_24 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_23, x_6);
x_25 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_24, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
x_28 = lean_ctor_get(x_7, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_30 = lean_apply_2(x_1, lean_box(0), x_8);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
lean_dec_ref(x_2);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_27, x_32);
lean_inc_ref(x_26);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_28);
x_35 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__2), 4, 3);
lean_closure_set(x_35, 0, x_1);
lean_closure_set(x_35, 1, x_10);
lean_closure_set(x_35, 2, x_34);
x_36 = lean_array_fget(x_26, x_27);
lean_dec(x_27);
lean_dec_ref(x_26);
x_37 = lean_apply_2(x_3, x_8, x_36);
x_38 = lean_apply_4(x_31, lean_box(0), lean_box(0), x_4, x_37);
lean_inc(x_5);
x_39 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_38, x_6);
x_40 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_39, x_35);
return x_40;
}
}
}
}
static lean_object* _init_l_Subarray_foldlM___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = l_Subarray_foldlM___redArg___closed__0;
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__3), 10, 6);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_9);
lean_closure_set(x_11, 4, x_6);
lean_closure_set(x_11, 5, x_10);
x_12 = l_WellFounded_opaqueFix_u2083___redArg(x_11, x_4, x_3, lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec_ref(x_4);
x_10 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = l_Subarray_foldlM___redArg___closed__0;
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__3), 10, 6);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_10);
lean_closure_set(x_14, 2, x_5);
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_9);
lean_closure_set(x_14, 5, x_13);
x_15 = l_WellFounded_opaqueFix_u2083___redArg(x_14, x_7, x_6, lean_box(0));
return x_15;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldl___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_8, x_11);
lean_inc_ref(x_7);
lean_ctor_set(x_2, 1, x_12);
x_13 = lean_array_fget(x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
x_14 = lean_apply_2(x_1, x_3, x_13);
x_15 = lean_apply_4(x_5, x_2, x_14, lean_box(0), lean_box(0));
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_17, x_20);
lean_inc_ref(x_16);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_18);
x_23 = lean_array_fget(x_16, x_17);
lean_dec(x_17);
lean_dec_ref(x_16);
x_24 = lean_apply_2(x_1, x_3, x_23);
x_25 = lean_apply_4(x_5, x_22, x_24, lean_box(0), lean_box(0));
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_foldl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Subarray_foldl___redArg___lam__0), 5, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_WellFounded_opaqueFix_u2083___redArg(x_4, x_3, x_2, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Subarray_foldl___redArg___lam__0), 5, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = l_WellFounded_opaqueFix_u2083___redArg(x_6, x_5, x_4, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 2);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
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
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_11, x_15);
lean_inc_ref(x_10);
lean_ctor_set(x_5, 1, x_16);
x_17 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__2), 4, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_8);
lean_closure_set(x_17, 2, x_5);
x_18 = lean_array_fget(x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
x_19 = lean_apply_2(x_2, x_18, x_6);
lean_inc(x_3);
x_20 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_19, x_4);
x_21 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_20, x_17);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
x_24 = lean_ctor_get(x_5, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_apply_2(x_1, lean_box(0), x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_23, x_27);
lean_inc_ref(x_22);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_24);
x_30 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__2), 4, 3);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_8);
lean_closure_set(x_30, 2, x_29);
x_31 = lean_array_fget(x_22, x_23);
lean_dec(x_23);
lean_dec_ref(x_22);
x_32 = lean_apply_2(x_2, x_31, x_6);
lean_inc(x_3);
x_33 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_32, x_4);
x_34 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_33, x_30);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__2), 8, 4);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_6);
lean_closure_set(x_9, 3, x_8);
x_10 = l_WellFounded_opaqueFix_u2083___redArg(x_9, x_2, x_3, lean_box(0));
return x_10;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec_ref(x_4);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_Subarray_forIn___redArg___lam__2), 8, 4);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_9);
lean_closure_set(x_12, 3, x_11);
x_13 = l_WellFounded_opaqueFix_u2083___redArg(x_12, x_5, x_6, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_toArray_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_free_object(x_1);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_5, x_8);
lean_inc_ref(x_4);
lean_ctor_set(x_1, 1, x_9);
x_10 = lean_array_fget(x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
x_11 = lean_array_push(x_2, x_10);
x_2 = x_11;
goto _start;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_14, x_17);
lean_inc_ref(x_13);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_15);
x_20 = lean_array_fget(x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
x_21 = lean_array_push(x_2, x_20);
x_1 = x_19;
x_2 = x_21;
goto _start;
}
}
}
}
static lean_object* _init_l_Subarray_toArray___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_toArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Subarray_toArray___redArg___closed__0;
x_3 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_toArray_spec__0___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_toArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Subarray_toArray___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_toArray_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_toArray_spec__0___redArg(x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_instCoeSubarrayArray___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Subarray_toArray), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_instCoeSubarrayArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instCoeSubarrayArray___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_copy___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Subarray_toArray___redArg___closed__0;
x_3 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_toArray_spec__0___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_copy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Subarray_copy___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_ofSubarray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Subarray_toArray___redArg___closed__0;
x_3 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_toArray_spec__0___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_ofSubarray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_ofSubarray___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Subarray_toArray___redArg(x_1);
x_4 = l_Subarray_toArray___redArg(x_2);
x_5 = l_Array_append___redArg(x_3, x_4);
lean_dec_ref(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_5);
x_8 = l_Array_toSubarray___redArg(x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Array_instAppendSubarray___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_instAppendSubarray___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_instAppendSubarray___closed__0;
return x_2;
}
}
static lean_object* _init_l_Array_Subarray_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".toSubarray", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Array_Subarray_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Subarray_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_Subarray_repr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Subarray_toArray___redArg(x_2);
x_4 = l_Array_Array_repr___redArg(x_1, x_3);
x_5 = l_Array_Subarray_repr___redArg___closed__1;
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_Subarray_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_Subarray_repr___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_Subarray_repr___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_instReprSubarray___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_instReprSubarray___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_instReprSubarray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_instReprSubarray___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_instToStringSubarray___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Subarray_toArray___redArg(x_2);
x_4 = l_Array_instToStringSubarray___redArg___lam__0___closed__0;
x_5 = lean_array_to_list(x_3);
x_6 = l_List_toString___redArg(x_1, x_5);
x_7 = lean_string_append(x_4, x_6);
lean_dec_ref(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_instToStringSubarray___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_instToStringSubarray___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_Slice_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Operations(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_ULift(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Operations(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_Array_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Slice_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_ULift(builtin);
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
res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instIteratorSubarrayIteratorId___closed__0 = _init_l_instIteratorSubarrayIteratorId___closed__0();
lean_mark_persistent(l_instIteratorSubarrayIteratorId___closed__0);
l_Subarray_instToIterator___closed__0 = _init_l_Subarray_instToIterator___closed__0();
lean_mark_persistent(l_Subarray_instToIterator___closed__0);
l_instSliceSizeSubarrayData___closed__0 = _init_l_instSliceSizeSubarrayData___closed__0();
lean_mark_persistent(l_instSliceSizeSubarrayData___closed__0);
l_Subarray_foldlM___redArg___closed__0 = _init_l_Subarray_foldlM___redArg___closed__0();
lean_mark_persistent(l_Subarray_foldlM___redArg___closed__0);
l_Subarray_toArray___redArg___closed__0 = _init_l_Subarray_toArray___redArg___closed__0();
lean_mark_persistent(l_Subarray_toArray___redArg___closed__0);
l_instCoeSubarrayArray___closed__0 = _init_l_instCoeSubarrayArray___closed__0();
lean_mark_persistent(l_instCoeSubarrayArray___closed__0);
l_Array_instAppendSubarray___closed__0 = _init_l_Array_instAppendSubarray___closed__0();
lean_mark_persistent(l_Array_instAppendSubarray___closed__0);
l_Array_Subarray_repr___redArg___closed__0 = _init_l_Array_Subarray_repr___redArg___closed__0();
lean_mark_persistent(l_Array_Subarray_repr___redArg___closed__0);
l_Array_Subarray_repr___redArg___closed__1 = _init_l_Array_Subarray_repr___redArg___closed__1();
lean_mark_persistent(l_Array_Subarray_repr___redArg___closed__1);
l_Array_instToStringSubarray___redArg___lam__0___closed__0 = _init_l_Array_instToStringSubarray___redArg___lam__0___closed__0();
lean_mark_persistent(l_Array_instToStringSubarray___redArg___lam__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

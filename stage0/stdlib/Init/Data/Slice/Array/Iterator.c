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
LEAN_EXPORT lean_object* l_Subarray_foldlM___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_Subarray_repr(lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_foldl___closed__10;
LEAN_EXPORT lean_object* l_instIteratorLoopPartialSubarrayIteratorIdOfMonad___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instCoeSubarray(lean_object*);
static lean_object* l_Subarray_forIn___closed__0;
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMappedPartial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldlM___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_Subarray_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instToIterator___lam__0___boxed(lean_object*);
lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopOfFiniteId___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_foldl___closed__5;
LEAN_EXPORT lean_object* l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_SubarrayIterator_step(lean_object*, lean_object*, lean_object*);
static lean_object* l_instForInSubarrayOfMonad___redArg___closed__0;
LEAN_EXPORT lean_object* l_instIteratorCollectSubarrayIteratorIdOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeSubarrayData___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Array_ofSubarray_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeSubarrayData___lam__0(lean_object*);
static lean_object* l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___lam__0___closed__0;
static lean_object* l_Subarray_foldl___closed__8;
LEAN_EXPORT lean_object* l_instIteratorLoopPartialSubarrayIteratorIdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Subarray_foldl___closed__1;
LEAN_EXPORT lean_object* l_Array_ofSubarray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation(lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeSubarrayData(lean_object*);
LEAN_EXPORT lean_object* l_Array_instToStringSubarray(lean_object*, lean_object*);
lean_object* l_Array_Array_repr___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Subarray_foldl___closed__9;
LEAN_EXPORT lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppendSubarray(lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldlM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_foldl___closed__6;
LEAN_EXPORT lean_object* l_Subarray_toArray___redArg(lean_object*);
static lean_object* l_Array_Subarray_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_Subarray_repr___redArg___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Subarray_foldl___closed__7;
static lean_object* l_Subarray_foldl___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_instToIterator(lean_object*);
LEAN_EXPORT lean_object* l_instIteratorCollectPartialSubarrayIteratorIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Array_ofSubarray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Array_instCoeSubarray___closed__0;
LEAN_EXPORT lean_object* l_instIteratorLoopPartialSubarrayIteratorIdOfMonad(lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_foldl___closed__3;
LEAN_EXPORT lean_object* l_Subarray_foldlM___lam__1(lean_object*);
static lean_object* l_Subarray_foldl___closed__4;
static lean_object* l_Array_Subarray_repr___redArg___closed__0;
LEAN_EXPORT lean_object* l_Subarray_foldlM___lam__1___boxed(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_instToStringSubarray___redArg___lam__2___closed__0;
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forIn___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_foldl___closed__0;
static lean_object* l_Array_Subarray_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l_Subarray_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg(lean_object*);
lean_object* l_Std_Iterators_IterM_DefaultConsumers_forInPartial___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray(lean_object*, lean_object*);
lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0;
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorCollectPartialSubarrayIteratorIdOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SubarrayIterator_step___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_instIteratorSubarrayIteratorId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instIteratorSubarrayIteratorId___lam__0), 1, 0);
return x_2;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
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
static lean_object* _init_l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instIteratorSubarrayIteratorId___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___lam__0___closed__0;
x_9 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_1, x_4, x_6, x_2, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0;
x_3 = lean_alloc_closure((void*)(l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___lam__0), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorCollectSubarrayIteratorIdOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instIteratorCollectPartialSubarrayIteratorIdOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0;
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_IterM_DefaultConsumers_toArrayMappedPartial), 10, 6);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, lean_box(0));
lean_closure_set(x_3, 3, lean_box(0));
lean_closure_set(x_3, 4, x_1);
lean_closure_set(x_3, 5, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorCollectPartialSubarrayIteratorIdOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instIteratorCollectPartialSubarrayIteratorIdOfMonad___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_1, x_2, x_3, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0;
x_3 = lean_alloc_closure((void*)(l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0), 9, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopSubarrayIteratorIdOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopPartialSubarrayIteratorIdOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Iterators_IterM_DefaultConsumers_forInPartial___redArg(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopPartialSubarrayIteratorIdOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0;
x_3 = lean_alloc_closure((void*)(l_instIteratorLoopPartialSubarrayIteratorIdOfMonad___redArg___lam__0), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopPartialSubarrayIteratorIdOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instIteratorLoopPartialSubarrayIteratorIdOfMonad___redArg(x_3);
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
LEAN_EXPORT lean_object* l_Subarray_instToIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Subarray_instToIterator___lam__0___boxed), 1, 0);
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
LEAN_EXPORT lean_object* l_instSliceSizeSubarrayData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSliceSizeSubarrayData___lam__0___boxed), 1, 0);
return x_2;
}
}
static lean_object* _init_l_instForInSubarrayOfMonad___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Subarray_instToIterator___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instForInSubarrayOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_instForInSubarrayOfMonad___redArg___closed__0;
lean_inc_ref(x_1);
x_3 = l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg(x_1);
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
LEAN_EXPORT lean_object* l_Subarray_foldlM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM___lam__1(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_2(x_2, x_7, x_5);
lean_inc(x_8);
x_10 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_3, x_9);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Subarray_foldlM___lam__1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_alloc_closure((void*)(l_Subarray_foldlM___lam__0), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Subarray_foldlM___lam__1___boxed), 1, 0);
x_12 = lean_alloc_closure((void*)(l_Subarray_foldlM___lam__2), 1, 0);
lean_inc_ref(x_9);
x_13 = lean_alloc_closure((void*)(l_Subarray_foldlM___lam__3), 7, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_11);
x_14 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0;
x_15 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_14, x_4, x_10, x_7, x_6, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_alloc_closure((void*)(l_Subarray_foldlM___lam__0), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Subarray_foldlM___lam__1___boxed), 1, 0);
x_9 = lean_alloc_closure((void*)(l_Subarray_foldlM___lam__2), 1, 0);
lean_inc_ref(x_6);
x_10 = lean_alloc_closure((void*)(l_Subarray_foldlM___lam__3), 7, 4);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_8);
x_11 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0;
x_12 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_11, x_1, x_7, x_4, x_3, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldl___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_2(x_1, x_4, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
static lean_object* _init_l_Subarray_foldl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Subarray_foldlM___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Subarray_foldl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Subarray_foldl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Subarray_foldl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Subarray_foldl___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Subarray_foldl___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Subarray_foldl___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Subarray_foldl___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Subarray_foldl___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_foldl___closed__2;
x_2 = l_Subarray_foldl___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Subarray_foldl___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Subarray_foldl___closed__6;
x_2 = l_Subarray_foldl___closed__5;
x_3 = l_Subarray_foldl___closed__4;
x_4 = l_Subarray_foldl___closed__3;
x_5 = l_Subarray_foldl___closed__8;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Subarray_foldl___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_foldl___closed__7;
x_2 = l_Subarray_foldl___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Subarray_foldl___closed__0;
x_7 = lean_alloc_closure((void*)(l_Subarray_foldl___lam__1), 4, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = l_Subarray_foldl___closed__10;
x_9 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0;
x_10 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_9, x_8, x_6, x_5, x_4, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Subarray_foldl___closed__0;
x_5 = lean_alloc_closure((void*)(l_Subarray_foldl___lam__1), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Subarray_foldl___closed__10;
x_7 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0;
x_8 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_7, x_6, x_4, x_3, x_2, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Subarray_forIn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Subarray_foldlM___lam__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_8, 0);
x_10 = l_Subarray_foldl___closed__0;
x_11 = l_Subarray_forIn___closed__0;
lean_inc_ref(x_9);
x_12 = lean_alloc_closure((void*)(l_Subarray_forIn___lam__2), 6, 3);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_11);
x_13 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0;
x_14 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_13, x_4, x_10, x_5, x_6, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = l_Subarray_foldl___closed__0;
x_8 = l_Subarray_forIn___closed__0;
lean_inc_ref(x_6);
x_9 = lean_alloc_closure((void*)(l_Subarray_forIn___lam__2), 6, 3);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_8);
x_10 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0;
x_11 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_10, x_1, x_7, x_2, x_3, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Array_ofSubarray_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Array_ofSubarray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___lam__0___closed__0;
x_3 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Array_ofSubarray_spec__0___redArg(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Array_ofSubarray_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___00Array_ofSubarray_spec__0___redArg(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_instCoeSubarray___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_ofSubarray), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_instCoeSubarray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_instCoeSubarray___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___lam__0___closed__0;
lean_inc_ref(x_3);
x_11 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_8, x_1, x_2, x_3, x_6, x_10);
x_12 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_8, x_4, x_5, x_3, x_7, x_10);
x_13 = l_Array_append___redArg(x_11, x_12);
lean_dec_ref(x_12);
x_14 = lean_array_get_size(x_13);
x_15 = l_Array_toSubarray___redArg(x_13, x_9, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_instAppendSubarray___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_instAppendSubarray___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Array_instAppendSubarray___lam__0___boxed), 2, 0);
x_3 = lean_alloc_closure((void*)(l_Array_instAppendSubarray___lam__1___boxed), 1, 0);
x_4 = l_Subarray_foldl___closed__10;
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_5 = lean_alloc_closure((void*)(l_Array_instAppendSubarray___lam__4), 7, 5);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
lean_closure_set(x_5, 3, x_2);
lean_closure_set(x_5, 4, x_3);
return x_5;
}
}
static lean_object* _init_l_Array_Subarray_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_instAppendSubarray___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Array_Subarray_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_instAppendSubarray___lam__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_Subarray_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".toSubarray", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Array_Subarray_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Subarray_repr___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_Subarray_repr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Array_Subarray_repr___redArg___closed__0;
x_4 = l_Array_Subarray_repr___redArg___closed__1;
x_5 = l_Subarray_foldl___closed__10;
x_6 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0;
x_7 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___lam__0___closed__0;
x_8 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_6, x_3, x_4, x_5, x_2, x_7);
x_9 = l_Array_Array_repr___redArg(x_1, x_8);
x_10 = l_Array_Subarray_repr___redArg___closed__3;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
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
x_3 = l_Array_instReprSubarray___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_Array_instToStringSubarray___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0;
x_7 = l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___lam__0___closed__0;
x_8 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_6, x_1, x_2, x_3, x_5, x_7);
x_9 = l_Array_instToStringSubarray___redArg___lam__2___closed__0;
x_10 = lean_array_to_list(x_8);
x_11 = l_List_toString___redArg(x_4, x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec_ref(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Array_Subarray_repr___redArg___closed__0;
x_3 = l_Array_Subarray_repr___redArg___closed__1;
x_4 = l_Subarray_foldl___closed__10;
x_5 = lean_alloc_closure((void*)(l_Array_instToStringSubarray___redArg___lam__2), 5, 4);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
lean_closure_set(x_5, 3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_instToStringSubarray___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_toArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_ofSubarray___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_toArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_ofSubarray___redArg(x_1);
return x_2;
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
l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0 = _init_l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0();
lean_mark_persistent(l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___closed__0);
l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___lam__0___closed__0 = _init_l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___lam__0___closed__0();
lean_mark_persistent(l_instIteratorCollectSubarrayIteratorIdOfMonad___redArg___lam__0___closed__0);
l_instForInSubarrayOfMonad___redArg___closed__0 = _init_l_instForInSubarrayOfMonad___redArg___closed__0();
lean_mark_persistent(l_instForInSubarrayOfMonad___redArg___closed__0);
l_Subarray_foldl___closed__0 = _init_l_Subarray_foldl___closed__0();
lean_mark_persistent(l_Subarray_foldl___closed__0);
l_Subarray_foldl___closed__1 = _init_l_Subarray_foldl___closed__1();
lean_mark_persistent(l_Subarray_foldl___closed__1);
l_Subarray_foldl___closed__2 = _init_l_Subarray_foldl___closed__2();
lean_mark_persistent(l_Subarray_foldl___closed__2);
l_Subarray_foldl___closed__3 = _init_l_Subarray_foldl___closed__3();
lean_mark_persistent(l_Subarray_foldl___closed__3);
l_Subarray_foldl___closed__4 = _init_l_Subarray_foldl___closed__4();
lean_mark_persistent(l_Subarray_foldl___closed__4);
l_Subarray_foldl___closed__5 = _init_l_Subarray_foldl___closed__5();
lean_mark_persistent(l_Subarray_foldl___closed__5);
l_Subarray_foldl___closed__6 = _init_l_Subarray_foldl___closed__6();
lean_mark_persistent(l_Subarray_foldl___closed__6);
l_Subarray_foldl___closed__7 = _init_l_Subarray_foldl___closed__7();
lean_mark_persistent(l_Subarray_foldl___closed__7);
l_Subarray_foldl___closed__8 = _init_l_Subarray_foldl___closed__8();
lean_mark_persistent(l_Subarray_foldl___closed__8);
l_Subarray_foldl___closed__9 = _init_l_Subarray_foldl___closed__9();
lean_mark_persistent(l_Subarray_foldl___closed__9);
l_Subarray_foldl___closed__10 = _init_l_Subarray_foldl___closed__10();
lean_mark_persistent(l_Subarray_foldl___closed__10);
l_Subarray_forIn___closed__0 = _init_l_Subarray_forIn___closed__0();
lean_mark_persistent(l_Subarray_forIn___closed__0);
l_Array_instCoeSubarray___closed__0 = _init_l_Array_instCoeSubarray___closed__0();
lean_mark_persistent(l_Array_instCoeSubarray___closed__0);
l_Array_Subarray_repr___redArg___closed__0 = _init_l_Array_Subarray_repr___redArg___closed__0();
lean_mark_persistent(l_Array_Subarray_repr___redArg___closed__0);
l_Array_Subarray_repr___redArg___closed__1 = _init_l_Array_Subarray_repr___redArg___closed__1();
lean_mark_persistent(l_Array_Subarray_repr___redArg___closed__1);
l_Array_Subarray_repr___redArg___closed__2 = _init_l_Array_Subarray_repr___redArg___closed__2();
lean_mark_persistent(l_Array_Subarray_repr___redArg___closed__2);
l_Array_Subarray_repr___redArg___closed__3 = _init_l_Array_Subarray_repr___redArg___closed__3();
lean_mark_persistent(l_Array_Subarray_repr___redArg___closed__3);
l_Array_instToStringSubarray___redArg___lam__2___closed__0 = _init_l_Array_instToStringSubarray___redArg___lam__2___closed__0();
lean_mark_persistent(l_Array_instToStringSubarray___redArg___lam__2___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

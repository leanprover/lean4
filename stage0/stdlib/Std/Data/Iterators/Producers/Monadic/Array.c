// Lean compiler output
// Module: Std.Data.Iterators.Producers.Monadic.Array
// Imports: Init.Data.Nat.Lemmas Init.RCases Init.Data.Iterators.Consumers Init.Data.Iterators.Internal.Termination
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
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorLoopPartialArrayIteratorOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorSizePartialArrayIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorLoopArrayIteratorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMappedPartial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorCollectPartialArrayIteratorOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorCollectArrayIteratorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_IterM_DefaultConsumers_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorCollectArrayIteratorOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorCollectPartialArrayIteratorOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_ArrayIterator_finitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorLoopArrayIteratorOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorLoopPartialArrayIteratorOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterFromIdxM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorArrayIteratorOfPure(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_IterM_DefaultConsumers_sizePartial___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorLoopPartialArrayIteratorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_ArrayIterator_finitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorLoopArrayIteratorOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Iterators_instIteratorCollectArrayIteratorOfMonad___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Array_iterFromIdxM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorSizeArrayIterator___redArg(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorCollectArrayIteratorOfMonad___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterM___redArg(lean_object*);
lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorSizeArrayIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterFromIdxM___redArg(lean_object*, lean_object*);
lean_object* l_Std_Iterators_IterM_DefaultConsumers_forInPartial___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorSizePartialArrayIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_iterFromIdxM___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_iterFromIdxM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_iterFromIdxM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterFromIdxM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_iterM___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_iterM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_iterM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterM(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_free_object(x_2);
lean_dec(x_5);
lean_dec_ref(x_4);
x_8 = lean_box(2);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_inc_ref(x_4);
lean_ctor_set(x_2, 1, x_11);
x_12 = lean_array_fget(x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_apply_2(x_1, lean_box(0), x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_lt(x_16, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec_ref(x_15);
x_19 = lean_box(2);
x_20 = lean_apply_2(x_1, lean_box(0), x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_16, x_21);
lean_inc_ref(x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_fget(x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_apply_2(x_1, lean_box(0), x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorArrayIteratorOfPure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_ArrayIterator_finitenessRelation(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_ArrayIterator_finitenessRelation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_ArrayIterator_finitenessRelation(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Iterators_instIteratorCollectArrayIteratorOfMonad___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorCollectArrayIteratorOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_Iterators_instIteratorCollectArrayIteratorOfMonad___redArg___lam__0___closed__0;
x_9 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_1, x_4, x_6, x_2, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorCollectArrayIteratorOfMonad___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorCollectArrayIteratorOfMonad___redArg___lam__0), 7, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorCollectArrayIteratorOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorCollectArrayIteratorOfMonad___redArg___lam__0), 7, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorCollectPartialArrayIteratorOfMonad___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Std_Iterators_IterM_DefaultConsumers_toArrayMappedPartial), 10, 6);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, lean_box(0));
lean_closure_set(x_6, 3, lean_box(0));
lean_closure_set(x_6, 4, x_2);
lean_closure_set(x_6, 5, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorCollectPartialArrayIteratorOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_closure((void*)(l_Std_Iterators_IterM_DefaultConsumers_toArrayMappedPartial), 10, 6);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, lean_box(0));
lean_closure_set(x_9, 3, lean_box(0));
lean_closure_set(x_9, 4, x_5);
lean_closure_set(x_9, 5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorLoopArrayIteratorOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_1, x_2, x_3, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorLoopArrayIteratorOfMonad___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorLoopArrayIteratorOfMonad___redArg___lam__0), 9, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorLoopArrayIteratorOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorLoopArrayIteratorOfMonad___redArg___lam__0), 9, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorLoopPartialArrayIteratorOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Iterators_IterM_DefaultConsumers_forInPartial___redArg(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorLoopPartialArrayIteratorOfMonad___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorLoopPartialArrayIteratorOfMonad___redArg___lam__0), 7, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorLoopPartialArrayIteratorOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorLoopPartialArrayIteratorOfMonad___redArg___lam__0), 7, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorSizeArrayIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
lean_inc_ref(x_1);
lean_inc_ref(x_4);
x_5 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorLoopArrayIteratorOfMonad___redArg___lam__0), 9, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Iterators_IterM_DefaultConsumers_size___boxed), 8, 7);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_1);
lean_closure_set(x_6, 3, lean_box(0));
lean_closure_set(x_6, 4, x_4);
lean_closure_set(x_6, 5, x_5);
lean_closure_set(x_6, 6, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorSizeArrayIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_6, 0, x_5);
lean_inc_ref(x_3);
lean_inc_ref(x_6);
x_7 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorLoopArrayIteratorOfMonad___redArg___lam__0), 9, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_IterM_DefaultConsumers_size___boxed), 8, 7);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, x_6);
lean_closure_set(x_8, 5, x_7);
lean_closure_set(x_8, 6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorSizePartialArrayIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
lean_inc_ref(x_1);
lean_inc_ref(x_4);
x_5 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorLoopPartialArrayIteratorOfMonad___redArg___lam__0), 7, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Iterators_IterM_DefaultConsumers_sizePartial___boxed), 7, 6);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_1);
lean_closure_set(x_6, 3, lean_box(0));
lean_closure_set(x_6, 4, x_4);
lean_closure_set(x_6, 5, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_instIteratorSizePartialArrayIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorArrayIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_6, 0, x_5);
lean_inc_ref(x_3);
lean_inc_ref(x_6);
x_7 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorLoopPartialArrayIteratorOfMonad___redArg___lam__0), 7, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_alloc_closure((void*)(l_Std_Iterators_IterM_DefaultConsumers_sizePartial___boxed), 7, 6);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, x_6);
lean_closure_set(x_8, 5, x_7);
return x_8;
}
}
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_RCases(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Consumers(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Internal_Termination(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Producers_Monadic_Array(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Internal_Termination(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Iterators_instIteratorCollectArrayIteratorOfMonad___redArg___lam__0___closed__0 = _init_l_Std_Iterators_instIteratorCollectArrayIteratorOfMonad___redArg___lam__0___closed__0();
lean_mark_persistent(l_Std_Iterators_instIteratorCollectArrayIteratorOfMonad___redArg___lam__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

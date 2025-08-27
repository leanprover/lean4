// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Iterators
// Imports: Init.Data.Range.Polymorphic.RangeIterator Init.Data.Range.Polymorphic.Basic Init.Data.Iterators.Combinators.Attach
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
LEAN_EXPORT lean_object* l_Std_PRange_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_toList(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_toList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_toList___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_Internal_iter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_Internal_iter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_size___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instIteratorSizeRangeIteratorIdOfRangeSize___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instIteratorSizeRangeIteratorIdOfRangeSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_toList___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_toList___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_size(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_Internal_iter(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instIteratorSizeRangeIteratorIdOfRangeSize(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_toList___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instIteratorSizeRangeIteratorIdOfRangeSize___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_Internal_iter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_Internal_iter(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_apply_1(x_5, x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_apply_1(x_5, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_Internal_iter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox(x_2);
x_9 = l_Std_PRange_Internal_iter(x_7, x_8, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_toList___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_toList___redArg___lam__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_toList___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_alloc_closure((void*)(l_Std_PRange_toList___redArg___lam__0___boxed), 2, 0);
x_7 = lean_alloc_closure((void*)(l_Std_PRange_toList___redArg___lam__1___boxed), 1, 0);
x_8 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_2, 0, x_8);
x_9 = lean_apply_5(x_3, lean_box(0), x_6, lean_box(0), x_7, x_2);
x_10 = lean_array_to_list(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_alloc_closure((void*)(l_Std_PRange_toList___redArg___lam__0___boxed), 2, 0);
x_14 = lean_alloc_closure((void*)(l_Std_PRange_toList___redArg___lam__1___boxed), 1, 0);
x_15 = lean_apply_1(x_1, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
x_17 = lean_apply_5(x_3, lean_box(0), x_13, lean_box(0), x_14, x_16);
x_18 = lean_array_to_list(x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_toList(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_alloc_closure((void*)(l_Std_PRange_toList___redArg___lam__0___boxed), 2, 0);
x_14 = lean_alloc_closure((void*)(l_Std_PRange_toList___redArg___lam__1___boxed), 1, 0);
x_15 = lean_apply_1(x_5, x_12);
lean_ctor_set(x_7, 0, x_15);
x_16 = lean_apply_5(x_10, lean_box(0), x_13, lean_box(0), x_14, x_7);
x_17 = lean_array_to_list(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_closure((void*)(l_Std_PRange_toList___redArg___lam__0___boxed), 2, 0);
x_21 = lean_alloc_closure((void*)(l_Std_PRange_toList___redArg___lam__1___boxed), 1, 0);
x_22 = lean_apply_1(x_5, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
x_24 = lean_apply_5(x_10, lean_box(0), x_20, lean_box(0), x_21, x_23);
x_25 = lean_array_to_list(x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_toList___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PRange_toList___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_toList___redArg___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_PRange_toList___redArg___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_toList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox(x_2);
x_13 = l_Std_PRange_toList(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instIteratorSizeRangeIteratorIdOfRangeSize___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_apply_2(x_1, x_5, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instIteratorSizeRangeIteratorIdOfRangeSize___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PRange_instIteratorSizeRangeIteratorIdOfRangeSize___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instIteratorSizeRangeIteratorIdOfRangeSize(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PRange_instIteratorSizeRangeIteratorIdOfRangeSize___redArg(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instIteratorSizeRangeIteratorIdOfRangeSize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Std_PRange_instIteratorSizeRangeIteratorIdOfRangeSize(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_size___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_2, 0, x_6);
x_7 = lean_apply_1(x_3, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_apply_1(x_1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_apply_1(x_3, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_size(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_apply_1(x_5, x_10);
lean_ctor_set(x_7, 0, x_11);
x_12 = lean_apply_1(x_8, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_apply_1(x_5, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_apply_1(x_8, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox(x_2);
x_11 = l_Std_PRange_size(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_3(x_2, x_4, lean_box(0), x_7);
x_10 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec_ref(x_7);
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_apply_1(x_1, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_inc(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_16 = lean_apply_2(x_14, lean_box(0), x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc_ref(x_2);
lean_inc(x_17);
lean_inc(x_12);
x_18 = lean_apply_2(x_2, x_12, x_17);
x_19 = lean_unbox(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_inc(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_20 = lean_apply_2(x_14, lean_box(0), x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_13);
x_21 = lean_alloc_closure((void*)(l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg___lam__1), 7, 3);
lean_closure_set(x_21, 0, x_13);
lean_closure_set(x_21, 1, x_9);
lean_closure_set(x_21, 2, x_3);
x_22 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___redArg(x_4, x_2, x_6, x_12, x_8, x_21, x_17);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg___lam__0___boxed), 1, 0);
x_5 = lean_alloc_closure((void*)(l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg___lam__2), 9, 4);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
lean_closure_set(x_5, 3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg(x_5, x_6, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_1);
x_15 = lean_unbox(x_2);
x_16 = l_Std_PRange_instForIn_x27MkInferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLowerBoundOfLawfulUpwardEnumerableUpperBoundOfMonadOfFiniteRangeIteratorId(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_7);
return x_16;
}
}
lean_object* initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Combinators_Attach(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_Attach(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

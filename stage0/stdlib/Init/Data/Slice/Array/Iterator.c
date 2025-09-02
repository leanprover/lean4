// Lean compiler output
// Module: Init.Data.Slice.Array.Iterator
// Imports: Init.Core Init.Data.Slice.Array.Basic Init.Data.Iterators.Combinators.Attach Init.Data.Iterators.Combinators.FilterMap Init.Data.Iterators.Combinators.ULift Init.Data.Iterators.Consumers.Collect Init.Data.Iterators.Consumers.Loop Init.Data.Range.Polymorphic.Basic Init.Data.Range.Polymorphic.Basic Init.Data.Range.Polymorphic.Nat Init.Data.Range.Polymorphic.Iterators Init.Data.Slice.Operations Init.Omega
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
static lean_object* l_instIteratorCollectStateSubarrayId___redArg___closed__1;
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_Subarray_repr(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_instIteratorStateSubarrayId___redArg___closed__6;
LEAN_EXPORT lean_object* l_Array_instCoeSubarray(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_toArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopPartialStateSubarrayIdOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Std_Iterators_Map_instIteratorLoopPartial___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instIteratorStateSubarrayId___redArg___closed__2;
LEAN_EXPORT lean_object* l_Subarray_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_instToStringSubarray___redArg___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Array_Subarray_repr___redArg(lean_object*, lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instForInSubarray___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldl___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInSubarray___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__4___boxed(lean_object*, lean_object*);
static lean_object* l_instIteratorStateSubarrayId___redArg___closed__10;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___Array_ofSubarray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Std_Iterators_Map_instIteratorCollect___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorStateSubarrayId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInSubarray___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instIteratorStateSubarrayId___redArg___closed__11;
LEAN_EXPORT lean_object* l_Subarray_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInSubarray___lam__3(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_instIteratorSizePartialMap___redArg(lean_object*, lean_object*);
lean_object* l_Std_Iterators_instIteratorMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___Array_ofSubarray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___Array_ofSubarray_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_Types_ULiftIterator_instIteratorSizePartial___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_toArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg___lam__2(lean_object*);
static lean_object* l_instIteratorStateSubarrayId___redArg___closed__4;
LEAN_EXPORT lean_object* l_Subarray_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInSubarray___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorStateSubarrayId___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_Iterators_Map_instIteratorCollectPartial___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instIteratorSizeStateSubarrayId___closed__1;
LEAN_EXPORT lean_object* l_instIteratorStateSubarrayId___redArg(lean_object*);
lean_object* l_Std_Iterators_instIteratorSizeMap___redArg(lean_object*, lean_object*);
lean_object* l_Std_Iterators_Types_Attach_instIterator___redArg(lean_object*, lean_object*);
static lean_object* l_Array_ofSubarray___redArg___closed__0;
static lean_object* l_instIteratorStateSubarrayId___redArg___closed__12;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInSubarray(lean_object*, lean_object*);
static lean_object* l_instIteratorCollectStateSubarrayId___redArg___closed__0;
LEAN_EXPORT lean_object* l_instIteratorSizePartialStateSubarrayId___boxed(lean_object*, lean_object*);
static lean_object* l_instIteratorStateSubarrayId___redArg___closed__13;
LEAN_EXPORT lean_object* l_Array_ofSubarray(lean_object*, lean_object*);
static lean_object* l_instIteratorStateSubarrayId___redArg___closed__9;
LEAN_EXPORT lean_object* l_Array_instToStringSubarray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopPartialStateSubarrayIdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_Array_repr___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppendSubarray(lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorStateSubarrayId___redArg___lam__2(lean_object*, lean_object*);
static lean_object* l_instIteratorLoopStateSubarrayIdOfMonad___redArg___closed__0;
static lean_object* l_instIteratorSizePartialStateSubarrayId___closed__0;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorSizeStateSubarrayId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorSizeStateSubarrayId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_toArray___redArg(lean_object*);
static lean_object* l_instIteratorStateSubarrayId___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__4(lean_object*, lean_object*);
extern lean_object* l_Std_PRange_instUpwardEnumerableNat;
LEAN_EXPORT lean_object* l_instIteratorStateSubarrayId___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_instIteratorStateSubarrayId___redArg___closed__7;
static lean_object* l_instIteratorSizePartialStateSubarrayId___closed__1;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorCollectStateSubarrayId(lean_object*, lean_object*);
lean_object* l_Std_Iterators_Types_ULiftIterator_instIteratorCollect___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorStateSubarrayId___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___Array_ofSubarray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_instCoeSubarray___closed__0;
LEAN_EXPORT lean_object* l_instIteratorSizePartialStateSubarrayId(lean_object*, lean_object*);
static lean_object* l_instIteratorStateSubarrayId___redArg___closed__3;
LEAN_EXPORT lean_object* l_instIteratorLoopStateSubarrayIdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInSubarray___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_Subarray_repr___redArg___closed__0;
static lean_object* l_instIteratorStateSubarrayId___redArg___closed__1;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_foldlM___redArg___closed__1;
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopStateSubarrayIdOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg(lean_object*);
static lean_object* l_instIteratorStateSubarrayId___redArg___closed__8;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofSubarray___redArg___boxed(lean_object*);
static lean_object* l_instIteratorCollectPartialStateSubarrayId___redArg___closed__0;
lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofSubarray___boxed(lean_object*, lean_object*);
static lean_object* l_Array_Subarray_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInSubarray___lam__1(lean_object*, lean_object*);
static lean_object* l_instIteratorStateSubarrayId___redArg___closed__5;
static lean_object* l_Subarray_foldlM___redArg___closed__0;
LEAN_EXPORT lean_object* l_instIteratorCollectPartialStateSubarrayId___redArg(lean_object*);
lean_object* l_Std_Iterators_Types_ULiftIterator_instIteratorSize___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_PRange_instIteratorRangeIteratorIdOfUpwardEnumerableOfSupportsUpperBound___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId___redArg(lean_object*);
lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_Iterators_Map_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_Types_ULiftIterator_instIteratorCollectPartial___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_instIteratorSizeStateSubarrayId___closed__0;
LEAN_EXPORT lean_object* l_instIteratorCollectPartialStateSubarrayId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorCollectStateSubarrayId___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instToIteratorSubarrayId___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToIteratorSubarrayId___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instToIteratorSubarrayId(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorStateSubarrayId___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instIteratorStateSubarrayId___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_fget_borrowed(x_3, x_2);
lean_inc(x_4);
return x_4;
}
}
static lean_object* _init_l_instIteratorStateSubarrayId___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateSubarrayId___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateSubarrayId___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateSubarrayId___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateSubarrayId___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateSubarrayId___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateSubarrayId___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateSubarrayId___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instIteratorStateSubarrayId___redArg___closed__1;
x_2 = l_instIteratorStateSubarrayId___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_instIteratorStateSubarrayId___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_instIteratorStateSubarrayId___redArg___closed__5;
x_2 = l_instIteratorStateSubarrayId___redArg___closed__4;
x_3 = l_instIteratorStateSubarrayId___redArg___closed__3;
x_4 = l_instIteratorStateSubarrayId___redArg___closed__2;
x_5 = l_instIteratorStateSubarrayId___redArg___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_instIteratorStateSubarrayId___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instIteratorStateSubarrayId___redArg___closed__6;
x_2 = l_instIteratorStateSubarrayId___redArg___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_instIteratorStateSubarrayId___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateSubarrayId___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instIteratorStateSubarrayId___redArg___closed__10;
x_2 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_instIteratorStateSubarrayId___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PRange_instUpwardEnumerableNat;
x_2 = l_instIteratorStateSubarrayId___redArg___closed__11;
x_3 = lean_alloc_closure((void*)(l_Std_PRange_instIteratorRangeIteratorIdOfUpwardEnumerableOfSupportsUpperBound___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_instIteratorStateSubarrayId___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instIteratorStateSubarrayId___redArg___closed__12;
x_2 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_3 = l_Std_Iterators_Types_Attach_instIterator___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorStateSubarrayId___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_instIteratorStateSubarrayId___redArg___lam__0___boxed), 2, 0);
x_3 = lean_alloc_closure((void*)(l_instIteratorStateSubarrayId___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_5 = l_instIteratorStateSubarrayId___redArg___closed__13;
lean_inc_ref(x_2);
x_6 = l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(x_2, x_5, x_4);
x_7 = l_Std_Iterators_instIteratorMap___redArg(x_4, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instIteratorStateSubarrayId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorStateSubarrayId___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorStateSubarrayId___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorStateSubarrayId___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorStateSubarrayId___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorStateSubarrayId___redArg___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_instIteratorCollectStateSubarrayId___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instIteratorStateSubarrayId___redArg___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorCollectStateSubarrayId___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_instIteratorStateSubarrayId___redArg___closed__13;
x_2 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_3 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_4 = l_Std_Iterators_Types_ULiftIterator_instIteratorCollect___redArg(x_3, x_2, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instIteratorCollectStateSubarrayId___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_3 = lean_alloc_closure((void*)(l_instIteratorStateSubarrayId___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_5 = l_instIteratorCollectStateSubarrayId___redArg___closed__1;
x_6 = l_Std_Iterators_Map_instIteratorCollect___redArg(x_4, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instIteratorCollectStateSubarrayId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorCollectStateSubarrayId___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_instIteratorCollectPartialStateSubarrayId___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_instIteratorStateSubarrayId___redArg___closed__13;
x_2 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_3 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_4 = l_Std_Iterators_Types_ULiftIterator_instIteratorCollectPartial___redArg(x_3, x_2, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instIteratorCollectPartialStateSubarrayId___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_3 = lean_alloc_closure((void*)(l_instIteratorStateSubarrayId___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_5 = l_instIteratorCollectPartialStateSubarrayId___redArg___closed__0;
x_6 = l_Std_Iterators_Map_instIteratorCollectPartial___redArg(x_4, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instIteratorCollectPartialStateSubarrayId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorCollectPartialStateSubarrayId___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_instIteratorLoopStateSubarrayIdOfMonad___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_2 = l_instIteratorStateSubarrayId___redArg___closed__13;
x_3 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_4 = l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopStateSubarrayIdOfMonad___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_4 = lean_alloc_closure((void*)(l_instIteratorStateSubarrayId___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_6 = l_instIteratorLoopStateSubarrayIdOfMonad___redArg___closed__0;
x_7 = l_Std_Iterators_Map_instIteratorLoop___redArg(x_5, x_2, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopStateSubarrayIdOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instIteratorLoopStateSubarrayIdOfMonad___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopPartialStateSubarrayIdOfMonad___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_4 = lean_alloc_closure((void*)(l_instIteratorStateSubarrayId___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_6 = l_instIteratorLoopStateSubarrayIdOfMonad___redArg___closed__0;
x_7 = l_Std_Iterators_Map_instIteratorLoopPartial___redArg(x_5, x_2, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopPartialStateSubarrayIdOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instIteratorLoopPartialStateSubarrayIdOfMonad___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_instIteratorSizeStateSubarrayId___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_instIteratorStateSubarrayId___redArg___closed__13;
x_2 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_3 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_4 = l_Std_Iterators_Types_ULiftIterator_instIteratorSize___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_instIteratorSizeStateSubarrayId___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instIteratorSizeStateSubarrayId___closed__0;
x_2 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_3 = l_Std_Iterators_instIteratorSizeMap___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorSizeStateSubarrayId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorSizeStateSubarrayId___closed__1;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorSizeStateSubarrayId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorSizeStateSubarrayId(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_instIteratorSizePartialStateSubarrayId___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_instIteratorStateSubarrayId___redArg___closed__13;
x_2 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_3 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_4 = l_Std_Iterators_Types_ULiftIterator_instIteratorSizePartial___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_instIteratorSizePartialStateSubarrayId___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instIteratorSizePartialStateSubarrayId___closed__0;
x_2 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_3 = l_Std_Iterators_instIteratorSizePartialMap___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorSizePartialStateSubarrayId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorSizePartialStateSubarrayId___closed__1;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorSizePartialStateSubarrayId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorSizePartialStateSubarrayId(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instForInSubarray___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instForInSubarray___lam__3(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instForInSubarray___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_fget_borrowed(x_1, x_2);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instForInSubarray___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_instForInSubarray___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
lean_dec_ref(x_7);
x_13 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_alloc_closure((void*)(l_instForInSubarray___lam__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_10);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
x_19 = l_instIteratorStateSubarrayId___redArg___closed__13;
x_20 = l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(x_1, x_19, x_13);
x_21 = l_Std_Iterators_instIteratorMap___redArg(x_13, x_20, x_2, x_16);
lean_inc_ref(x_15);
x_22 = lean_alloc_closure((void*)(l_instForInSubarray___lam__2), 6, 3);
lean_closure_set(x_22, 0, x_15);
lean_closure_set(x_22, 1, x_9);
lean_closure_set(x_22, 2, x_3);
x_23 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_21, x_6, x_4, x_18, x_8, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_instForInSubarray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_instForInSubarray___lam__0), 4, 0);
x_4 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_5 = lean_alloc_closure((void*)(l_instForInSubarray___lam__3___boxed), 1, 0);
x_6 = lean_alloc_closure((void*)(l_instForInSubarray___lam__4), 9, 4);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_5);
lean_closure_set(x_6, 3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instForInSubarray___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instForInSubarray___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instForInSubarray___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instForInSubarray___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
static lean_object* _init_l_Subarray_foldlM___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instForInSubarray___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Subarray_foldlM___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instForInSubarray___lam__3___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_ctor_get(x_5, 0);
x_10 = l_Subarray_foldlM___redArg___closed__0;
x_11 = l_Subarray_foldlM___redArg___closed__1;
x_12 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__2), 1, 0);
x_13 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_14 = lean_alloc_closure((void*)(l_instForInSubarray___lam__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_6);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
lean_inc_ref(x_9);
x_17 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__4), 7, 4);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_12);
lean_closure_set(x_17, 3, x_11);
x_18 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_19 = l_instIteratorLoopStateSubarrayIdOfMonad___redArg___closed__0;
x_20 = l_Std_Iterators_instIteratorMap___redArg(x_18, x_19, x_13, x_14);
x_21 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_20, x_1, x_10, x_16, x_3, x_17);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldlM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_ctor_get(x_8, 0);
x_13 = l_Subarray_foldlM___redArg___closed__0;
x_14 = l_Subarray_foldlM___redArg___closed__1;
x_15 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__2), 1, 0);
x_16 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_17 = lean_alloc_closure((void*)(l_instForInSubarray___lam__1___boxed), 2, 1);
lean_closure_set(x_17, 0, x_9);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
lean_inc_ref(x_12);
x_20 = lean_alloc_closure((void*)(l_Subarray_foldlM___redArg___lam__4), 7, 4);
lean_closure_set(x_20, 0, x_12);
lean_closure_set(x_20, 1, x_5);
lean_closure_set(x_20, 2, x_15);
lean_closure_set(x_20, 3, x_14);
x_21 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_22 = l_instIteratorLoopStateSubarrayIdOfMonad___redArg___closed__0;
x_23 = l_Std_Iterators_instIteratorMap___redArg(x_21, x_22, x_16, x_17);
x_24 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_23, x_4, x_13, x_19, x_6, x_20);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldl___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_2(x_1, x_4, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = l_Subarray_foldlM___redArg___closed__0;
x_9 = lean_alloc_closure((void*)(l_Subarray_foldl___redArg___lam__1), 4, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_11 = lean_alloc_closure((void*)(l_instForInSubarray___lam__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_5);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = l_instIteratorLoopStateSubarrayIdOfMonad___redArg___closed__0;
x_15 = l_Std_Iterators_instIteratorMap___redArg(x_4, x_14, x_10, x_11);
x_16 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_15, x_4, x_8, x_13, x_2, x_9);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Subarray_foldl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = l_Subarray_foldlM___redArg___closed__0;
x_11 = lean_alloc_closure((void*)(l_Subarray_foldl___redArg___lam__1), 4, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_13 = lean_alloc_closure((void*)(l_instForInSubarray___lam__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_7);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = l_instIteratorLoopStateSubarrayIdOfMonad___redArg___closed__0;
x_17 = l_Std_Iterators_instIteratorMap___redArg(x_6, x_16, x_12, x_13);
x_18 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_17, x_6, x_10, x_15, x_4, x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_alloc_closure((void*)(l_instForInSubarray___lam__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_5);
x_12 = l_Subarray_foldlM___redArg___closed__1;
x_13 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_14 = l_Subarray_foldlM___redArg___closed__0;
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
x_17 = l_instIteratorLoopStateSubarrayIdOfMonad___redArg___closed__0;
x_18 = l_Std_Iterators_instIteratorMap___redArg(x_8, x_17, x_13, x_11);
lean_inc_ref(x_10);
x_19 = lean_alloc_closure((void*)(l_instForInSubarray___lam__2), 6, 3);
lean_closure_set(x_19, 0, x_10);
lean_closure_set(x_19, 1, x_4);
lean_closure_set(x_19, 2, x_12);
x_20 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_18, x_1, x_14, x_16, x_3, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Subarray_forIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
lean_dec_ref(x_5);
x_11 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_alloc_closure((void*)(l_instForInSubarray___lam__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_8);
x_15 = l_Subarray_foldlM___redArg___closed__1;
x_16 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_17 = l_Subarray_foldlM___redArg___closed__0;
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_10);
x_20 = l_instIteratorLoopStateSubarrayIdOfMonad___redArg___closed__0;
x_21 = l_Std_Iterators_instIteratorMap___redArg(x_11, x_20, x_16, x_14);
lean_inc_ref(x_13);
x_22 = lean_alloc_closure((void*)(l_instForInSubarray___lam__2), 6, 3);
lean_closure_set(x_22, 0, x_13);
lean_closure_set(x_22, 1, x_7);
lean_closure_set(x_22, 2, x_15);
x_23 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___redArg(x_21, x_4, x_17, x_19, x_6, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___Array_ofSubarray_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = l_instIteratorStateSubarrayId___redArg___closed__10;
x_11 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_10);
lean_inc(x_9);
lean_inc(x_6);
x_12 = lean_apply_2(x_11, x_6, x_9);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_free_object(x_4);
lean_dec(x_9);
lean_free_object(x_2);
lean_dec(x_6);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_9, x_15);
lean_ctor_set(x_4, 0, x_16);
x_17 = lean_array_fget_borrowed(x_14, x_9);
lean_dec(x_9);
lean_inc(x_17);
x_18 = lean_array_push(x_3, x_17);
x_3 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
lean_dec(x_4);
x_21 = l_instIteratorStateSubarrayId___redArg___closed__10;
x_22 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_21);
lean_inc(x_20);
lean_inc(x_6);
x_23 = lean_apply_2(x_22, x_6, x_20);
x_24 = lean_unbox(x_23);
if (x_24 == 0)
{
lean_dec(x_20);
lean_free_object(x_2);
lean_dec(x_6);
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_20, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_2, 0, x_28);
x_29 = lean_array_fget_borrowed(x_25, x_20);
lean_dec(x_20);
lean_inc(x_29);
x_30 = lean_array_push(x_3, x_29);
x_3 = x_30;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
lean_dec(x_2);
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_34 = x_4;
} else {
 lean_dec_ref(x_4);
 x_34 = lean_box(0);
}
x_35 = l_instIteratorStateSubarrayId___redArg___closed__10;
x_36 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_35);
lean_inc(x_33);
lean_inc(x_32);
x_37 = lean_apply_2(x_36, x_32, x_33);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_3;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_33, x_40);
if (lean_is_scalar(x_34)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_34;
}
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_32);
x_44 = lean_array_fget_borrowed(x_39, x_33);
lean_dec(x_33);
lean_inc(x_44);
x_45 = lean_array_push(x_3, x_44);
x_2 = x_43;
x_3 = x_45;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___Array_ofSubarray_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___Array_ofSubarray_spec__0___redArg(x_2, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Array_ofSubarray___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_ofSubarray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Array_ofSubarray___redArg___closed__0;
x_7 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___Array_ofSubarray_spec__0___redArg(x_1, x_5, x_6);
return x_7;
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
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___Array_ofSubarray_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___Array_ofSubarray_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___Array_ofSubarray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___at___Array_ofSubarray_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_ofSubarray___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_ofSubarray___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_ofSubarray___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_ofSubarray(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Array_instCoeSubarray___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_ofSubarray___boxed), 2, 1);
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
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_fget_borrowed(x_1, x_2);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_11 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
lean_dec_ref(x_6);
x_14 = lean_alloc_closure((void*)(l_Array_instAppendSubarray___lam__4___boxed), 2, 1);
lean_closure_set(x_14, 0, x_7);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
x_17 = l_instIteratorStateSubarrayId___redArg___closed__13;
x_18 = l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(x_1, x_17, x_10);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_ofSubarray___redArg___closed__0;
x_21 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_18, x_2, x_14, x_10, x_16, x_20);
x_22 = lean_alloc_closure((void*)(l_Array_instAppendSubarray___lam__4___boxed), 2, 1);
lean_closure_set(x_22, 0, x_11);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_13);
x_25 = l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(x_3, x_17, x_10);
x_26 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_25, x_4, x_22, x_10, x_24, x_20);
x_27 = l_Array_append___redArg(x_21, x_26);
lean_dec_ref(x_26);
x_28 = lean_array_get_size(x_27);
x_29 = l_Array_toSubarray___redArg(x_27, x_19, x_28);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_3 = lean_alloc_closure((void*)(l_Array_instAppendSubarray___lam__1), 6, 4);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_2);
lean_closure_set(x_3, 2, x_2);
lean_closure_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_instAppendSubarray___lam__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_instAppendSubarray___lam__4(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_7 = lean_alloc_closure((void*)(l_Array_instAppendSubarray___lam__4___boxed), 2, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_11 = l_instIteratorLoopStateSubarrayIdOfMonad___redArg___closed__0;
x_12 = l_Array_ofSubarray___redArg___closed__0;
x_13 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_11, x_6, x_7, x_10, x_9, x_12);
x_14 = l_Array_Array_repr___redArg(x_1, x_13);
x_15 = l_Array_Subarray_repr___redArg___closed__1;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
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
LEAN_EXPORT lean_object* l_Array_instReprSubarray___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_instReprSubarray___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Array_instToStringSubarray___redArg___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_alloc_closure((void*)(l_Array_instAppendSubarray___lam__4___boxed), 2, 1);
lean_closure_set(x_8, 0, x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
x_11 = l_instIteratorStateSubarrayId___redArg___closed__9;
x_12 = l_instIteratorStateSubarrayId___redArg___closed__13;
x_13 = l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(x_1, x_12, x_11);
x_14 = l_Array_ofSubarray___redArg___closed__0;
x_15 = l_Std_Iterators_IterM_DefaultConsumers_toArrayMapped_go___redArg(x_13, x_2, x_8, x_11, x_10, x_14);
x_16 = l_Array_instToStringSubarray___redArg___lam__3___closed__0;
x_17 = lean_array_to_list(x_15);
x_18 = l_List_toString___redArg(x_3, x_17);
x_19 = lean_string_append(x_16, x_18);
lean_dec_ref(x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_instToStringSubarray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_instIteratorCollectStateSubarrayId___redArg___closed__0;
x_3 = lean_alloc_closure((void*)(l_Array_instToStringSubarray___redArg___lam__3), 4, 3);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_2);
lean_closure_set(x_3, 2, x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Subarray_toArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_ofSubarray___redArg(x_1);
return x_2;
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
LEAN_EXPORT lean_object* l_Subarray_toArray___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Subarray_toArray___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_toArray___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Subarray_toArray(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
lean_object* initialize_Init_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Slice_Array_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Combinators_Attach(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Combinators_ULift(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Slice_Operations(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Omega(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_Array_Iterator(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_Attach(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_ULift(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Operations(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instIteratorStateSubarrayId___redArg___closed__0 = _init_l_instIteratorStateSubarrayId___redArg___closed__0();
lean_mark_persistent(l_instIteratorStateSubarrayId___redArg___closed__0);
l_instIteratorStateSubarrayId___redArg___closed__1 = _init_l_instIteratorStateSubarrayId___redArg___closed__1();
lean_mark_persistent(l_instIteratorStateSubarrayId___redArg___closed__1);
l_instIteratorStateSubarrayId___redArg___closed__2 = _init_l_instIteratorStateSubarrayId___redArg___closed__2();
lean_mark_persistent(l_instIteratorStateSubarrayId___redArg___closed__2);
l_instIteratorStateSubarrayId___redArg___closed__3 = _init_l_instIteratorStateSubarrayId___redArg___closed__3();
lean_mark_persistent(l_instIteratorStateSubarrayId___redArg___closed__3);
l_instIteratorStateSubarrayId___redArg___closed__4 = _init_l_instIteratorStateSubarrayId___redArg___closed__4();
lean_mark_persistent(l_instIteratorStateSubarrayId___redArg___closed__4);
l_instIteratorStateSubarrayId___redArg___closed__5 = _init_l_instIteratorStateSubarrayId___redArg___closed__5();
lean_mark_persistent(l_instIteratorStateSubarrayId___redArg___closed__5);
l_instIteratorStateSubarrayId___redArg___closed__6 = _init_l_instIteratorStateSubarrayId___redArg___closed__6();
lean_mark_persistent(l_instIteratorStateSubarrayId___redArg___closed__6);
l_instIteratorStateSubarrayId___redArg___closed__7 = _init_l_instIteratorStateSubarrayId___redArg___closed__7();
lean_mark_persistent(l_instIteratorStateSubarrayId___redArg___closed__7);
l_instIteratorStateSubarrayId___redArg___closed__8 = _init_l_instIteratorStateSubarrayId___redArg___closed__8();
lean_mark_persistent(l_instIteratorStateSubarrayId___redArg___closed__8);
l_instIteratorStateSubarrayId___redArg___closed__9 = _init_l_instIteratorStateSubarrayId___redArg___closed__9();
lean_mark_persistent(l_instIteratorStateSubarrayId___redArg___closed__9);
l_instIteratorStateSubarrayId___redArg___closed__10 = _init_l_instIteratorStateSubarrayId___redArg___closed__10();
lean_mark_persistent(l_instIteratorStateSubarrayId___redArg___closed__10);
l_instIteratorStateSubarrayId___redArg___closed__11 = _init_l_instIteratorStateSubarrayId___redArg___closed__11();
lean_mark_persistent(l_instIteratorStateSubarrayId___redArg___closed__11);
l_instIteratorStateSubarrayId___redArg___closed__12 = _init_l_instIteratorStateSubarrayId___redArg___closed__12();
lean_mark_persistent(l_instIteratorStateSubarrayId___redArg___closed__12);
l_instIteratorStateSubarrayId___redArg___closed__13 = _init_l_instIteratorStateSubarrayId___redArg___closed__13();
lean_mark_persistent(l_instIteratorStateSubarrayId___redArg___closed__13);
l_instIteratorCollectStateSubarrayId___redArg___closed__0 = _init_l_instIteratorCollectStateSubarrayId___redArg___closed__0();
lean_mark_persistent(l_instIteratorCollectStateSubarrayId___redArg___closed__0);
l_instIteratorCollectStateSubarrayId___redArg___closed__1 = _init_l_instIteratorCollectStateSubarrayId___redArg___closed__1();
lean_mark_persistent(l_instIteratorCollectStateSubarrayId___redArg___closed__1);
l_instIteratorCollectPartialStateSubarrayId___redArg___closed__0 = _init_l_instIteratorCollectPartialStateSubarrayId___redArg___closed__0();
lean_mark_persistent(l_instIteratorCollectPartialStateSubarrayId___redArg___closed__0);
l_instIteratorLoopStateSubarrayIdOfMonad___redArg___closed__0 = _init_l_instIteratorLoopStateSubarrayIdOfMonad___redArg___closed__0();
lean_mark_persistent(l_instIteratorLoopStateSubarrayIdOfMonad___redArg___closed__0);
l_instIteratorSizeStateSubarrayId___closed__0 = _init_l_instIteratorSizeStateSubarrayId___closed__0();
lean_mark_persistent(l_instIteratorSizeStateSubarrayId___closed__0);
l_instIteratorSizeStateSubarrayId___closed__1 = _init_l_instIteratorSizeStateSubarrayId___closed__1();
lean_mark_persistent(l_instIteratorSizeStateSubarrayId___closed__1);
l_instIteratorSizePartialStateSubarrayId___closed__0 = _init_l_instIteratorSizePartialStateSubarrayId___closed__0();
lean_mark_persistent(l_instIteratorSizePartialStateSubarrayId___closed__0);
l_instIteratorSizePartialStateSubarrayId___closed__1 = _init_l_instIteratorSizePartialStateSubarrayId___closed__1();
lean_mark_persistent(l_instIteratorSizePartialStateSubarrayId___closed__1);
l_Subarray_foldlM___redArg___closed__0 = _init_l_Subarray_foldlM___redArg___closed__0();
lean_mark_persistent(l_Subarray_foldlM___redArg___closed__0);
l_Subarray_foldlM___redArg___closed__1 = _init_l_Subarray_foldlM___redArg___closed__1();
lean_mark_persistent(l_Subarray_foldlM___redArg___closed__1);
l_Array_ofSubarray___redArg___closed__0 = _init_l_Array_ofSubarray___redArg___closed__0();
lean_mark_persistent(l_Array_ofSubarray___redArg___closed__0);
l_Array_instCoeSubarray___closed__0 = _init_l_Array_instCoeSubarray___closed__0();
lean_mark_persistent(l_Array_instCoeSubarray___closed__0);
l_Array_Subarray_repr___redArg___closed__0 = _init_l_Array_Subarray_repr___redArg___closed__0();
lean_mark_persistent(l_Array_Subarray_repr___redArg___closed__0);
l_Array_Subarray_repr___redArg___closed__1 = _init_l_Array_Subarray_repr___redArg___closed__1();
lean_mark_persistent(l_Array_Subarray_repr___redArg___closed__1);
l_Array_instToStringSubarray___redArg___lam__3___closed__0 = _init_l_Array_instToStringSubarray___redArg___lam__3___closed__0();
lean_mark_persistent(l_Array_instToStringSubarray___redArg___lam__3___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

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
LEAN_EXPORT lean_object* l_instIteratorCollectPartialStateListSliceId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_ListSlice_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopPartialStateListSliceIdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSlice___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ListSlice_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instIteratorCollectPartialStateListSliceId___boxed(lean_object*, lean_object*);
lean_object* l_Std_Iterators_Take_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_instIteratorStateListSliceId___closed__10;
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instForInListSlice___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instIteratorStateListSliceId___closed__11;
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_Take_instIterator___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_instToStringListSlice___redArg___lam__2___closed__0;
lean_object* l_Std_Iterators_instIteratorListIteratorOfPure___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_List_toSlice___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_instIteratorCollectPartialStateListSliceId___closed__0;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instIteratorStateListSliceId___closed__8;
LEAN_EXPORT lean_object* l_List_ListSlice_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopStateListSliceIdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instIteratorStateListSliceId___closed__5;
LEAN_EXPORT lean_object* l_List_instReprListSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopPartialStateListSliceIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToIteratorListSliceId(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_instIteratorCollectStateListSliceId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ofSlice___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_instIteratorStateListSliceId___closed__3;
static lean_object* l_instIteratorStateListSliceId___closed__2;
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorCollectStateListSliceId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ofSlice___redArg___lam__1___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instAppendListSlice(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSlice___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopStateListSliceIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_Take_instIteratorCollectPartial___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorStateListSliceId___boxed(lean_object*, lean_object*);
static lean_object* l_instIteratorStateListSliceId___closed__0;
static lean_object* l_instIteratorStateListSliceId___closed__4;
static lean_object* l_instIteratorStateListSliceId___closed__1;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopPartialStateListSliceIdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_instAppendListSlice___closed__0;
static lean_object* l_instIteratorCollectStateListSliceId___closed__0;
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData(lean_object*);
LEAN_EXPORT lean_object* l_List_ofSlice___redArg___lam__1(lean_object*);
static lean_object* l_instIteratorStateListSliceId___closed__9;
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instToStringListSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInListSlice___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorLoopStateListSliceIdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ListSlice_toList(lean_object*, lean_object*);
static lean_object* l_List_ListSlice_repr___redArg___closed__0;
LEAN_EXPORT lean_object* l_instForInListSlice___lam__1___boxed(lean_object*);
lean_object* l_Std_Iterators_Take_instIteratorLoopPartial___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_instIteratorStateListSliceId___closed__6;
LEAN_EXPORT lean_object* l_List_ofSlice___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_instAppendListSlice___closed__1;
LEAN_EXPORT lean_object* l_List_ofSlice(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Iterators_Take_instIteratorCollect___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instIteratorStateListSliceId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToIteratorListSliceId___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_ListSlice_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_ofSlice___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_instIteratorStateListSliceId___closed__7;
LEAN_EXPORT lean_object* l_instToIteratorListSliceId___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_instToIteratorListSliceId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instToIteratorListSliceId___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_instIteratorStateListSliceId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateListSliceId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateListSliceId___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateListSliceId___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateListSliceId___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateListSliceId___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateListSliceId___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_instIteratorStateListSliceId___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instIteratorStateListSliceId___closed__1;
x_2 = l_instIteratorStateListSliceId___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_instIteratorStateListSliceId___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_instIteratorStateListSliceId___closed__5;
x_2 = l_instIteratorStateListSliceId___closed__4;
x_3 = l_instIteratorStateListSliceId___closed__3;
x_4 = l_instIteratorStateListSliceId___closed__2;
x_5 = l_instIteratorStateListSliceId___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_instIteratorStateListSliceId___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instIteratorStateListSliceId___closed__6;
x_2 = l_instIteratorStateListSliceId___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_instIteratorStateListSliceId___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instIteratorStateListSliceId___closed__2;
x_2 = lean_alloc_closure((void*)(l_Std_Iterators_instIteratorListIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instIteratorStateListSliceId___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instIteratorStateListSliceId___closed__10;
x_2 = l_instIteratorStateListSliceId___closed__9;
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_Take_instIterator___redArg___lam__1), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorStateListSliceId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorStateListSliceId___closed__11;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorStateListSliceId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorStateListSliceId(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_instIteratorCollectStateListSliceId___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instIteratorStateListSliceId___closed__10;
x_2 = l_instIteratorStateListSliceId___closed__9;
x_3 = l_Std_Iterators_Take_instIteratorCollect___redArg(x_2, x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorCollectStateListSliceId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorCollectStateListSliceId___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorCollectStateListSliceId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorCollectStateListSliceId(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_instIteratorCollectPartialStateListSliceId___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instIteratorStateListSliceId___closed__10;
x_2 = l_instIteratorStateListSliceId___closed__9;
x_3 = l_Std_Iterators_Take_instIteratorCollectPartial___redArg(x_2, x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorCollectPartialStateListSliceId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorCollectPartialStateListSliceId___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorCollectPartialStateListSliceId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instIteratorCollectPartialStateListSliceId(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopStateListSliceIdOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_instIteratorStateListSliceId___closed__9;
x_3 = l_instIteratorStateListSliceId___closed__10;
x_4 = l_Std_Iterators_Take_instIteratorLoop___redArg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopStateListSliceIdOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instIteratorLoopStateListSliceIdOfMonad___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopStateListSliceIdOfMonad___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instIteratorLoopStateListSliceIdOfMonad(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopPartialStateListSliceIdOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_instIteratorStateListSliceId___closed__9;
x_3 = l_instIteratorStateListSliceId___closed__10;
x_4 = l_Std_Iterators_Take_instIteratorLoopPartial___redArg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopPartialStateListSliceIdOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instIteratorLoopPartialStateListSliceIdOfMonad___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instIteratorLoopPartialStateListSliceIdOfMonad___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_instIteratorLoopPartialStateListSliceIdOfMonad(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
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
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_instToIteratorListSliceId___redArg(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_instIteratorLoopStateListSliceIdOfMonad___redArg(x_1);
x_8 = lean_apply_7(x_7, x_2, lean_box(0), lean_box(0), lean_box(0), x_5, x_6, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_instSliceSizeListSliceData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_instSliceSizeListSliceData___lam__0), 4, 0);
x_3 = lean_alloc_closure((void*)(l_instSliceSizeListSliceData___lam__1___boxed), 3, 0);
x_4 = l_instIteratorStateListSliceId___closed__9;
x_5 = lean_alloc_closure((void*)(l_instSliceSizeListSliceData___lam__2), 4, 3);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
return x_5;
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
LEAN_EXPORT lean_object* l_instForInListSlice___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instForInListSlice___lam__1(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instForInListSlice___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_instForInListSlice___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_8, 0);
x_10 = l_instToIteratorListSliceId___redArg(x_5);
lean_inc_ref(x_9);
x_11 = lean_alloc_closure((void*)(l_instForInListSlice___lam__2), 6, 3);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_1);
x_12 = l_instIteratorLoopStateListSliceIdOfMonad___redArg(x_4);
x_13 = lean_apply_7(x_12, x_2, lean_box(0), lean_box(0), lean_box(0), x_10, x_6, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_instForInListSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_instForInListSlice___lam__0), 4, 0);
x_4 = lean_alloc_closure((void*)(l_instForInListSlice___lam__1___boxed), 1, 0);
x_5 = lean_alloc_closure((void*)(l_instForInListSlice___lam__3), 7, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instForInListSlice___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instForInListSlice___lam__1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_ofSlice___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_ofSlice___redArg___lam__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_ofSlice___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_List_ofSlice___redArg___lam__0___boxed), 2, 0);
x_3 = lean_alloc_closure((void*)(l_List_ofSlice___redArg___lam__1___boxed), 1, 0);
lean_inc_ref(x_1);
x_4 = l_instToIteratorListSliceId___redArg(x_1);
x_5 = l_instIteratorCollectStateListSliceId(lean_box(0), x_1);
lean_dec_ref(x_1);
x_6 = lean_apply_5(x_5, lean_box(0), x_2, lean_box(0), x_3, x_4);
x_7 = lean_array_to_list(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_ofSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_ofSlice___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_ofSlice___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_ofSlice___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_ofSlice___redArg___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_ofSlice___redArg___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_5);
x_7 = l_instToIteratorListSliceId___redArg(x_5);
x_8 = l_instIteratorCollectStateListSliceId(lean_box(0), x_5);
lean_dec_ref(x_5);
x_9 = lean_apply_5(x_8, lean_box(0), x_1, lean_box(0), x_2, x_7);
x_10 = lean_array_to_list(x_9);
lean_inc_ref(x_6);
x_11 = l_instToIteratorListSliceId___redArg(x_6);
x_12 = l_instIteratorCollectStateListSliceId(lean_box(0), x_6);
lean_dec_ref(x_6);
x_13 = lean_apply_5(x_12, lean_box(0), x_3, lean_box(0), x_4, x_11);
x_14 = lean_array_to_list(x_13);
x_15 = l_List_appendTR___redArg(x_10, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_List_lengthTR___redArg(x_15);
x_18 = l_List_toSlice___redArg(x_15, x_16, x_17);
lean_dec(x_17);
lean_dec(x_15);
return x_18;
}
}
static lean_object* _init_l_List_instAppendListSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_ofSlice___redArg___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_List_instAppendListSlice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_ofSlice___redArg___lam__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_instAppendListSlice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_List_instAppendListSlice___closed__0;
x_3 = l_List_instAppendListSlice___closed__1;
x_4 = lean_alloc_closure((void*)(l_List_instAppendListSlice___lam__4), 6, 4);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_2);
lean_closure_set(x_4, 3, x_3);
return x_4;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = l_List_instAppendListSlice___closed__0;
x_4 = l_List_instAppendListSlice___closed__1;
lean_inc_ref(x_2);
x_5 = l_instToIteratorListSliceId___redArg(x_2);
x_6 = l_instIteratorCollectStateListSliceId(lean_box(0), x_2);
lean_dec_ref(x_2);
x_7 = lean_apply_5(x_6, lean_box(0), x_3, lean_box(0), x_4, x_5);
x_8 = lean_array_to_list(x_7);
lean_inc(x_8);
x_9 = l_List_repr___redArg(x_1, x_8);
x_10 = l_List_ListSlice_repr___redArg___closed__1;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_List_lengthTR___redArg(x_8);
lean_dec(x_8);
x_13 = l_Nat_reprFast(x_12);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
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
LEAN_EXPORT lean_object* l_List_instReprListSlice___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_instReprListSlice___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_4);
x_5 = l_instToIteratorListSliceId___redArg(x_4);
x_6 = l_instIteratorCollectStateListSliceId(lean_box(0), x_4);
lean_dec_ref(x_4);
x_7 = lean_apply_5(x_6, lean_box(0), x_1, lean_box(0), x_2, x_5);
x_8 = l_List_instToStringListSlice___redArg___lam__2___closed__0;
x_9 = lean_array_to_list(x_7);
x_10 = l_List_toString___redArg(x_3, x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec_ref(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_instToStringListSlice___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_List_instAppendListSlice___closed__0;
x_3 = l_List_instAppendListSlice___closed__1;
x_4 = lean_alloc_closure((void*)(l_List_instToStringListSlice___redArg___lam__2), 4, 3);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_1);
return x_4;
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
LEAN_EXPORT lean_object* l_ListSlice_toList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_ofSlice___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ListSlice_toList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_ofSlice___redArg(x_2);
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
l_instIteratorStateListSliceId___closed__0 = _init_l_instIteratorStateListSliceId___closed__0();
lean_mark_persistent(l_instIteratorStateListSliceId___closed__0);
l_instIteratorStateListSliceId___closed__1 = _init_l_instIteratorStateListSliceId___closed__1();
lean_mark_persistent(l_instIteratorStateListSliceId___closed__1);
l_instIteratorStateListSliceId___closed__2 = _init_l_instIteratorStateListSliceId___closed__2();
lean_mark_persistent(l_instIteratorStateListSliceId___closed__2);
l_instIteratorStateListSliceId___closed__3 = _init_l_instIteratorStateListSliceId___closed__3();
lean_mark_persistent(l_instIteratorStateListSliceId___closed__3);
l_instIteratorStateListSliceId___closed__4 = _init_l_instIteratorStateListSliceId___closed__4();
lean_mark_persistent(l_instIteratorStateListSliceId___closed__4);
l_instIteratorStateListSliceId___closed__5 = _init_l_instIteratorStateListSliceId___closed__5();
lean_mark_persistent(l_instIteratorStateListSliceId___closed__5);
l_instIteratorStateListSliceId___closed__6 = _init_l_instIteratorStateListSliceId___closed__6();
lean_mark_persistent(l_instIteratorStateListSliceId___closed__6);
l_instIteratorStateListSliceId___closed__7 = _init_l_instIteratorStateListSliceId___closed__7();
lean_mark_persistent(l_instIteratorStateListSliceId___closed__7);
l_instIteratorStateListSliceId___closed__8 = _init_l_instIteratorStateListSliceId___closed__8();
lean_mark_persistent(l_instIteratorStateListSliceId___closed__8);
l_instIteratorStateListSliceId___closed__9 = _init_l_instIteratorStateListSliceId___closed__9();
lean_mark_persistent(l_instIteratorStateListSliceId___closed__9);
l_instIteratorStateListSliceId___closed__10 = _init_l_instIteratorStateListSliceId___closed__10();
lean_mark_persistent(l_instIteratorStateListSliceId___closed__10);
l_instIteratorStateListSliceId___closed__11 = _init_l_instIteratorStateListSliceId___closed__11();
lean_mark_persistent(l_instIteratorStateListSliceId___closed__11);
l_instIteratorCollectStateListSliceId___closed__0 = _init_l_instIteratorCollectStateListSliceId___closed__0();
lean_mark_persistent(l_instIteratorCollectStateListSliceId___closed__0);
l_instIteratorCollectPartialStateListSliceId___closed__0 = _init_l_instIteratorCollectPartialStateListSliceId___closed__0();
lean_mark_persistent(l_instIteratorCollectPartialStateListSliceId___closed__0);
l_List_instAppendListSlice___closed__0 = _init_l_List_instAppendListSlice___closed__0();
lean_mark_persistent(l_List_instAppendListSlice___closed__0);
l_List_instAppendListSlice___closed__1 = _init_l_List_instAppendListSlice___closed__1();
lean_mark_persistent(l_List_instAppendListSlice___closed__1);
l_List_ListSlice_repr___redArg___closed__0 = _init_l_List_ListSlice_repr___redArg___closed__0();
lean_mark_persistent(l_List_ListSlice_repr___redArg___closed__0);
l_List_ListSlice_repr___redArg___closed__1 = _init_l_List_ListSlice_repr___redArg___closed__1();
lean_mark_persistent(l_List_ListSlice_repr___redArg___closed__1);
l_List_instToStringListSlice___redArg___lam__2___closed__0 = _init_l_List_instToStringListSlice___redArg___lam__2___closed__0();
lean_mark_persistent(l_List_instToStringListSlice___redArg___lam__2___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Monadic.Collect
// Imports: public import Init.Data.Iterators.Consumers.Monadic.Partial public import Init.Data.Iterators.Consumers.Monadic.Total public import Init.Data.Iterators.Internal.LawfulMonadLiftFunction public import Init.WFExtrinsicFix
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toListRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toList___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toListRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toListRev___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_IterM_toArray___redArg___closed__0;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toListRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toListRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_IterM_toList___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_array_push(x_1, x_6);
x_8 = lean_apply_3(x_2, x_5, x_7, lean_box(0));
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec_ref(x_4);
x_10 = lean_apply_3(x_2, x_9, x_1, lean_box(0));
return x_10;
}
default: 
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_apply_2(x_3, lean_box(0), x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_1);
x_8 = lean_apply_1(x_2, x_4);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_6);
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_8, x_3, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toArray_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec_ref(x_4);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_9);
x_12 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_11, x_6, x_7);
return x_12;
}
}
static lean_object* _init_l_Std_IterM_toArray___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toArray___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Std_IterM_toArray___redArg___closed__0;
x_8 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_5);
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_8, x_3, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Std_IterM_toArray___redArg___closed__0;
x_11 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_8);
x_12 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_11, x_6, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toArray___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Std_IterM_toArray___redArg___closed__0;
x_8 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_5);
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_8, x_3, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Std_IterM_toArray___redArg___closed__0;
x_11 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_8);
x_12 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_11, x_6, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toArray___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Std_IterM_toArray___redArg___closed__0;
x_8 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_5);
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_8, x_3, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Std_IterM_toArray___redArg___closed__0;
x_12 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_9);
x_13 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_12, x_7, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 0, x_7);
x_8 = lean_apply_3(x_2, x_6, x_4, lean_box(0));
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_apply_3(x_2, x_9, x_11, lean_box(0));
return x_12;
}
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec_ref(x_4);
x_14 = lean_apply_3(x_2, x_13, x_1, lean_box(0));
return x_14;
}
default: 
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_apply_2(x_3, lean_box(0), x_1);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_1);
x_8 = lean_apply_1(x_2, x_4);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_6);
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_8, x_3, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_9);
x_12 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_11, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_5);
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_8, x_3, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toListRev(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_8);
x_12 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_11, x_6, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toListRev___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_5);
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_8, x_3, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toListRev(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_8);
x_12 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_11, x_6, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toListRev___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_5);
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_8, x_3, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toListRev(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = lean_box(0);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_toListRev_go___redArg___lam__1), 6, 3);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_9);
x_13 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_12, x_7, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toList___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_to_list(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_IterM_toList___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_IterM_toList___redArg___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toList___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = l_Std_IterM_toList___redArg___closed__0;
x_10 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_6);
x_11 = l_Std_IterM_toArray___redArg___closed__0;
x_12 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_10, x_3, x_11);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = l_Std_IterM_toList___redArg___closed__0;
x_13 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_9);
x_14 = l_Std_IterM_toArray___redArg___closed__0;
x_15 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_13, x_6, x_14);
x_16 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toList___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = l_Std_IterM_toList___redArg___closed__0;
x_10 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_6);
x_11 = l_Std_IterM_toArray___redArg___closed__0;
x_12 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_10, x_3, x_11);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = l_Std_IterM_toList___redArg___closed__0;
x_13 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_9);
x_14 = l_Std_IterM_toArray___redArg___closed__0;
x_15 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_13, x_6, x_14);
x_16 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toList___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = l_Std_IterM_toList___redArg___closed__0;
x_10 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_6);
x_11 = l_Std_IterM_toArray___redArg___closed__0;
x_12 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_10, x_3, x_11);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec_ref(x_4);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = l_Std_IterM_toList___redArg___closed__0;
x_14 = lean_alloc_closure((void*)(l_Std_IterM_toArray_go___redArg___lam__1), 6, 3);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_10);
x_15 = l_Std_IterM_toArray___redArg___closed__0;
x_16 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_14, x_7, x_15);
x_17 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_16);
return x_17;
}
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Partial(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Total(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(uint8_t builtin);
lean_object* initialize_Init_WFExtrinsicFix(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFExtrinsicFix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_IterM_toArray___redArg___closed__0 = _init_l_Std_IterM_toArray___redArg___closed__0();
lean_mark_persistent(l_Std_IterM_toArray___redArg___closed__0);
l_Std_IterM_toList___redArg___closed__0 = _init_l_Std_IterM_toList___redArg___closed__0();
lean_mark_persistent(l_Std_IterM_toList___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

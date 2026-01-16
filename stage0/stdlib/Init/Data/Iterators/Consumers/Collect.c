// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Collect
// Imports: public import Init.Data.Iterators.Consumers.Partial public import Init.Data.Iterators.Consumers.Total public import Init.Data.Iterators.Consumers.Monadic.Collect
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
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toListRev(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toListRev___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toListRev___redArg(lean_object*, lean_object*);
static lean_object* l_Std_Iter_toArray___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Iter_Total_toArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toListRev(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toListRev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toListRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toList(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toListRev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toArray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_2);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_array_push(x_3, x_7);
x_9 = lean_apply_3(x_4, x_6, x_8, lean_box(0));
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec_ref(x_5);
x_11 = lean_apply_3(x_4, x_10, x_3, lean_box(0));
return x_11;
}
default: 
{
lean_dec_ref(x_4);
return x_3;
}
}
}
}
static lean_object* _init_l_Std_Iter_toArray___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Std_Iter_toArray___redArg___closed__0;
x_5 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = l_Std_Iter_toArray___redArg___closed__0;
x_7 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_5, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Std_Iter_toArray___redArg___closed__0;
x_5 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = l_Std_Iter_toArray___redArg___closed__0;
x_7 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_5, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Std_Iter_toArray___redArg___closed__0;
x_5 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = l_Std_Iter_toArray___redArg___closed__0;
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_6, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toListRev___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_2);
switch (lean_obj_tag(x_5)) {
case 0:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_8);
x_9 = lean_apply_3(x_4, x_7, x_5, lean_box(0));
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_apply_3(x_4, x_10, x_12, lean_box(0));
return x_13;
}
}
case 1:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec_ref(x_5);
x_15 = lean_apply_3(x_4, x_14, x_3, lean_box(0));
return x_15;
}
default: 
{
lean_dec_ref(x_4);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toListRev___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_box(0);
x_5 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toListRev(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_box(0);
x_7 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_5, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toListRev___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_box(0);
x_5 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toListRev(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_box(0);
x_7 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_5, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toListRev___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_box(0);
x_5 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toListRev(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = lean_box(0);
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_6, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toList___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Std_Iter_toArray___redArg___closed__0;
x_5 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_3, x_2, x_4);
x_6 = lean_array_to_list(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = l_Std_Iter_toArray___redArg___closed__0;
x_7 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_5, x_4, x_6);
x_8 = lean_array_to_list(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toList___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Std_Iter_toArray___redArg___closed__0;
x_5 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_3, x_2, x_4);
x_6 = lean_array_to_list(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = l_Std_Iter_toArray___redArg___closed__0;
x_7 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_5, x_4, x_6);
x_8 = lean_array_to_list(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toList___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Std_Iter_toArray___redArg___closed__0;
x_5 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_3, x_2, x_4);
x_6 = lean_array_to_list(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = l_Std_Iter_toArray___redArg___closed__0;
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_6, x_5, x_7);
x_9 = lean_array_to_list(x_8);
return x_9;
}
}
lean_object* initialize_Init_Data_Iterators_Consumers_Partial(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Partial(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Iter_toArray___redArg___closed__0 = _init_l_Std_Iter_toArray___redArg___closed__0();
lean_mark_persistent(l_Std_Iter_toArray___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

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
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Std_Iter_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Iter_toArray___redArg___closed__0 = (const lean_object*)&l_Std_Iter_toArray___redArg___closed__0_value;
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toListRev___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toListRev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toListRev(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toListRev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toListRev(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toListRev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toListRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Iter_toArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
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
x_6 = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
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
x_4 = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
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
x_6 = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
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
x_4 = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
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
x_7 = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_15; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
x_8 = x_5;
x_9 = x_15;
goto block_14;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_10; 
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 0, x_7);
x_10 = x_8;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_3);
x_10 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_11; 
x_11 = lean_apply_3(x_4, x_6, x_10, lean_box(0));
return x_11;
}
}
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec_ref(x_5);
x_17 = lean_apply_3(x_4, x_16, x_3, lean_box(0));
return x_17;
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
x_4 = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
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
x_6 = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
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
x_4 = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
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
x_6 = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
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
x_4 = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
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
x_7 = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_6, x_5, x_7);
x_9 = lean_array_to_list(x_8);
return x_9;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Partial(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Consumers_Partial(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Total(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Partial(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Partial(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Total(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Consumers_Collect(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Consumers_Collect(builtin);
}
#ifdef __cplusplus
}
#endif

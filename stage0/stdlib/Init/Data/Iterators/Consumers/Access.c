// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Access
// Imports: Init.Data.Iterators.Consumers.Partial
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__3_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_atIdxSlow_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_Partial_atIdxSlow_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_Partial_atIdxSlow_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_Partial_atIdxSlow_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_atIdxSlow_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_atIdxSlow_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = lean_apply_1(x_1, x_4);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_3);
x_2 = lean_box(0);
x_3 = x_11;
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_7);
return x_13;
}
}
case 1:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_2 = lean_box(0);
x_4 = x_14;
goto _start;
}
default: 
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_box(0);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_atIdxSlow_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_Iter_atIdxSlow_x3f___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__3_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_3(x_2, x_5, x_6, lean_box(0));
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_8, lean_box(0));
return x_9;
}
default: 
{
lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_apply_1(x_4, lean_box(0));
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__3_splitter___rarg), 4, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__3_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iterators_Iter_atIdxSlow_x3f_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_Partial_atIdxSlow_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = lean_apply_1(x_1, x_4);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_7);
return x_13;
}
}
case 1:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_4 = x_14;
goto _start;
}
default: 
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_box(0);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_Partial_atIdxSlow_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Iterators_Iter_Partial_atIdxSlow_x3f___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_Partial_atIdxSlow_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_Iter_Partial_atIdxSlow_x3f___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init_Data_Iterators_Consumers_Partial(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Consumers_Access(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Partial(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

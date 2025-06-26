// Lean compiler output
// Module: Init.Data.Array.Subarray.Split
// Imports: Init.Data.Array.Basic Init.Data.Array.Subarray Init.Omega
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
LEAN_EXPORT lean_object* l_Subarray_drop___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_take___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_drop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_take___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_split___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_split___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_take(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_split___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_take___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_drop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_split(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_split___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_add(x_5, x_2);
lean_inc(x_7);
lean_inc(x_4);
lean_ctor_set(x_1, 2, x_7);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = lean_nat_add(x_11, x_2);
lean_inc(x_13);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_split(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Subarray_split___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_split___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Subarray_split___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_split___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Subarray_split(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_drop___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_7 = lean_nat_dec_le(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_6);
lean_inc(x_5);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = lean_nat_add(x_9, x_2);
lean_dec(x_9);
x_12 = lean_nat_dec_le(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_inc(x_10);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_10);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_10);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_drop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Subarray_drop___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_drop___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Subarray_drop___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_drop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Subarray_drop(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_take___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_add(x_4, x_2);
x_7 = lean_nat_dec_le(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_6);
return x_1;
}
else
{
lean_dec(x_5);
lean_ctor_set(x_1, 2, x_6);
return x_1;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = lean_nat_add(x_9, x_2);
x_12 = lean_nat_dec_le(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_10);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_11);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_take(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Subarray_take___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_take___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Subarray_take___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_take___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Subarray_take(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Subarray(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Omega(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Subarray_Split(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Subarray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

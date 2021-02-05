// Lean compiler output
// Module: Init.Data.Array.InsertionSort
// Imports: Init.Data.Array.Basic
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
lean_object* l_Array_insertionSort_swapLoop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Array_mapIdx___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertionSort_swapLoop_match__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_insertionSort_traverse_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_insertionSort_traverse(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_insertionSort_swapLoop___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertionSort_swapLoop_match__1(lean_object*, lean_object*);
lean_object* l_Array_insertionSort_traverse_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertionSort_swapLoop_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertionSort(lean_object*);
lean_object* l_Array_insertionSort_swapLoop(lean_object*);
lean_object* l_Array_insertionSort_traverse_match__1(lean_object*);
lean_object* l_Array_insertionSort_traverse___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertionSort_swapLoop_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertionSort_swapLoop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertionSort___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_insertionSort_traverse_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
}
lean_object* l_Array_insertionSort_traverse_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_insertionSort_traverse_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_insertionSort_traverse_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_insertionSort_traverse_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_insertionSort_swapLoop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_4, x_8, lean_box(0));
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_1(x_3, lean_box(0));
return x_10;
}
}
}
lean_object* l_Array_insertionSort_swapLoop_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_insertionSort_swapLoop_match__1___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Array_insertionSort_swapLoop_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_insertionSort_swapLoop_match__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_insertionSort_swapLoop_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_insertionSort_swapLoop_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_insertionSort_swapLoop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_array_fget(x_1, x_4);
lean_inc(x_3);
x_8 = lean_apply_2(x_3, x_6, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fswap(x_1, x_2, x_4);
x_11 = l_Array_insertionSort_swapLoop___rarg(x_3, x_10, x_4, lean_box(0));
return x_11;
}
}
}
lean_object* l_Array_insertionSort_swapLoop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_Array_mapIdxM_map___at_Array_mapIdx___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_2);
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l_Array_insertionSort_swapLoop___rarg___lambda__1___boxed), 5, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_1);
x_7 = l_Array_insertionSort_swapLoop_match__1___rarg(x_3, lean_box(0), x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Array_insertionSort_swapLoop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_insertionSort_swapLoop___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_insertionSort_swapLoop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_insertionSort_swapLoop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_insertionSort_traverse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Array_insertionSort_swapLoop___rarg(x_1, x_2, x_3, lean_box(0));
x_12 = lean_nat_add(x_3, x_7);
lean_dec(x_3);
x_2 = x_11;
x_3 = x_12;
x_4 = x_8;
goto _start;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
lean_object* l_Array_insertionSort_traverse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_insertionSort_traverse___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_insertionSort___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_insertionSort_traverse___rarg(x_2, x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_Array_insertionSort(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_insertionSort___rarg), 2, 0);
return x_2;
}
}
lean_object* initialize_Init_Data_Array_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Array_InsertionSort(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

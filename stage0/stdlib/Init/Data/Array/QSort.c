// Lean compiler output
// Module: Init.Data.Array.QSort
// Imports: Init.Data.Array.Basic Init.Data.Ord
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
LEAN_EXPORT lean_object* l_Array_qpartition_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition_loop(lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Array_qsortOrd___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort(lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition(lean_object*);
uint8_t l_Ordering_isLT(uint8_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Array_qsortOrd___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Array_qsortOrd___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsortOrd___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsortOrd(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Array_qsortOrd___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Array_qsortOrd___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_array_swap(x_5, x_6, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_3);
x_11 = lean_array_get(x_3, x_5, x_7);
lean_inc(x_1);
lean_inc(x_4);
x_12 = lean_apply_2(x_1, x_11, x_4);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_7, x_14);
lean_dec(x_7);
x_7 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_swap(x_5, x_6, x_7);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_20 = lean_nat_add(x_7, x_18);
lean_dec(x_7);
x_5 = x_17;
x_6 = x_19;
x_7 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qpartition_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qpartition_loop___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_qpartition_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qpartition_loop___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_qpartition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_8 = lean_array_fget(x_1, x_6);
x_9 = lean_nat_add(x_3, x_4);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_8);
x_34 = lean_array_get(x_8, x_1, x_11);
lean_inc(x_8);
x_35 = lean_array_get(x_8, x_1, x_3);
lean_inc(x_2);
x_36 = lean_apply_2(x_2, x_34, x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
x_12 = x_1;
goto block_33;
}
else
{
lean_object* x_38; 
x_38 = lean_array_swap(x_1, x_3, x_11);
x_12 = x_38;
goto block_33;
}
block_33:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_8);
x_13 = lean_array_get(x_8, x_12, x_4);
lean_inc(x_8);
x_14 = lean_array_get(x_8, x_12, x_3);
lean_inc(x_2);
lean_inc(x_13);
x_15 = lean_apply_2(x_2, x_13, x_14);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc(x_8);
x_17 = lean_array_get(x_8, x_12, x_11);
lean_inc(x_2);
lean_inc(x_13);
x_18 = lean_apply_2(x_2, x_17, x_13);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_11);
lean_inc(x_3);
x_20 = l_Array_qpartition_loop___rarg(x_2, x_4, x_8, x_13, x_12, x_3, x_3);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_13);
x_21 = lean_array_swap(x_12, x_11, x_4);
lean_dec(x_11);
lean_inc(x_8);
x_22 = lean_array_get(x_8, x_21, x_4);
lean_inc(x_3);
x_23 = l_Array_qpartition_loop___rarg(x_2, x_4, x_8, x_22, x_21, x_3, x_3);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_13);
x_24 = lean_array_swap(x_12, x_3, x_4);
lean_inc(x_8);
x_25 = lean_array_get(x_8, x_24, x_11);
lean_inc(x_8);
x_26 = lean_array_get(x_8, x_24, x_4);
lean_inc(x_2);
lean_inc(x_26);
x_27 = lean_apply_2(x_2, x_25, x_26);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_11);
lean_inc(x_3);
x_29 = l_Array_qpartition_loop___rarg(x_2, x_4, x_8, x_26, x_24, x_3, x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_26);
x_30 = lean_array_swap(x_24, x_11, x_4);
lean_dec(x_11);
lean_inc(x_8);
x_31 = lean_array_get(x_8, x_30, x_4);
lean_inc(x_3);
x_32 = l_Array_qpartition_loop___rarg(x_2, x_4, x_8, x_31, x_30, x_3, x_3);
return x_32;
}
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_6);
lean_ctor_set(x_39, 1, x_1);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Array_qpartition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qpartition___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_qpartition___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qpartition___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Array_qpartition___rarg(x_2, x_1, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_4, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_10 = l_Array_qsort_sort___rarg(x_1, x_8, x_3, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_2 = x_10;
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qsort_sort___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___rarg(x_2, x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qsort___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_qsort___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Array_qsortOrd___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Ordering_isLT(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Array_qsortOrd___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Array_qsortOrd___spec__1___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_nat_dec_lt(x_3, x_4);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_3);
x_7 = l_Array_qpartition___rarg(x_2, x_5, x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_nat_dec_le(x_4, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_11 = l_Array_qsort_sort___at_Array_qsortOrd___spec__1___rarg(x_1, x_9, x_3, x_8);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Array_qsortOrd___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Array_qsortOrd___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_qsortOrd___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_qsort_sort___at_Array_qsortOrd___spec__1___rarg(x_1, x_2, x_6, x_5);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_qsortOrd(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qsortOrd___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Array_qsortOrd___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_qsort_sort___at_Array_qsortOrd___spec__1___rarg___lambda__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Array_qsortOrd___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at_Array_qsortOrd___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Ord(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_QSort(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

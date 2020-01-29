// Lean compiler output
// Module: Init.Data.Array.QSort
// Imports: Init.Data.Array.Basic
#include "runtime/lean.h"
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
lean_object* l_Array_qsortAux(lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_qsort___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main(lean_object*);
lean_object* l_Array_qsort(lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_partition(lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux(lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main(lean_object*);
lean_object* l_Array_partition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_partition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_array_swap(x_5, x_6, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
lean_inc(x_1);
x_11 = lean_array_get(x_1, x_5, x_7);
lean_inc(x_2);
lean_inc(x_4);
x_12 = lean_apply_2(x_2, x_11, x_4);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_7, x_15);
lean_dec(x_7);
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_swap(x_5, x_6, x_7);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_21 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_5 = x_18;
x_6 = x_20;
x_7 = x_21;
goto _start;
}
}
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_1__partitionAux___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_1__partitionAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Array_partition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; 
x_6 = lean_nat_add(x_4, x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_div(x_6, x_7);
lean_dec(x_6);
lean_inc(x_1);
x_34 = lean_array_get(x_1, x_2, x_8);
lean_inc(x_1);
x_35 = lean_array_get(x_1, x_2, x_4);
lean_inc(x_3);
x_36 = lean_apply_2(x_3, x_34, x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
x_38 = l_coeDecidableEq(x_37);
if (x_38 == 0)
{
x_9 = x_2;
goto block_33;
}
else
{
lean_object* x_39; 
x_39 = lean_array_swap(x_2, x_4, x_8);
x_9 = x_39;
goto block_33;
}
block_33:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
lean_inc(x_1);
x_10 = lean_array_get(x_1, x_9, x_5);
lean_inc(x_1);
x_11 = lean_array_get(x_1, x_9, x_4);
lean_inc(x_3);
lean_inc(x_10);
x_12 = lean_apply_2(x_3, x_10, x_11);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
lean_inc(x_1);
x_15 = lean_array_get(x_1, x_9, x_8);
lean_inc(x_3);
lean_inc(x_10);
x_16 = lean_apply_2(x_3, x_15, x_10);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
x_18 = l_coeDecidableEq(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_8);
lean_inc(x_4);
x_19 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_3, x_5, x_10, x_9, x_4, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
x_20 = lean_array_swap(x_9, x_8, x_5);
lean_dec(x_8);
lean_inc(x_1);
x_21 = lean_array_get(x_1, x_20, x_5);
lean_inc(x_4);
x_22 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_3, x_5, x_21, x_20, x_4, x_4);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
lean_dec(x_10);
x_23 = lean_array_swap(x_9, x_4, x_5);
lean_inc(x_1);
x_24 = lean_array_get(x_1, x_23, x_8);
lean_inc(x_1);
x_25 = lean_array_get(x_1, x_23, x_5);
lean_inc(x_3);
lean_inc(x_25);
x_26 = lean_apply_2(x_3, x_24, x_25);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
x_28 = l_coeDecidableEq(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_8);
lean_inc(x_4);
x_29 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_3, x_5, x_25, x_23, x_4, x_4);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
x_30 = lean_array_swap(x_23, x_8, x_5);
lean_dec(x_8);
lean_inc(x_1);
x_31 = lean_array_get(x_1, x_30, x_5);
lean_inc(x_4);
x_32 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_3, x_5, x_31, x_30, x_4, x_4);
return x_32;
}
}
}
}
}
lean_object* l_Array_partition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_partition___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_partition___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_partition___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Array_qsortAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_4, x_5);
if (x_15 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_16 = lean_nat_add(x_4, x_5);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_div(x_16, x_17);
lean_dec(x_16);
lean_inc(x_1);
x_44 = lean_array_get(x_1, x_3, x_18);
lean_inc(x_1);
x_45 = lean_array_get(x_1, x_3, x_4);
lean_inc(x_2);
x_46 = lean_apply_2(x_2, x_44, x_45);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
x_48 = l_coeDecidableEq(x_47);
if (x_48 == 0)
{
x_19 = x_3;
goto block_43;
}
else
{
lean_object* x_49; 
x_49 = lean_array_swap(x_3, x_4, x_18);
x_19 = x_49;
goto block_43;
}
block_43:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
lean_inc(x_1);
x_20 = lean_array_get(x_1, x_19, x_5);
lean_inc(x_1);
x_21 = lean_array_get(x_1, x_19, x_4);
lean_inc(x_2);
lean_inc(x_20);
x_22 = lean_apply_2(x_2, x_20, x_21);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
x_24 = l_coeDecidableEq(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
lean_inc(x_1);
x_25 = lean_array_get(x_1, x_19, x_18);
lean_inc(x_2);
lean_inc(x_20);
x_26 = lean_apply_2(x_2, x_25, x_20);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
x_28 = l_coeDecidableEq(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_18);
lean_inc_n(x_4, 2);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_20, x_19, x_4, x_4);
x_6 = x_29;
goto block_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_20);
x_30 = lean_array_swap(x_19, x_18, x_5);
lean_dec(x_18);
lean_inc(x_1);
x_31 = lean_array_get(x_1, x_30, x_5);
lean_inc_n(x_4, 2);
lean_inc(x_2);
lean_inc(x_1);
x_32 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_31, x_30, x_4, x_4);
x_6 = x_32;
goto block_14;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; 
lean_dec(x_20);
x_33 = lean_array_swap(x_19, x_4, x_5);
lean_inc(x_1);
x_34 = lean_array_get(x_1, x_33, x_18);
lean_inc(x_1);
x_35 = lean_array_get(x_1, x_33, x_5);
lean_inc(x_2);
lean_inc(x_35);
x_36 = lean_apply_2(x_2, x_34, x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
x_38 = l_coeDecidableEq(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_18);
lean_inc_n(x_4, 2);
lean_inc(x_2);
lean_inc(x_1);
x_39 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_35, x_33, x_4, x_4);
x_6 = x_39;
goto block_14;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_35);
x_40 = lean_array_swap(x_33, x_18, x_5);
lean_dec(x_18);
lean_inc(x_1);
x_41 = lean_array_get(x_1, x_40, x_5);
lean_inc_n(x_4, 2);
lean_inc(x_2);
lean_inc(x_1);
x_42 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_41, x_40, x_4, x_4);
x_6 = x_42;
goto block_14;
}
}
}
}
block_14:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_5, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Array_qsortAux___main___rarg(x_1, x_2, x_8, x_4, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_3 = x_10;
x_4 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
}
lean_object* l_Array_qsortAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qsortAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_qsortAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_qsortAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Array_qsortAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_qsortAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_qsortAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qsortAux___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_qsortAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_qsortAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Array_qsort___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_qsortAux___main___rarg(x_1, x_3, x_2, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_qsort(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qsort___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_qsort___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_qsort___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* initialize_Init_Data_Array_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Array_QSort(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

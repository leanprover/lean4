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
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux(lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main(lean_object*);
lean_object* l_Array_partition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_partition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; 
lean_inc(x_1);
x_11 = lean_array_get(x_1, x_5, x_7);
lean_inc(x_2);
lean_inc(x_4);
x_12 = lean_apply_2(x_2, x_11, x_4);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
x_14 = 1;
x_15 = l_Bool_DecidableEq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_7, x_16);
lean_dec(x_7);
x_7 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_swap(x_5, x_6, x_7);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_6, x_20);
lean_dec(x_6);
x_22 = lean_nat_add(x_7, x_20);
lean_dec(x_7);
x_5 = x_19;
x_6 = x_21;
x_7 = x_22;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; 
x_6 = lean_nat_add(x_4, x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_div(x_6, x_7);
lean_dec(x_6);
lean_inc(x_1);
x_35 = lean_array_get(x_1, x_2, x_8);
lean_inc(x_1);
x_36 = lean_array_get(x_1, x_2, x_4);
lean_inc(x_3);
x_37 = lean_apply_2(x_3, x_35, x_36);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
x_39 = 1;
x_40 = l_Bool_DecidableEq(x_38, x_39);
if (x_40 == 0)
{
x_9 = x_2;
goto block_34;
}
else
{
lean_object* x_41; 
x_41 = lean_array_swap(x_2, x_4, x_8);
x_9 = x_41;
goto block_34;
}
block_34:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; 
lean_inc(x_1);
x_10 = lean_array_get(x_1, x_9, x_5);
lean_inc(x_1);
x_11 = lean_array_get(x_1, x_9, x_4);
lean_inc(x_3);
lean_inc(x_10);
x_12 = lean_apply_2(x_3, x_10, x_11);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
x_14 = 1;
x_15 = l_Bool_DecidableEq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
lean_inc(x_1);
x_16 = lean_array_get(x_1, x_9, x_8);
lean_inc(x_3);
lean_inc(x_10);
x_17 = lean_apply_2(x_3, x_16, x_10);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
x_19 = l_Bool_DecidableEq(x_18, x_14);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_8);
lean_inc(x_4);
x_20 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_3, x_5, x_10, x_9, x_4, x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_21 = lean_array_swap(x_9, x_8, x_5);
lean_dec(x_8);
lean_inc(x_1);
x_22 = lean_array_get(x_1, x_21, x_5);
lean_inc(x_4);
x_23 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_3, x_5, x_22, x_21, x_4, x_4);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; 
lean_dec(x_10);
x_24 = lean_array_swap(x_9, x_4, x_5);
lean_inc(x_1);
x_25 = lean_array_get(x_1, x_24, x_8);
lean_inc(x_1);
x_26 = lean_array_get(x_1, x_24, x_5);
lean_inc(x_3);
lean_inc(x_26);
x_27 = lean_apply_2(x_3, x_25, x_26);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
x_29 = l_Bool_DecidableEq(x_28, x_14);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_8);
lean_inc(x_4);
x_30 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_3, x_5, x_26, x_24, x_4, x_4);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_31 = lean_array_swap(x_24, x_8, x_5);
lean_dec(x_8);
lean_inc(x_1);
x_32 = lean_array_get(x_1, x_31, x_5);
lean_inc(x_4);
x_33 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_3, x_5, x_32, x_31, x_4, x_4);
return x_33;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; 
x_16 = lean_nat_add(x_4, x_5);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_div(x_16, x_17);
lean_dec(x_16);
lean_inc(x_1);
x_45 = lean_array_get(x_1, x_3, x_18);
lean_inc(x_1);
x_46 = lean_array_get(x_1, x_3, x_4);
lean_inc(x_2);
x_47 = lean_apply_2(x_2, x_45, x_46);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
x_49 = 1;
x_50 = l_Bool_DecidableEq(x_48, x_49);
if (x_50 == 0)
{
x_19 = x_3;
goto block_44;
}
else
{
lean_object* x_51; 
x_51 = lean_array_swap(x_3, x_4, x_18);
x_19 = x_51;
goto block_44;
}
block_44:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; 
lean_inc(x_1);
x_20 = lean_array_get(x_1, x_19, x_5);
lean_inc(x_1);
x_21 = lean_array_get(x_1, x_19, x_4);
lean_inc(x_2);
lean_inc(x_20);
x_22 = lean_apply_2(x_2, x_20, x_21);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
x_24 = 1;
x_25 = l_Bool_DecidableEq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; 
lean_inc(x_1);
x_26 = lean_array_get(x_1, x_19, x_18);
lean_inc(x_2);
lean_inc(x_20);
x_27 = lean_apply_2(x_2, x_26, x_20);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
x_29 = l_Bool_DecidableEq(x_28, x_24);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_18);
lean_inc_n(x_4, 2);
lean_inc(x_2);
lean_inc(x_1);
x_30 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_20, x_19, x_4, x_4);
x_6 = x_30;
goto block_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
x_31 = lean_array_swap(x_19, x_18, x_5);
lean_dec(x_18);
lean_inc(x_1);
x_32 = lean_array_get(x_1, x_31, x_5);
lean_inc_n(x_4, 2);
lean_inc(x_2);
lean_inc(x_1);
x_33 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_32, x_31, x_4, x_4);
x_6 = x_33;
goto block_14;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; 
lean_dec(x_20);
x_34 = lean_array_swap(x_19, x_4, x_5);
lean_inc(x_1);
x_35 = lean_array_get(x_1, x_34, x_18);
lean_inc(x_1);
x_36 = lean_array_get(x_1, x_34, x_5);
lean_inc(x_2);
lean_inc(x_36);
x_37 = lean_apply_2(x_2, x_35, x_36);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
x_39 = l_Bool_DecidableEq(x_38, x_24);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_18);
lean_inc_n(x_4, 2);
lean_inc(x_2);
lean_inc(x_1);
x_40 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_36, x_34, x_4, x_4);
x_6 = x_40;
goto block_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_36);
x_41 = lean_array_swap(x_34, x_18, x_5);
lean_dec(x_18);
lean_inc(x_1);
x_42 = lean_array_get(x_1, x_41, x_5);
lean_inc_n(x_4, 2);
lean_inc(x_2);
lean_inc(x_1);
x_43 = l___private_Init_Data_Array_QSort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_42, x_41, x_4, x_4);
x_6 = x_43;
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

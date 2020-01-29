// Lean compiler output
// Module: Init.Data.Array.BinSearch
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
lean_object* l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1(lean_object*);
lean_object* l_Array_binInsert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at_Array_binSearch___spec__1(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main(lean_object*, lean_object*);
lean_object* l_Array_modifyM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binInsert(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_binInsertM___at_Array_binInsert___spec__1(lean_object*);
lean_object* l_Array_binInsertM(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at_Array_binInsert___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearch(lean_object*);
lean_object* l_Array_binInsertM___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Array_binSearchContains___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Array_binInsertM___boxed(lean_object*, lean_object*);
lean_object* l_Array_binInsertM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binInsertM___at_Array_binInsert___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_binInsertM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearch___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchContains___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchContains(lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at_Array_binInsert___spec__2(lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_12 = lean_nat_add(x_7, x_8);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_div(x_12, x_13);
lean_dec(x_12);
lean_inc(x_1);
x_15 = lean_array_get(x_1, x_5, x_14);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_15);
x_16 = lean_apply_2(x_3, x_15, x_6);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
x_18 = l_coeDecidableEq(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; uint8_t x_21; 
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_15);
lean_inc(x_6);
x_19 = lean_apply_2(x_3, x_6, x_15);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
x_21 = l_coeDecidableEq(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_15);
x_23 = lean_apply_1(x_4, x_22);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; uint8_t x_26; 
lean_dec(x_15);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_14, x_24);
x_26 = l_coeDecidableEq(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_14, x_27);
lean_dec(x_14);
x_8 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_apply_1(x_4, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_15);
lean_dec(x_7);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_14, x_32);
lean_dec(x_14);
x_7 = x_33;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_binSearchAux___main___rarg___boxed), 8, 0);
return x_3;
}
}
lean_object* l_Array_binSearchAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_binSearchAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_binSearchAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_binSearchAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Array_binSearchAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_binSearchAux___rarg___boxed), 8, 0);
return x_3;
}
}
lean_object* l_Array_binSearchAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_binSearchAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_12);
x_13 = lean_apply_2(x_2, x_12, x_4);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
x_15 = l_coeDecidableEq(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; 
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_4);
x_16 = lean_apply_2(x_2, x_4, x_12);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
x_18 = l_coeDecidableEq(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_12);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_22; 
lean_dec(x_12);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_11, x_20);
x_22 = l_coeDecidableEq(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_11, x_23);
lean_dec(x_11);
x_6 = x_24;
goto _start;
}
else
{
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
lean_dec(x_5);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_11, x_27);
lean_dec(x_11);
x_5 = x_28;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___main___at_Array_binSearch___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Array_binSearch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg(x_1, x_4, x_2, x_3, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_binSearch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearch___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Array_binSearch___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearch___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
uint8_t l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_array_get(x_1, x_3, x_11);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_12);
x_13 = lean_apply_2(x_2, x_12, x_4);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
x_15 = l_coeDecidableEq(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; 
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_4);
x_16 = lean_apply_2(x_2, x_4, x_12);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
x_18 = l_coeDecidableEq(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = 1;
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_11, x_20);
x_22 = l_coeDecidableEq(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_11, x_23);
lean_dec(x_11);
x_6 = x_24;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_26 = 0;
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
lean_dec(x_5);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_11, x_27);
lean_dec(x_11);
x_5 = x_28;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
uint8_t l_Array_binSearchContains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg(x_1, x_4, x_2, x_3, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_binSearchContains(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchContains___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_binSearchContains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_binSearchContains___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
x_9 = l_Array_insertAt___rarg(x_3, x_8, x_4);
lean_dec(x_8);
x_10 = lean_apply_2(x_6, lean_box(0), x_9);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_10 = lean_nat_add(x_8, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
lean_inc(x_2);
x_13 = lean_array_get(x_2, x_6, x_12);
lean_inc(x_3);
lean_inc(x_7);
lean_inc(x_13);
x_14 = lean_apply_2(x_3, x_13, x_7);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; 
lean_dec(x_9);
lean_inc(x_3);
lean_inc(x_7);
x_17 = lean_apply_2(x_3, x_7, x_13);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_20 = lean_array_get_size(x_6);
x_21 = lean_nat_dec_lt(x_12, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_apply_2(x_23, lean_box(0), x_6);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_array_fget(x_6, x_12);
x_26 = lean_array_fset(x_6, x_12, x_2);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_apply_1(x_4, x_25);
x_29 = lean_alloc_closure((void*)(l_Array_modifyM___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_26);
lean_closure_set(x_29, 2, x_12);
x_30 = lean_apply_4(x_27, lean_box(0), lean_box(0), x_28, x_29);
return x_30;
}
}
else
{
x_9 = x_12;
goto _start;
}
}
else
{
uint8_t x_32; uint8_t x_33; 
lean_dec(x_13);
x_32 = lean_nat_dec_eq(x_12, x_8);
x_33 = l_coeDecidableEq(x_32);
if (x_33 == 0)
{
lean_dec(x_8);
x_8 = x_12;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_box(0);
x_37 = lean_apply_1(x_5, x_36);
x_38 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_38, 0, x_1);
lean_closure_set(x_38, 1, x_8);
lean_closure_set(x_38, 2, x_6);
x_39 = lean_apply_4(x_35, lean_box(0), lean_box(0), x_37, x_38);
return x_39;
}
}
}
}
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___rarg), 9, 0);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_1__binInsertAux___rarg), 9, 0);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_Array_BinSearch_1__binInsertAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_binInsertM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_fset(x_2, x_6, x_3);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_Array_binInsertM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_insertAt___rarg(x_2, x_6, x_3);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_Array_binInsertM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_29; uint8_t x_57; uint8_t x_58; 
x_57 = l_Array_isEmpty___rarg(x_6);
x_58 = l_coeDecidableEq(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_59 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_60 = lean_array_get(x_2, x_6, x_59);
lean_inc(x_3);
lean_inc(x_60);
lean_inc(x_7);
x_61 = lean_apply_2(x_3, x_7, x_60);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
x_63 = l_coeDecidableEq(x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
lean_inc(x_3);
lean_inc(x_7);
x_64 = lean_apply_2(x_3, x_60, x_7);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = 1;
x_29 = x_66;
goto block_56;
}
else
{
uint8_t x_67; 
x_67 = 0;
x_29 = x_67;
goto block_56;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
x_69 = lean_box(0);
x_70 = lean_apply_1(x_5, x_69);
x_71 = lean_alloc_closure((void*)(l_Array_binInsertM___rarg___lambda__2), 3, 2);
lean_closure_set(x_71, 0, x_1);
lean_closure_set(x_71, 1, x_6);
x_72 = lean_apply_4(x_68, lean_box(0), lean_box(0), x_70, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
x_74 = lean_box(0);
x_75 = lean_apply_1(x_5, x_74);
x_76 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_76, 0, x_1);
lean_closure_set(x_76, 1, x_6);
x_77 = lean_apply_4(x_73, lean_box(0), lean_box(0), x_75, x_76);
return x_77;
}
block_28:
{
uint8_t x_9; 
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_get_size(x_6);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_13, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_15 = lean_array_get_size(x_6);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
x_18 = lean_nat_dec_lt(x_17, x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_2(x_20, lean_box(0), x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_fget(x_6, x_17);
x_23 = lean_array_fset(x_6, x_17, x_2);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_apply_1(x_4, x_22);
x_26 = lean_alloc_closure((void*)(l_Array_modifyM___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_23);
lean_closure_set(x_26, 2, x_17);
x_27 = lean_apply_4(x_24, lean_box(0), lean_box(0), x_25, x_26);
return x_27;
}
}
}
block_56:
{
uint8_t x_30; 
x_30 = l_coeDecidableEq(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; 
lean_inc(x_2);
x_31 = l_Array_back___rarg(x_2, x_6);
lean_inc(x_3);
lean_inc(x_7);
lean_inc(x_31);
x_32 = lean_apply_2(x_3, x_31, x_7);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
x_34 = l_coeDecidableEq(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
lean_inc(x_3);
lean_inc(x_7);
x_35 = lean_apply_2(x_3, x_7, x_31);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = 1;
x_8 = x_37;
goto block_28;
}
else
{
uint8_t x_38; 
x_38 = 0;
x_8 = x_38;
goto block_28;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_31);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_box(0);
x_41 = lean_apply_1(x_5, x_40);
x_42 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_42, 0, x_1);
lean_closure_set(x_42, 1, x_6);
x_43 = lean_apply_4(x_39, lean_box(0), lean_box(0), x_41, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_44 = lean_array_get_size(x_6);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_lt(x_45, x_44);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_4);
lean_dec(x_2);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_apply_2(x_48, lean_box(0), x_6);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_array_fget(x_6, x_45);
x_51 = lean_array_fset(x_6, x_45, x_2);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
x_53 = lean_apply_1(x_4, x_50);
x_54 = lean_alloc_closure((void*)(l_Array_binInsertM___rarg___lambda__1), 3, 2);
lean_closure_set(x_54, 0, x_1);
lean_closure_set(x_54, 1, x_51);
x_55 = lean_apply_4(x_52, lean_box(0), lean_box(0), x_53, x_54);
return x_55;
}
}
}
}
}
lean_object* l_Array_binInsertM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_binInsertM___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Array_binInsertM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_binInsertM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at_Array_binInsert___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_8 = lean_nat_add(x_6, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_div(x_8, x_9);
lean_dec(x_8);
lean_inc(x_1);
x_11 = lean_array_get(x_1, x_4, x_10);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_11);
x_12 = lean_apply_2(x_2, x_11, x_5);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; uint8_t x_17; 
lean_dec(x_7);
lean_inc(x_2);
lean_inc(x_5);
x_15 = lean_apply_2(x_2, x_5, x_11);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
x_17 = l_coeDecidableEq(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_18 = lean_array_get_size(x_4);
x_19 = lean_nat_dec_lt(x_10, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_4, x_10, x_1);
x_21 = lean_array_fset(x_20, x_10, x_3);
lean_dec(x_10);
return x_21;
}
}
else
{
x_7 = x_10;
goto _start;
}
}
else
{
uint8_t x_23; uint8_t x_24; 
lean_dec(x_11);
x_23 = lean_nat_dec_eq(x_10, x_6);
x_24 = l_coeDecidableEq(x_23);
if (x_24 == 0)
{
lean_dec(x_6);
x_6 = x_10;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_6, x_26);
lean_dec(x_6);
x_28 = l_Array_insertAt___rarg(x_4, x_27, x_3);
lean_dec(x_27);
return x_28;
}
}
}
}
lean_object* l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at_Array_binInsert___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at_Array_binInsert___spec__2___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Array_binInsertM___at_Array_binInsert___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_20; uint8_t x_37; uint8_t x_38; 
x_37 = l_Array_isEmpty___rarg(x_4);
x_38 = l_coeDecidableEq(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; 
x_39 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_40 = lean_array_get(x_1, x_4, x_39);
lean_inc(x_2);
lean_inc(x_40);
lean_inc(x_5);
x_41 = lean_apply_2(x_2, x_5, x_40);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
x_43 = l_coeDecidableEq(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
lean_inc(x_2);
lean_inc(x_5);
x_44 = lean_apply_2(x_2, x_40, x_5);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = 1;
x_20 = x_46;
goto block_36;
}
else
{
uint8_t x_47; 
x_47 = 0;
x_20 = x_47;
goto block_36;
}
}
else
{
lean_object* x_48; 
lean_dec(x_40);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_48 = l_Array_insertAt___rarg(x_4, x_39, x_3);
return x_48;
}
}
else
{
lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_array_push(x_4, x_3);
return x_49;
}
block_19:
{
uint8_t x_7; 
x_7 = l_coeDecidableEq(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at_Array_binInsert___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_11, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_2);
x_13 = lean_array_get_size(x_4);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
x_16 = lean_nat_dec_lt(x_15, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_4, x_15, x_1);
x_18 = lean_array_fset(x_17, x_15, x_3);
lean_dec(x_15);
return x_18;
}
}
}
block_36:
{
uint8_t x_21; 
x_21 = l_coeDecidableEq(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
lean_inc(x_1);
x_22 = l_Array_back___rarg(x_1, x_4);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_22);
x_23 = lean_apply_2(x_2, x_22, x_5);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_inc(x_2);
lean_inc(x_5);
x_26 = lean_apply_2(x_2, x_5, x_22);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = 1;
x_6 = x_28;
goto block_19;
}
else
{
uint8_t x_29; 
x_29 = 0;
x_6 = x_29;
goto block_19;
}
}
else
{
lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_array_push(x_4, x_3);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_5);
lean_dec(x_2);
x_31 = lean_array_get_size(x_4);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
lean_dec(x_31);
if (x_33 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_array_fset(x_4, x_32, x_1);
x_35 = lean_array_fset(x_34, x_32, x_3);
return x_35;
}
}
}
}
}
lean_object* l_Array_binInsertM___at_Array_binInsert___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binInsertM___at_Array_binInsert___spec__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Array_binInsert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_4);
x_5 = l_Array_binInsertM___at_Array_binInsert___spec__1___rarg(x_1, x_2, x_4, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_binInsert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binInsert___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init_Data_Array_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Array_BinSearch(lean_object* w) {
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

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
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
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
x_18 = 1;
x_19 = l_Bool_DecidableEq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; uint8_t x_22; 
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_15);
lean_inc(x_6);
x_20 = lean_apply_2(x_3, x_6, x_15);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
x_22 = l_Bool_DecidableEq(x_21, x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_15);
x_24 = lean_apply_1(x_4, x_23);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; uint8_t x_27; 
lean_dec(x_15);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_14, x_25);
x_27 = l_Bool_DecidableEq(x_26, x_18);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_14, x_28);
lean_dec(x_14);
x_8 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_apply_1(x_4, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_15);
lean_dec(x_7);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_14, x_33);
lean_dec(x_14);
x_7 = x_34;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
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
x_15 = 1;
x_16 = l_Bool_DecidableEq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; 
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_4);
x_17 = lean_apply_2(x_2, x_4, x_12);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
x_19 = l_Bool_DecidableEq(x_18, x_15);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_12);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; 
lean_dec(x_12);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_11, x_21);
x_23 = l_Bool_DecidableEq(x_22, x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_11, x_24);
lean_dec(x_11);
x_6 = x_25;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_5);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_11, x_28);
lean_dec(x_11);
x_5 = x_29;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
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
x_15 = 1;
x_16 = l_Bool_DecidableEq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; 
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_4);
x_17 = lean_apply_2(x_2, x_4, x_12);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
x_19 = l_Bool_DecidableEq(x_18, x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = 1;
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_11, x_21);
x_23 = l_Bool_DecidableEq(x_22, x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_11, x_24);
lean_dec(x_11);
x_6 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = 0;
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_5);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_11, x_28);
lean_dec(x_11);
x_5 = x_29;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
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
x_16 = 1;
x_17 = l_Bool_DecidableEq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; 
lean_dec(x_9);
lean_inc(x_3);
lean_inc(x_7);
x_18 = lean_apply_2(x_3, x_7, x_13);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
x_20 = l_Bool_DecidableEq(x_19, x_16);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_21 = lean_array_get_size(x_6);
x_22 = lean_nat_dec_lt(x_12, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_2(x_24, lean_box(0), x_6);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_array_fget(x_6, x_12);
x_27 = lean_array_fset(x_6, x_12, x_2);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_apply_1(x_4, x_26);
x_30 = lean_alloc_closure((void*)(l_Array_modifyM___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_27);
lean_closure_set(x_30, 2, x_12);
x_31 = lean_apply_4(x_28, lean_box(0), lean_box(0), x_29, x_30);
return x_31;
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
uint8_t x_33; uint8_t x_34; 
lean_dec(x_13);
x_33 = lean_nat_dec_eq(x_12, x_8);
x_34 = l_Bool_DecidableEq(x_33, x_16);
if (x_34 == 0)
{
lean_dec(x_8);
x_8 = x_12;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_box(0);
x_38 = lean_apply_1(x_5, x_37);
x_39 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_8);
lean_closure_set(x_39, 2, x_6);
x_40 = lean_apply_4(x_36, lean_box(0), lean_box(0), x_38, x_39);
return x_40;
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
uint8_t x_8; uint8_t x_30; uint8_t x_58; uint8_t x_59; uint8_t x_60; 
x_58 = l_Array_isEmpty___rarg(x_6);
x_59 = 1;
x_60 = l_Bool_DecidableEq(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; 
x_61 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_62 = lean_array_get(x_2, x_6, x_61);
lean_inc(x_3);
lean_inc(x_62);
lean_inc(x_7);
x_63 = lean_apply_2(x_3, x_7, x_62);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
x_65 = l_Bool_DecidableEq(x_64, x_59);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
lean_inc(x_3);
lean_inc(x_7);
x_66 = lean_apply_2(x_3, x_62, x_7);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
x_30 = x_59;
goto block_57;
}
else
{
uint8_t x_68; 
x_68 = 0;
x_30 = x_68;
goto block_57;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_62);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
x_70 = lean_box(0);
x_71 = lean_apply_1(x_5, x_70);
x_72 = lean_alloc_closure((void*)(l_Array_binInsertM___rarg___lambda__2), 3, 2);
lean_closure_set(x_72, 0, x_1);
lean_closure_set(x_72, 1, x_6);
x_73 = lean_apply_4(x_69, lean_box(0), lean_box(0), x_71, x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_ctor_get(x_1, 1);
lean_inc(x_74);
x_75 = lean_box(0);
x_76 = lean_apply_1(x_5, x_75);
x_77 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_77, 0, x_1);
lean_closure_set(x_77, 1, x_6);
x_78 = lean_apply_4(x_74, lean_box(0), lean_box(0), x_76, x_77);
return x_78;
}
block_29:
{
uint8_t x_9; uint8_t x_10; 
x_9 = 1;
x_10 = l_Bool_DecidableEq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_get_size(x_6);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_16 = lean_array_get_size(x_6);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_16, x_17);
x_19 = lean_nat_dec_lt(x_18, x_16);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_2(x_21, lean_box(0), x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_array_fget(x_6, x_18);
x_24 = lean_array_fset(x_6, x_18, x_2);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
x_26 = lean_apply_1(x_4, x_23);
x_27 = lean_alloc_closure((void*)(l_Array_modifyM___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_24);
lean_closure_set(x_27, 2, x_18);
x_28 = lean_apply_4(x_25, lean_box(0), lean_box(0), x_26, x_27);
return x_28;
}
}
}
block_57:
{
uint8_t x_31; uint8_t x_32; 
x_31 = 1;
x_32 = l_Bool_DecidableEq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; 
lean_inc(x_2);
x_33 = l_Array_back___rarg(x_2, x_6);
lean_inc(x_3);
lean_inc(x_7);
lean_inc(x_33);
x_34 = lean_apply_2(x_3, x_33, x_7);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
x_36 = l_Bool_DecidableEq(x_35, x_31);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
lean_inc(x_3);
lean_inc(x_7);
x_37 = lean_apply_2(x_3, x_7, x_33);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
x_8 = x_31;
goto block_29;
}
else
{
uint8_t x_39; 
x_39 = 0;
x_8 = x_39;
goto block_29;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_33);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_box(0);
x_42 = lean_apply_1(x_5, x_41);
x_43 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_43, 0, x_1);
lean_closure_set(x_43, 1, x_6);
x_44 = lean_apply_4(x_40, lean_box(0), lean_box(0), x_42, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_45 = lean_array_get_size(x_6);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_lt(x_46, x_45);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_4);
lean_dec(x_2);
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_apply_2(x_49, lean_box(0), x_6);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_array_fget(x_6, x_46);
x_52 = lean_array_fset(x_6, x_46, x_2);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = lean_apply_1(x_4, x_51);
x_55 = lean_alloc_closure((void*)(l_Array_binInsertM___rarg___lambda__1), 3, 2);
lean_closure_set(x_55, 0, x_1);
lean_closure_set(x_55, 1, x_52);
x_56 = lean_apply_4(x_53, lean_box(0), lean_box(0), x_54, x_55);
return x_56;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; 
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
x_14 = 1;
x_15 = l_Bool_DecidableEq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; 
lean_dec(x_7);
lean_inc(x_2);
lean_inc(x_5);
x_16 = lean_apply_2(x_2, x_5, x_11);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
x_18 = l_Bool_DecidableEq(x_17, x_14);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_19 = lean_array_get_size(x_4);
x_20 = lean_nat_dec_lt(x_10, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_array_fset(x_4, x_10, x_1);
x_22 = lean_array_fset(x_21, x_10, x_3);
lean_dec(x_10);
return x_22;
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
uint8_t x_24; uint8_t x_25; 
lean_dec(x_11);
x_24 = lean_nat_dec_eq(x_10, x_6);
x_25 = l_Bool_DecidableEq(x_24, x_14);
if (x_25 == 0)
{
lean_dec(x_6);
x_6 = x_10;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_6, x_27);
lean_dec(x_6);
x_29 = l_Array_insertAt___rarg(x_4, x_28, x_3);
lean_dec(x_28);
return x_29;
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
uint8_t x_6; uint8_t x_21; uint8_t x_38; uint8_t x_39; uint8_t x_40; 
x_38 = l_Array_isEmpty___rarg(x_4);
x_39 = 1;
x_40 = l_Bool_DecidableEq(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; 
x_41 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_42 = lean_array_get(x_1, x_4, x_41);
lean_inc(x_2);
lean_inc(x_42);
lean_inc(x_5);
x_43 = lean_apply_2(x_2, x_5, x_42);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
x_45 = l_Bool_DecidableEq(x_44, x_39);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
lean_inc(x_2);
lean_inc(x_5);
x_46 = lean_apply_2(x_2, x_42, x_5);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
x_21 = x_39;
goto block_37;
}
else
{
uint8_t x_48; 
x_48 = 0;
x_21 = x_48;
goto block_37;
}
}
else
{
lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_49 = l_Array_insertAt___rarg(x_4, x_41, x_3);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_array_push(x_4, x_3);
return x_50;
}
block_20:
{
uint8_t x_7; uint8_t x_8; 
x_7 = 1;
x_8 = l_Bool_DecidableEq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_4);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Init_Data_Array_BinSearch_1__binInsertAux___main___at_Array_binInsert___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_12, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_2);
x_14 = lean_array_get_size(x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_14, x_15);
x_17 = lean_nat_dec_lt(x_16, x_14);
lean_dec(x_14);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_fset(x_4, x_16, x_1);
x_19 = lean_array_fset(x_18, x_16, x_3);
lean_dec(x_16);
return x_19;
}
}
}
block_37:
{
uint8_t x_22; uint8_t x_23; 
x_22 = 1;
x_23 = l_Bool_DecidableEq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; 
lean_inc(x_1);
x_24 = l_Array_back___rarg(x_1, x_4);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_24);
x_25 = lean_apply_2(x_2, x_24, x_5);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
x_27 = l_Bool_DecidableEq(x_26, x_22);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
lean_inc(x_2);
lean_inc(x_5);
x_28 = lean_apply_2(x_2, x_5, x_24);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
x_6 = x_22;
goto block_20;
}
else
{
uint8_t x_30; 
x_30 = 0;
x_6 = x_30;
goto block_20;
}
}
else
{
lean_object* x_31; 
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_array_push(x_4, x_3);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_5);
lean_dec(x_2);
x_32 = lean_array_get_size(x_4);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_32);
lean_dec(x_32);
if (x_34 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_array_fset(x_4, x_33, x_1);
x_36 = lean_array_fset(x_35, x_33, x_3);
return x_36;
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

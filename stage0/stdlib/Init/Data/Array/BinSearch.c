// Lean compiler output
// Module: Init.Data.Array.BinSearch
// Imports: Init.Data.Array.Basic Init.Data.Int.DivMod.Lemmas Init.Omega
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
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Array_binInsert___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchContains(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearch___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsert___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearchContains___spec__1(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearchContains___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at_Array_binSearchContains___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at_Array_binSearchContains___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearch(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Array_binInsert___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearch___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchContains___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearch___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Array_binInsert___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearch___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Array_binInsert___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearch___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearch___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearchContains___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearchContains___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearch___spec__1(lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchContains___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsert(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_insertIdx_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_nat_add(x_5, x_6);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_div(x_8, x_9);
lean_dec(x_8);
x_11 = lean_array_fget(x_3, x_10);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_11);
x_12 = lean_apply_2(x_1, x_11, x_4);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_6);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_4);
x_14 = lean_apply_2(x_1, x_4, x_11);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_17 = lean_apply_1(x_2, x_16);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_11);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_10, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_10, x_20);
lean_dec(x_10);
x_22 = lean_nat_dec_lt(x_21, x_5);
if (x_22 == 0)
{
x_6 = x_21;
x_7 = lean_box(0);
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_apply_1(x_2, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_apply_1(x_2, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_5);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_10, x_28);
lean_dec(x_10);
x_30 = lean_nat_dec_le(x_29, x_6);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_apply_1(x_2, x_31);
return x_32;
}
else
{
x_5 = x_29;
x_7 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_binSearchAux___rarg___boxed), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_binSearchAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearch___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_nat_add(x_4, x_5);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = lean_array_fget(x_2, x_9);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_10);
x_11 = lean_apply_2(x_1, x_10, x_3);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_3);
x_13 = lean_apply_2(x_1, x_3, x_10);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_10);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_10);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_9, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_9, x_18);
lean_dec(x_9);
x_20 = lean_nat_dec_lt(x_19, x_4);
if (x_20 == 0)
{
x_5 = x_19;
x_6 = lean_box(0);
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = lean_box(0);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_9, x_24);
lean_dec(x_9);
x_26 = lean_nat_dec_le(x_25, x_5);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_box(0);
return x_27;
}
else
{
x_4 = x_25;
x_6 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearch___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Array_binSearch___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearch___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_nat_add(x_4, x_5);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = lean_array_fget(x_2, x_9);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_10);
x_11 = lean_apply_2(x_1, x_10, x_3);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_3);
x_13 = lean_apply_2(x_1, x_3, x_10);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_10);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_10);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_9, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_9, x_18);
lean_dec(x_9);
x_20 = lean_nat_dec_lt(x_19, x_4);
if (x_20 == 0)
{
x_5 = x_19;
x_6 = lean_box(0);
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = lean_box(0);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_9, x_24);
lean_dec(x_9);
x_26 = lean_nat_dec_le(x_25, x_5);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_box(0);
return x_27;
}
else
{
x_4 = x_25;
x_6 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearch___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Array_binSearch___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
lean_dec(x_6);
x_12 = lean_nat_dec_le(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Array_binSearchAux___at_Array_binSearch___spec__1___rarg(x_3, x_1, x_2, x_4, x_11, lean_box(0));
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_6);
x_15 = lean_nat_dec_le(x_4, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Array_binSearchAux___at_Array_binSearch___spec__2___rarg(x_3, x_1, x_2, x_4, x_5, lean_box(0));
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearch___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearch___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at_Array_binSearch___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearch___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binSearchAux___at_Array_binSearch___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearch___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binSearch___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at_Array_binSearchContains___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_nat_add(x_4, x_5);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = lean_array_fget(x_2, x_9);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_10);
x_11 = lean_apply_2(x_1, x_10, x_3);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_3);
x_13 = lean_apply_2(x_1, x_3, x_10);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = 1;
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_9, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_9, x_18);
lean_dec(x_9);
x_20 = lean_nat_dec_lt(x_19, x_4);
if (x_20 == 0)
{
x_5 = x_19;
x_6 = lean_box(0);
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = 0;
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = 0;
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_9, x_24);
lean_dec(x_9);
x_26 = lean_nat_dec_le(x_25, x_5);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_27 = 0;
return x_27;
}
else
{
x_4 = x_25;
x_6 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearchContains___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Array_binSearchContains___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at_Array_binSearchContains___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_nat_add(x_4, x_5);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = lean_array_fget(x_2, x_9);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_10);
x_11 = lean_apply_2(x_1, x_10, x_3);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_3);
x_13 = lean_apply_2(x_1, x_3, x_10);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = 1;
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_9, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_9, x_18);
lean_dec(x_9);
x_20 = lean_nat_dec_lt(x_19, x_4);
if (x_20 == 0)
{
x_5 = x_19;
x_6 = lean_box(0);
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = 0;
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = 0;
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_9, x_24);
lean_dec(x_9);
x_26 = lean_nat_dec_le(x_25, x_5);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_27 = 0;
return x_27;
}
else
{
x_4 = x_25;
x_6 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearchContains___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchAux___at_Array_binSearchContains___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchContains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
lean_dec(x_6);
x_12 = lean_nat_dec_le(x_4, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = 0;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = l_Array_binSearchAux___at_Array_binSearchContains___spec__1___rarg(x_3, x_1, x_2, x_4, x_11, lean_box(0));
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_6);
x_15 = lean_nat_dec_le(x_4, x_5);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = 0;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l_Array_binSearchAux___at_Array_binSearchContains___spec__2___rarg(x_3, x_1, x_2, x_4, x_5, lean_box(0));
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchContains(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binSearchContains___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearchContains___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_binSearchAux___at_Array_binSearchContains___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at_Array_binSearchContains___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_binSearchAux___at_Array_binSearchContains___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchContains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_binSearchContains___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_array_fset(x_2, x_3, x_4);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
x_9 = lean_array_get_size(x_3);
x_10 = lean_array_push(x_3, x_4);
x_11 = l_Array_insertIdx_loop___rarg(x_8, x_10, x_9);
lean_dec(x_8);
x_12 = lean_apply_2(x_6, lean_box(0), x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_nat_add(x_7, x_8);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = lean_array_fget(x_5, x_13);
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_14);
x_15 = lean_apply_2(x_2, x_14, x_6);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_14);
lean_inc(x_6);
x_17 = lean_apply_2(x_2, x_6, x_14);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_13, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_apply_2(x_22, lean_box(0), x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_box(0);
x_25 = lean_array_fset(x_5, x_13, x_24);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_apply_1(x_3, x_14);
x_28 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_25);
lean_closure_set(x_28, 2, x_13);
x_29 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_27, x_28);
return x_29;
}
}
else
{
lean_dec(x_14);
x_8 = x_13;
x_9 = lean_box(0);
x_10 = lean_box(0);
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_14);
x_31 = lean_nat_dec_eq(x_13, x_7);
if (x_31 == 0)
{
lean_dec(x_7);
x_7 = x_13;
x_9 = lean_box(0);
x_10 = lean_box(0);
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_box(0);
x_35 = lean_apply_1(x_4, x_34);
x_36 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_36, 0, x_1);
lean_closure_set(x_36, 1, x_7);
lean_closure_set(x_36, 2, x_5);
x_37 = lean_apply_4(x_33, lean_box(0), lean_box(0), x_35, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_binInsertM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_array_push(x_2, x_3);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_array_push(x_2, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_insertIdx_loop___rarg(x_8, x_7, x_3);
x_10 = lean_apply_2(x_6, lean_box(0), x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_5, x_8);
lean_inc(x_2);
lean_inc(x_10);
lean_inc(x_6);
x_11 = lean_apply_2(x_2, x_6, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_10);
x_13 = lean_apply_2(x_2, x_10, x_6);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_nat_dec_lt(x_8, x_7);
lean_dec(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_3);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_apply_2(x_17, lean_box(0), x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_box(0);
x_20 = lean_array_fset(x_5, x_8, x_19);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_apply_1(x_3, x_10);
x_23 = lean_alloc_closure((void*)(l_Array_binInsertM___rarg___lambda__1), 3, 2);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_20);
x_24 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_22, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_10);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_7, x_25);
x_27 = lean_array_fget(x_5, x_26);
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_27);
x_28 = lean_apply_2(x_2, x_27, x_6);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_inc(x_2);
lean_inc(x_27);
lean_inc(x_6);
x_30 = lean_apply_2(x_2, x_6, x_27);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_32 = lean_nat_dec_lt(x_26, x_7);
lean_dec(x_7);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_3);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_apply_2(x_34, lean_box(0), x_5);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_box(0);
x_37 = lean_array_fset(x_5, x_26, x_36);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_apply_1(x_3, x_27);
x_40 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_40, 0, x_1);
lean_closure_set(x_40, 1, x_37);
lean_closure_set(x_40, 2, x_26);
x_41 = lean_apply_4(x_38, lean_box(0), lean_box(0), x_39, x_40);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_27);
lean_dec(x_7);
x_42 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_26, lean_box(0), lean_box(0));
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_box(0);
x_45 = lean_apply_1(x_4, x_44);
x_46 = lean_alloc_closure((void*)(l_Array_binInsertM___rarg___lambda__2), 3, 2);
lean_closure_set(x_46, 0, x_1);
lean_closure_set(x_46, 1, x_5);
x_47 = lean_apply_4(x_43, lean_box(0), lean_box(0), x_45, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
x_49 = lean_box(0);
x_50 = lean_apply_1(x_4, x_49);
x_51 = lean_alloc_closure((void*)(l_Array_binInsertM___rarg___lambda__3), 4, 3);
lean_closure_set(x_51, 0, x_1);
lean_closure_set(x_51, 1, x_5);
lean_closure_set(x_51, 2, x_7);
x_52 = lean_apply_4(x_48, lean_box(0), lean_box(0), x_50, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = lean_box(0);
x_55 = lean_apply_1(x_4, x_54);
x_56 = lean_alloc_closure((void*)(l_Array_binInsertM___rarg___lambda__2), 3, 2);
lean_closure_set(x_56, 0, x_1);
lean_closure_set(x_56, 1, x_5);
x_57 = lean_apply_4(x_53, lean_box(0), lean_box(0), x_55, x_56);
return x_57;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_binInsertM___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Array_binInsert___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_nat_add(x_5, x_6);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
x_12 = lean_array_fget(x_3, x_11);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_12);
x_13 = lean_apply_2(x_1, x_12, x_4);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_6);
lean_inc(x_1);
lean_inc(x_4);
x_15 = lean_apply_2(x_1, x_4, x_12);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = lean_array_get_size(x_3);
x_18 = lean_nat_dec_lt(x_11, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_11);
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_box(0);
x_20 = lean_array_fset(x_3, x_11, x_19);
x_21 = lean_array_fset(x_20, x_11, x_2);
lean_dec(x_11);
return x_21;
}
}
else
{
x_6 = x_11;
x_7 = lean_box(0);
x_8 = lean_box(0);
goto _start;
}
}
else
{
uint8_t x_23; 
lean_dec(x_12);
x_23 = lean_nat_dec_eq(x_11, x_5);
if (x_23 == 0)
{
lean_dec(x_5);
x_5 = x_11;
x_7 = lean_box(0);
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_5, x_25);
lean_dec(x_5);
x_27 = lean_array_get_size(x_3);
x_28 = lean_array_push(x_3, x_2);
x_29 = l_Array_insertIdx_loop___rarg(x_26, x_28, x_27);
lean_dec(x_26);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Array_binInsert___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Array_binInsert___spec__2___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Array_binInsert___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_6);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_4);
x_9 = lean_apply_2(x_1, x_4, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
lean_inc(x_4);
x_11 = lean_apply_2(x_1, x_8, x_4);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
if (x_13 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(0);
x_15 = lean_array_fset(x_3, x_6, x_14);
x_16 = lean_array_fset(x_15, x_6, x_2);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_5, x_17);
x_19 = lean_array_fget(x_3, x_18);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_19);
x_20 = lean_apply_2(x_1, x_19, x_4);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_inc(x_1);
lean_inc(x_4);
x_22 = lean_apply_2(x_1, x_4, x_19);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_4);
lean_dec(x_1);
x_24 = lean_nat_dec_lt(x_18, x_5);
lean_dec(x_5);
if (x_24 == 0)
{
lean_dec(x_18);
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_box(0);
x_26 = lean_array_fset(x_3, x_18, x_25);
x_27 = lean_array_fset(x_26, x_18, x_2);
lean_dec(x_18);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_5);
x_28 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Array_binInsert___spec__2___rarg(x_1, x_2, x_3, x_4, x_6, x_18, lean_box(0), lean_box(0));
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_29 = lean_array_push(x_3, x_2);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_30 = lean_array_push(x_3, x_2);
x_31 = l_Array_insertIdx_loop___rarg(x_6, x_30, x_5);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_32 = lean_array_push(x_3, x_2);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Array_binInsert___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binInsertM___at_Array_binInsert___spec__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_binInsert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_3);
x_4 = l_Array_binInsertM___at_Array_binInsert___spec__1___rarg(x_1, x_3, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_binInsert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_binInsert___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Omega(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_BinSearch(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin, lean_io_mk_world());
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

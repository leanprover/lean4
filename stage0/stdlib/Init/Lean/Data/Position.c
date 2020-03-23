// Lean compiler output
// Module: Init.Lean.Data.Position
// Imports: Init.Data.Nat Init.Data.RBMap Init.Lean.Data.Format
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
lean_object* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Data_Position_3__toPositionAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofString___closed__2;
lean_object* l_Lean_Position_Inhabited;
lean_object* l_Lean_Position_HasToString(lean_object*);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Sigma_HasRepr___rarg___closed__1;
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Position_Inhabited___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_prodHasDecidableLt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatKVMap___closed__1;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Init_Lean_Data_Position_2__toColumnAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofString___closed__1;
extern lean_object* l_Sigma_HasRepr___rarg___closed__2;
lean_object* l_Lean_Position_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Position_Lean_HasFormat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Position_3__toPositionAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_FileMap_toPosition___spec__1___boxed(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Position_3__toPositionAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_Position_Lean_HasFormat___closed__2;
lean_object* l_Lean_FileMap_Inhabited;
lean_object* l___private_Init_Lean_Data_Position_2__toColumnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Position_1__ofStringAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_Position_Lean_HasFormat___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_FileMap_toPosition___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Data_Position_2__toColumnAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Position_DecidableEq___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Position_2__toColumnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_Inhabited___closed__1;
lean_object* l_Lean_Position_lt___closed__1;
lean_object* l___private_Init_Lean_Data_Position_1__ofStringAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Position_DecidableEq(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l_Nat_Inhabited;
lean_object* l___private_Init_Lean_Data_Position_3__toPositionAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_Position_lt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Position_lt___closed__2;
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_String_toFileMap(lean_object*);
uint8_t l_Lean_Position_DecidableEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_nat_dec_eq(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_4, x_6);
return x_9;
}
}
}
lean_object* l_Lean_Position_DecidableEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Position_DecidableEq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Position_lt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decEq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Position_lt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Position_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_inc(x_6);
lean_inc(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Position_lt___closed__1;
x_10 = l_Lean_Position_lt___closed__2;
x_11 = l_prodHasDecidableLt___rarg(x_9, x_9, x_10, x_10, x_7, x_8);
return x_11;
}
}
lean_object* l_Lean_Position_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Position_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Nat_repr(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Position_Lean_HasFormat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Sigma_HasRepr___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Position_Lean_HasFormat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Sigma_HasRepr___rarg___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Position_Lean_HasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_2);
x_5 = 0;
x_6 = l_Lean_Position_Lean_HasFormat___closed__1;
x_7 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_5);
x_8 = l_Lean_formatKVMap___closed__1;
x_9 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_5);
x_10 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_3);
x_11 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_5);
x_12 = l_Lean_Position_Lean_HasFormat___closed__2;
x_13 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_5);
return x_13;
}
}
lean_object* l_Lean_Position_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Nat_repr(x_2);
x_5 = l_Sigma_HasRepr___rarg___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_reprAux___main___rarg___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Nat_repr(x_3);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = l_Sigma_HasRepr___rarg___closed__2;
x_12 = lean_string_append(x_10, x_11);
return x_12;
}
}
lean_object* _init_l_Lean_Position_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Position_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Position_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_FileMap_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_FileMap_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_FileMap_Inhabited___closed__1;
return x_1;
}
}
lean_object* l___private_Init_Lean_Data_Position_1__ofStringAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_2);
if (x_6 == 0)
{
uint32_t x_7; lean_object* x_8; uint32_t x_9; uint8_t x_10; 
x_7 = lean_string_utf8_get(x_1, x_2);
x_8 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_9 = 10;
x_10 = x_7 == x_9;
if (x_10 == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
lean_inc(x_8);
x_14 = lean_array_push(x_4, x_8);
lean_inc(x_13);
x_15 = lean_array_push(x_5, x_13);
x_2 = x_8;
x_3 = x_13;
x_4 = x_14;
x_5 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_push(x_4, x_2);
x_18 = lean_array_push(x_5, x_3);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_Data_Position_1__ofStringAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Data_Position_1__ofStringAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_FileMap_ofString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_FileMap_ofString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_FileMap_ofString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_FileMap_ofString___closed__1;
x_5 = l_Lean_FileMap_ofString___closed__2;
x_6 = l___private_Init_Lean_Data_Position_1__ofStringAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Data_Position_2__toColumnAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_3, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_3 = x_7;
x_4 = x_9;
goto _start;
}
else
{
lean_dec(x_3);
return x_4;
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
lean_object* l___private_Init_Lean_Data_Position_2__toColumnAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Data_Position_2__toColumnAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Data_Position_2__toColumnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Data_Position_2__toColumnAux___main(x_1, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Data_Position_2__toColumnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Data_Position_2__toColumnAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_Data_Position_3__toPositionAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = l_Nat_Inhabited;
x_8 = lean_array_get(x_7, x_2, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
x_11 = lean_nat_dec_eq(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_8);
x_12 = lean_nat_add(x_5, x_6);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_div(x_12, x_13);
lean_dec(x_12);
x_15 = lean_array_get(x_7, x_2, x_14);
x_16 = lean_nat_dec_eq(x_4, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_15, x_4);
lean_dec(x_15);
if (x_17 == 0)
{
lean_dec(x_6);
x_6 = x_14;
goto _start;
}
else
{
lean_dec(x_5);
x_5 = x_14;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_array_get(x_7, x_3, x_14);
lean_dec(x_14);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
x_23 = lean_array_get(x_7, x_3, x_5);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l___private_Init_Lean_Data_Position_2__toColumnAux___main(x_1, x_4, x_8, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
lean_object* l___private_Init_Lean_Data_Position_3__toPositionAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Data_Position_3__toPositionAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Data_Position_3__toPositionAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Data_Position_3__toPositionAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Data_Position_3__toPositionAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Data_Position_3__toPositionAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_back___at_Lean_FileMap_toPosition___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Nat_Inhabited;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_FileMap_toPosition(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_array_get_size(x_4);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_dec_le(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Array_back___at_Lean_FileMap_toPosition___spec__1(x_4);
x_12 = lean_nat_dec_le(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_6, x_15);
lean_dec(x_6);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Init_Lean_Data_Position_3__toPositionAux___main(x_3, x_4, x_5, x_2, x_17, x_16);
lean_dec(x_2);
return x_18;
}
}
}
}
lean_object* l_Array_back___at_Lean_FileMap_toPosition___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_FileMap_toPosition___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_FileMap_toPosition___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_FileMap_toPosition(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_String_toFileMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_FileMap_ofString(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Nat(lean_object*);
lean_object* initialize_Init_Data_RBMap(lean_object*);
lean_object* initialize_Init_Lean_Data_Format(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Data_Position(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RBMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Data_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Position_lt___closed__1 = _init_l_Lean_Position_lt___closed__1();
lean_mark_persistent(l_Lean_Position_lt___closed__1);
l_Lean_Position_lt___closed__2 = _init_l_Lean_Position_lt___closed__2();
lean_mark_persistent(l_Lean_Position_lt___closed__2);
l_Lean_Position_Lean_HasFormat___closed__1 = _init_l_Lean_Position_Lean_HasFormat___closed__1();
lean_mark_persistent(l_Lean_Position_Lean_HasFormat___closed__1);
l_Lean_Position_Lean_HasFormat___closed__2 = _init_l_Lean_Position_Lean_HasFormat___closed__2();
lean_mark_persistent(l_Lean_Position_Lean_HasFormat___closed__2);
l_Lean_Position_Inhabited___closed__1 = _init_l_Lean_Position_Inhabited___closed__1();
lean_mark_persistent(l_Lean_Position_Inhabited___closed__1);
l_Lean_Position_Inhabited = _init_l_Lean_Position_Inhabited();
lean_mark_persistent(l_Lean_Position_Inhabited);
l_Lean_FileMap_Inhabited___closed__1 = _init_l_Lean_FileMap_Inhabited___closed__1();
lean_mark_persistent(l_Lean_FileMap_Inhabited___closed__1);
l_Lean_FileMap_Inhabited = _init_l_Lean_FileMap_Inhabited();
lean_mark_persistent(l_Lean_FileMap_Inhabited);
l_Lean_FileMap_ofString___closed__1 = _init_l_Lean_FileMap_ofString___closed__1();
lean_mark_persistent(l_Lean_FileMap_ofString___closed__1);
l_Lean_FileMap_ofString___closed__2 = _init_l_Lean_FileMap_ofString___closed__2();
lean_mark_persistent(l_Lean_FileMap_ofString___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

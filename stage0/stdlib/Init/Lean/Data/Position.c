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
uint8_t l_prodHasDecidableLt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatKVMap___closed__1;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Init_Lean_Data_Position_2__toColumnAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofString___closed__1;
extern lean_object* l_Sigma_HasRepr___rarg___closed__2;
uint8_t l_Lean_Position_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Position_Lean_HasFormat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Position_3__toPositionAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Position_3__toPositionAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
extern uint8_t l_String_posOfAux___main___closed__2;
lean_object* l_Lean_Position_Lean_HasFormat___closed__2;
extern uint8_t l_String_posOfAux___main___closed__1;
lean_object* l_Lean_FileMap_Inhabited;
lean_object* l___private_Init_Lean_Data_Position_2__toColumnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Position_1__ofStringAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_Position_Lean_HasFormat___closed__1;
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
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
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
uint8_t l_Lean_Position_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
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
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Position_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
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
uint8_t x_6; uint8_t x_7; 
x_6 = lean_string_utf8_at_end(x_1, x_2);
x_7 = l_coeDecidableEq(x_6);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_8 = lean_string_utf8_get(x_1, x_2);
x_9 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_10 = 10;
x_11 = x_8 == x_10;
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_String_posOfAux___main___closed__1;
if (x_12 == 0)
{
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
lean_inc(x_9);
x_16 = lean_array_push(x_4, x_9);
lean_inc(x_15);
x_17 = lean_array_push(x_5, x_15);
x_2 = x_9;
x_3 = x_15;
x_4 = x_16;
x_5 = x_17;
goto _start;
}
}
else
{
uint8_t x_19; 
x_19 = l_String_posOfAux___main___closed__2;
if (x_19 == 0)
{
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
lean_inc(x_9);
x_23 = lean_array_push(x_4, x_9);
lean_inc(x_22);
x_24 = lean_array_push(x_5, x_22);
x_2 = x_9;
x_3 = x_22;
x_4 = x_23;
x_5 = x_24;
goto _start;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_array_push(x_4, x_2);
x_27 = lean_array_push(x_5, x_3);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
return x_28;
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
uint8_t x_6; uint8_t x_7; 
x_6 = lean_string_utf8_at_end(x_1, x_3);
x_7 = l_coeDecidableEq(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_3 = x_8;
x_4 = x_10;
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
uint8_t x_12; 
x_12 = l_String_posOfAux___main___closed__2;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
else
{
lean_dec(x_3);
return x_4;
}
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_7 = l_Nat_Inhabited;
x_8 = lean_array_get(x_7, x_2, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
x_11 = lean_nat_dec_eq(x_6, x_10);
lean_dec(x_10);
x_12 = l_coeDecidableEq(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
lean_dec(x_8);
x_13 = lean_nat_add(x_5, x_6);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_div(x_13, x_14);
lean_dec(x_13);
x_16 = lean_array_get(x_7, x_2, x_15);
x_17 = lean_nat_dec_eq(x_4, x_16);
x_18 = l_coeDecidableEq(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_nat_dec_lt(x_16, x_4);
lean_dec(x_16);
if (x_19 == 0)
{
lean_dec(x_6);
x_6 = x_15;
goto _start;
}
else
{
lean_dec(x_5);
x_5 = x_15;
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
x_22 = lean_array_get(x_7, x_3, x_15);
lean_dec(x_15);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
x_25 = lean_array_get(x_7, x_3, x_5);
lean_dec(x_5);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l___private_Init_Lean_Data_Position_2__toColumnAux___main(x_1, x_4, x_8, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
return x_28;
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
lean_object* l_Lean_FileMap_toPosition(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_array_get_size(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Lean_Data_Position_3__toPositionAux___main(x_3, x_4, x_5, x_2, x_9, x_8);
return x_10;
}
}
lean_object* l_Lean_FileMap_toPosition___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_FileMap_toPosition(x_1, x_2);
lean_dec(x_2);
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

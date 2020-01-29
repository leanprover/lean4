// Lean compiler output
// Module: Init.Lean.Compiler.IR.SimpCase
// Imports: Init.Lean.Compiler.IR.Basic Init.Lean.Compiler.IR.Format
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
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_2__maxOccs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_4__mkSimpCase___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_2__maxOccs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_IR_ensureHasDefault___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_SimpCase_1__getOccsOf(lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_SimpCase_2__maxOccs___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_IR_ensureHasDefault___spec__2(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_SimpCase_2__maxOccs(lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_SimpCase_1__getOccsOf___boxed(lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_beq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_1__getOccsOf___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_IR_ensureHasDefault(lean_object*);
lean_object* l_Array_filterAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_simpCase___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_simpCase(lean_object*);
lean_object* l_Lean_IR_Decl_simpCase(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_flatten(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_simpCase___main(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_ensureHasDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_altInh;
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_1__getOccsOf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_Alt_isDefault(lean_object*);
lean_object* l_Array_back___at_Lean_IR_ensureHasDefault___spec__2___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_SimpCase_4__mkSimpCase(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_IR_ensureHasDefault___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l_Lean_IR_Alt_isDefault(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
return x_8;
}
}
}
}
lean_object* l_Array_back___at_Lean_IR_ensureHasDefault___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_IR_altInh;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_IR_ensureHasDefault(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_anyRangeMAux___main___at_Lean_IR_ensureHasDefault___spec__1(x_1, x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Array_back___at_Lean_IR_ensureHasDefault___spec__2(x_1);
x_8 = lean_array_pop(x_1);
x_9 = l_Lean_IR_AltCore_body(x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_array_push(x_8, x_10);
return x_11;
}
else
{
return x_1;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_ensureHasDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_IR_ensureHasDefault___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_back___at_Lean_IR_ensureHasDefault___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_IR_ensureHasDefault___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_1__getOccsOf___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Lean_IR_AltCore_body(x_8);
lean_dec(x_8);
lean_inc(x_2);
x_10 = l_Lean_IR_FnBody_beq(x_9, x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
if (x_10 == 0)
{
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_4 = x_12;
x_5 = x_14;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_SimpCase_1__getOccsOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_IR_altInh;
x_4 = lean_array_get(x_3, x_1, x_2);
x_5 = l_Lean_IR_AltCore_body(x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_2, x_6);
x_8 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_1__getOccsOf___spec__1(x_1, x_5, x_1, x_7, x_6);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_1__getOccsOf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_1__getOccsOf___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_SimpCase_1__getOccsOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Compiler_IR_SimpCase_1__getOccsOf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_2__maxOccs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l___private_Init_Lean_Compiler_IR_SimpCase_1__getOccsOf(x_1, x_3);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_nat_dec_lt(x_8, x_7);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_array_fget(x_1, x_3);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
x_3 = x_11;
x_4 = x_14;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_SimpCase_2__maxOccs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_IR_altInh;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get(x_2, x_1, x_3);
x_5 = l___private_Init_Lean_Compiler_IR_SimpCase_1__getOccsOf(x_1, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_2__maxOccs___spec__1(x_1, x_1, x_7, x_6);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_2__maxOccs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_2__maxOccs___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_SimpCase_2__maxOccs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Compiler_IR_SimpCase_2__maxOccs(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l_Lean_IR_Alt_isDefault(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
return x_8;
}
}
}
}
lean_object* l_Array_filterAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = l_Array_shrink___main___rarg(x_2, x_4);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_2, x_3);
x_9 = l_Lean_IR_AltCore_body(x_8);
lean_dec(x_8);
x_10 = l_Lean_IR_AltCore_body(x_1);
x_11 = l_Lean_IR_FnBody_beq(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_15 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_3 = x_14;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_fswap(x_2, x_3, x_4);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_20 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
x_2 = x_17;
x_3 = x_19;
x_4 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_3 = x_23;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_le(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault___spec__1(x_1, x_1, x_2, x_5);
lean_dec(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l___private_Init_Lean_Compiler_IR_SimpCase_2__maxOccs(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_nat_dec_eq(x_9, x_3);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Array_filterAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault___spec__2(x_8, x_1, x_5, x_5);
x_12 = l_Lean_IR_AltCore_body(x_8);
lean_dec(x_8);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_array_push(x_11, x_13);
return x_14;
}
else
{
lean_dec(x_8);
return x_1;
}
}
else
{
return x_1;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_filterAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_filterAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_4__mkSimpCase___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_Array_shrink___main___rarg(x_1, x_3);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Lean_IR_AltCore_body(x_7);
lean_dec(x_7);
x_9 = lean_box(13);
x_10 = l_Lean_IR_FnBody_beq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
x_14 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fswap(x_1, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_19 = lean_nat_add(x_3, x_17);
lean_dec(x_3);
x_1 = x_16;
x_2 = x_18;
x_3 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
lean_dec(x_2);
x_2 = x_22;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_SimpCase_4__mkSimpCase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_filterAux___main___at___private_Init_Lean_Compiler_IR_SimpCase_4__mkSimpCase___spec__1(x_4, x_5, x_5);
x_7 = l___private_Init_Lean_Compiler_IR_SimpCase_3__addDefault(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = lean_nat_dec_eq(x_8, x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_8, x_10);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_IR_altInh;
x_14 = lean_array_get(x_13, x_7, x_5);
lean_dec(x_7);
x_15 = l_Lean_IR_AltCore_body(x_14);
lean_dec(x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(13);
return x_16;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_simpCase___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 3);
lean_inc(x_21);
x_22 = l_Lean_IR_FnBody_simpCase___main(x_20);
x_23 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_21);
x_13 = x_23;
goto block_17;
}
else
{
lean_inc(x_7);
x_13 = x_7;
goto block_17;
}
block_17:
{
lean_object* x_14; lean_object* x_15; 
x_14 = x_13;
lean_dec(x_7);
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_15;
goto _start;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
x_15 = l_Lean_IR_FnBody_simpCase___main(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = x_16;
lean_dec(x_7);
x_18 = lean_array_fset(x_10, x_1, x_17);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
x_21 = l_Lean_IR_FnBody_simpCase___main(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = x_22;
lean_dec(x_7);
x_24 = lean_array_fset(x_10, x_1, x_23);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_24;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_FnBody_simpCase___main(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_IR_FnBody_flatten(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_Lean_IR_FnBody_simpCase___main___spec__1(x_5, x_3);
if (lean_obj_tag(x_4) == 10)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Array_umapMAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2(x_5, x_10);
x_12 = l___private_Init_Lean_Compiler_IR_SimpCase_4__mkSimpCase(x_7, x_8, x_9, x_11);
x_13 = l_Lean_IR_reshape(x_6, x_12);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_IR_reshape(x_6, x_4);
return x_14;
}
}
}
lean_object* l_Lean_IR_FnBody_simpCase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_FnBody_simpCase___main(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_Decl_simpCase(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_IR_FnBody_simpCase___main(x_3);
lean_ctor_set(x_1, 3, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = l_Lean_IR_FnBody_simpCase___main(x_8);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_9);
return x_10;
}
}
else
{
return x_1;
}
}
}
lean_object* initialize_Init_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Format(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_SimpCase(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

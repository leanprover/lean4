// Lean compiler output
// Module: Init.Lean.Compiler.NameMangling
// Imports: Init.Lean.Name
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
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_Char_isDigit(uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_appendIndexAfter___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__1;
uint32_t l_Nat_digitChar(lean_object*);
lean_object* l_String_Iterator_next(lean_object*);
lean_object* l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Char_isAlpha(uint32_t);
lean_object* l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__2;
lean_object* l_Lean_String_mangle(lean_object*);
lean_object* l___private_Init_Lean_Compiler_NameMangling_2__Name_mangleAux(lean_object*);
uint32_t l_String_Iterator_curr(lean_object*);
uint8_t l_Char_DecidableEq(uint32_t, uint32_t);
lean_object* lean_name_mangle(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_NameMangling_2__Name_mangleAux___main(lean_object*);
lean_object* _init_l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_u");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_x");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("__");
return x_1;
}
}
lean_object* l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; uint8_t x_57; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_8 = l_String_Iterator_curr(x_2);
x_57 = l_Char_isAlpha(x_8);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = l_Char_isDigit(x_8);
x_9 = x_58;
goto block_56;
}
else
{
uint8_t x_59; 
x_59 = 1;
x_9 = x_59;
goto block_56;
}
block_56:
{
uint8_t x_10; uint8_t x_11; 
x_10 = 1;
x_11 = l_Bool_DecidableEq(x_9, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 95;
x_13 = l_Char_DecidableEq(x_8, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_uint32_to_nat(x_8);
x_15 = lean_unsigned_to_nat(255u);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint32_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; lean_object* x_33; uint32_t x_34; lean_object* x_35; lean_object* x_36; 
x_17 = l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__1;
x_18 = lean_string_append(x_3, x_17);
x_19 = lean_unsigned_to_nat(4096u);
x_20 = lean_nat_div(x_14, x_19);
x_21 = l_Nat_digitChar(x_20);
lean_dec(x_20);
x_22 = lean_string_push(x_18, x_21);
x_23 = lean_nat_mod(x_14, x_19);
lean_dec(x_14);
x_24 = lean_unsigned_to_nat(256u);
x_25 = lean_nat_div(x_23, x_24);
x_26 = l_Nat_digitChar(x_25);
lean_dec(x_25);
x_27 = lean_string_push(x_22, x_26);
x_28 = lean_nat_mod(x_23, x_24);
lean_dec(x_23);
x_29 = lean_unsigned_to_nat(16u);
x_30 = lean_nat_div(x_28, x_29);
x_31 = l_Nat_digitChar(x_30);
lean_dec(x_30);
x_32 = lean_string_push(x_27, x_31);
x_33 = lean_nat_mod(x_28, x_29);
lean_dec(x_28);
x_34 = l_Nat_digitChar(x_33);
lean_dec(x_33);
x_35 = lean_string_push(x_32, x_34);
x_36 = l_String_Iterator_next(x_2);
x_1 = x_7;
x_2 = x_36;
x_3 = x_35;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint32_t x_42; lean_object* x_43; lean_object* x_44; uint32_t x_45; lean_object* x_46; lean_object* x_47; 
x_38 = l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__2;
x_39 = lean_string_append(x_3, x_38);
x_40 = lean_unsigned_to_nat(16u);
x_41 = lean_nat_div(x_14, x_40);
x_42 = l_Nat_digitChar(x_41);
lean_dec(x_41);
x_43 = lean_string_push(x_39, x_42);
x_44 = lean_nat_mod(x_14, x_40);
lean_dec(x_14);
x_45 = l_Nat_digitChar(x_44);
lean_dec(x_44);
x_46 = lean_string_push(x_43, x_45);
x_47 = l_String_Iterator_next(x_2);
x_1 = x_7;
x_2 = x_47;
x_3 = x_46;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = l_String_Iterator_next(x_2);
x_50 = l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__3;
x_51 = lean_string_append(x_3, x_50);
x_1 = x_7;
x_2 = x_49;
x_3 = x_51;
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_String_Iterator_next(x_2);
x_54 = lean_string_push(x_3, x_8);
x_1 = x_7;
x_2 = x_53;
x_3 = x_54;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_String_mangle(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_String_splitAux___main___closed__1;
x_6 = l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main(x_2, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Compiler_NameMangling_2__Name_mangleAux___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_String_splitAux___main___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_String_mangle(x_4);
if (lean_obj_tag(x_3) == 0)
{
return x_5;
}
else
{
lean_object* x_12; 
x_12 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_7 = l___private_Init_Lean_Compiler_NameMangling_2__Name_mangleAux___main(x_3);
x_8 = l_Lean_Name_appendIndexAfter___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_5);
lean_dec(x_5);
return x_10;
}
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l___private_Init_Lean_Compiler_NameMangling_2__Name_mangleAux___main(x_13);
x_16 = l_Lean_Name_appendIndexAfter___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Nat_repr(x_14);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = lean_string_append(x_19, x_16);
return x_20;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_NameMangling_2__Name_mangleAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Compiler_NameMangling_2__Name_mangleAux___main(x_1);
return x_2;
}
}
lean_object* lean_name_mangle(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Compiler_NameMangling_2__Name_mangleAux___main(x_1);
x_4 = lean_string_append(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init_Lean_Name(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_NameMangling(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Name(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__1 = _init_l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__1);
l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__2 = _init_l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__2);
l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__3 = _init_l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Compiler_NameMangling_1__String_mangleAux___main___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

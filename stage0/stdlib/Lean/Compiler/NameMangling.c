// Lean compiler output
// Module: Lean.Compiler.NameMangling
// Imports: Init Lean.Data.Name
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
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_String_Iterator_next(lean_object*);
uint8_t l_Char_isAlpha(uint32_t);
LEAN_EXPORT lean_object* lean_mk_module_initialization_function_name(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2;
uint32_t l_String_Iterator_curr(lean_object*);
static lean_object* l_Lean_mkModuleInitializationFunctionName___closed__1;
uint32_t l_Nat_digitChar(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeatTR_loop___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1;
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__2(lean_object*, lean_object*);
static lean_object* l_String_mangle___closed__1;
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
uint8_t l_Char_isDigit(uint32_t);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_name_mangle(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_String_mangle(lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeatTR_loop___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
x_7 = 48;
x_8 = lean_string_push(x_2, x_7);
x_1 = x_6;
x_2 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = lean_string_push(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_U", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_u", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_x", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("__", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; uint8_t x_67; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_8 = l_String_Iterator_curr(x_2);
x_67 = l_Char_isAlpha(x_8);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = l_Char_isDigit(x_8);
x_9 = x_68;
goto block_66;
}
else
{
uint8_t x_69; 
x_69 = 1;
x_9 = x_69;
goto block_66;
}
block_66:
{
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 95;
x_11 = lean_uint32_dec_eq(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_uint32_to_nat(x_8);
x_13 = lean_unsigned_to_nat(256u);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(65536u);
x_16 = lean_nat_dec_lt(x_12, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1;
x_18 = lean_string_append(x_3, x_17);
x_19 = lean_unsigned_to_nat(16u);
x_20 = l_Nat_toDigits(x_19, x_12);
x_21 = l_List_lengthTRAux___rarg(x_20, x_4);
x_22 = lean_unsigned_to_nat(8u);
x_23 = lean_nat_sub(x_22, x_21);
lean_dec(x_21);
x_24 = l_Nat_repeatTR_loop___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__1(x_23, x_18);
x_25 = l_List_foldl___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__2(x_24, x_20);
x_26 = l_String_Iterator_next(x_2);
x_1 = x_7;
x_2 = x_26;
x_3 = x_25;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint32_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint32_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint32_t x_41; lean_object* x_42; lean_object* x_43; uint32_t x_44; lean_object* x_45; lean_object* x_46; 
x_28 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2;
x_29 = lean_string_append(x_3, x_28);
x_30 = lean_unsigned_to_nat(4096u);
x_31 = lean_nat_div(x_12, x_30);
x_32 = l_Nat_digitChar(x_31);
lean_dec(x_31);
x_33 = lean_string_push(x_29, x_32);
x_34 = lean_nat_mod(x_12, x_30);
lean_dec(x_12);
x_35 = lean_nat_div(x_34, x_13);
x_36 = l_Nat_digitChar(x_35);
lean_dec(x_35);
x_37 = lean_string_push(x_33, x_36);
x_38 = lean_nat_mod(x_34, x_13);
lean_dec(x_34);
x_39 = lean_unsigned_to_nat(16u);
x_40 = lean_nat_div(x_38, x_39);
x_41 = l_Nat_digitChar(x_40);
lean_dec(x_40);
x_42 = lean_string_push(x_37, x_41);
x_43 = lean_nat_mod(x_38, x_39);
lean_dec(x_38);
x_44 = l_Nat_digitChar(x_43);
lean_dec(x_43);
x_45 = lean_string_push(x_42, x_44);
x_46 = l_String_Iterator_next(x_2);
x_1 = x_7;
x_2 = x_46;
x_3 = x_45;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint32_t x_52; lean_object* x_53; lean_object* x_54; uint32_t x_55; lean_object* x_56; lean_object* x_57; 
x_48 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
x_49 = lean_string_append(x_3, x_48);
x_50 = lean_unsigned_to_nat(16u);
x_51 = lean_nat_div(x_12, x_50);
x_52 = l_Nat_digitChar(x_51);
lean_dec(x_51);
x_53 = lean_string_push(x_49, x_52);
x_54 = lean_nat_mod(x_12, x_50);
lean_dec(x_12);
x_55 = l_Nat_digitChar(x_54);
lean_dec(x_54);
x_56 = lean_string_push(x_53, x_55);
x_57 = l_String_Iterator_next(x_2);
x_1 = x_7;
x_2 = x_57;
x_3 = x_56;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = l_String_Iterator_next(x_2);
x_60 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4;
x_61 = lean_string_append(x_3, x_60);
x_1 = x_7;
x_2 = x_59;
x_3 = x_61;
goto _start;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_String_Iterator_next(x_2);
x_64 = lean_string_push(x_3, x_8);
x_1 = x_7;
x_2 = x_63;
x_3 = x_64;
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
static lean_object* _init_l_String_mangle___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_mangle(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_String_mangle___closed__1;
x_6 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(x_2, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_String_mangle___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_String_mangle(x_4);
if (lean_obj_tag(x_3) == 0)
{
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_3);
x_7 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_string_append(x_8, x_5);
lean_dec(x_5);
return x_9;
}
}
default: 
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_10);
x_13 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Nat_repr(x_11);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_16, x_13);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* lean_name_mangle(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_1);
x_4 = lean_string_append(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_mkModuleInitializationFunctionName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initialize_", 11);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_mk_module_initialization_function_name(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_String_mangle___closed__1;
x_3 = lean_name_mangle(x_1, x_2);
x_4 = l_Lean_mkModuleInitializationFunctionName___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Name(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_NameMangling(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1 = _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1);
l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2 = _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2);
l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3 = _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3);
l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4 = _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4);
l_String_mangle___closed__1 = _init_l_String_mangle___closed__1();
lean_mark_persistent(l_String_mangle___closed__1);
l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1);
l_Lean_mkModuleInitializationFunctionName___closed__1 = _init_l_Lean_mkModuleInitializationFunctionName___closed__1();
lean_mark_persistent(l_Lean_mkModuleInitializationFunctionName___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

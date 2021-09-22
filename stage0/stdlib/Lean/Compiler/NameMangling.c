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
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
uint8_t l_Char_isDigit(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
LEAN_EXPORT lean_object* l_String_mangle(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeat_loop___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__1(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_mkModuleInitializationFunctionName___closed__1;
uint32_t l_Nat_digitChar(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__2(lean_object*, lean_object*);
lean_object* l_String_Iterator_next(lean_object*);
uint8_t l_Char_isAlpha(uint32_t);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* lean_mk_module_initialization_function_name(lean_object*);
uint32_t l_String_Iterator_curr(lean_object*);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object*);
LEAN_EXPORT lean_object* lean_name_mangle(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l_String_mangle___closed__1;
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2;
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1;
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeat_loop___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_1 = lean_mk_string("_U");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_u");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_x");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("__");
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
lean_object* x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_8 = l_String_Iterator_curr(x_2);
x_9 = l_Char_isAlpha(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Char_isDigit(x_8);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 95;
x_12 = x_8 == x_11;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_uint32_to_nat(x_8);
x_14 = lean_unsigned_to_nat(256u);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(65536u);
x_17 = lean_nat_dec_lt(x_13, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1;
x_19 = lean_string_append(x_3, x_18);
x_20 = lean_unsigned_to_nat(16u);
x_21 = l_Nat_toDigits(x_20, x_13);
x_22 = l_List_lengthTRAux___rarg(x_21, x_4);
x_23 = lean_unsigned_to_nat(8u);
x_24 = lean_nat_sub(x_23, x_22);
lean_dec(x_22);
x_25 = l_Nat_repeat_loop___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__1(x_24, x_19);
x_26 = l_List_foldl___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__2(x_25, x_21);
x_27 = l_String_Iterator_next(x_2);
x_1 = x_7;
x_2 = x_27;
x_3 = x_26;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint32_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint32_t x_42; lean_object* x_43; lean_object* x_44; uint32_t x_45; lean_object* x_46; lean_object* x_47; 
x_29 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2;
x_30 = lean_string_append(x_3, x_29);
x_31 = lean_unsigned_to_nat(4096u);
x_32 = lean_nat_div(x_13, x_31);
x_33 = l_Nat_digitChar(x_32);
lean_dec(x_32);
x_34 = lean_string_push(x_30, x_33);
x_35 = lean_nat_mod(x_13, x_31);
lean_dec(x_13);
x_36 = lean_nat_div(x_35, x_14);
x_37 = l_Nat_digitChar(x_36);
lean_dec(x_36);
x_38 = lean_string_push(x_34, x_37);
x_39 = lean_nat_mod(x_35, x_14);
lean_dec(x_35);
x_40 = lean_unsigned_to_nat(16u);
x_41 = lean_nat_div(x_39, x_40);
x_42 = l_Nat_digitChar(x_41);
lean_dec(x_41);
x_43 = lean_string_push(x_38, x_42);
x_44 = lean_nat_mod(x_39, x_40);
lean_dec(x_39);
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
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint32_t x_53; lean_object* x_54; lean_object* x_55; uint32_t x_56; lean_object* x_57; lean_object* x_58; 
x_49 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
x_50 = lean_string_append(x_3, x_49);
x_51 = lean_unsigned_to_nat(16u);
x_52 = lean_nat_div(x_13, x_51);
x_53 = l_Nat_digitChar(x_52);
lean_dec(x_52);
x_54 = lean_string_push(x_50, x_53);
x_55 = lean_nat_mod(x_13, x_51);
lean_dec(x_13);
x_56 = l_Nat_digitChar(x_55);
lean_dec(x_55);
x_57 = lean_string_push(x_54, x_56);
x_58 = l_String_Iterator_next(x_2);
x_1 = x_7;
x_2 = x_58;
x_3 = x_57;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = l_String_Iterator_next(x_2);
x_61 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4;
x_62 = lean_string_append(x_3, x_61);
x_1 = x_7;
x_2 = x_60;
x_3 = x_62;
goto _start;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_String_Iterator_next(x_2);
x_65 = lean_string_push(x_3, x_8);
x_1 = x_7;
x_2 = x_64;
x_3 = x_65;
goto _start;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_String_Iterator_next(x_2);
x_68 = lean_string_push(x_3, x_8);
x_1 = x_7;
x_2 = x_67;
x_3 = x_68;
goto _start;
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
x_1 = lean_mk_string("");
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
x_1 = lean_mk_string("_");
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
x_1 = lean_mk_string("initialize_");
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Name(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_NameMangling(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(lean_io_mk_world());
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

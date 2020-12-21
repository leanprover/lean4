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
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Char_isDigit(uint32_t);
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux_match__1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_mkModuleInitializationFunctionName___closed__1;
uint32_t l_Nat_digitChar(lean_object*);
lean_object* l_String_Iterator_next(lean_object*);
uint8_t l_Char_isAlpha(uint32_t);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_String_mangle(lean_object*);
lean_object* lean_mk_module_initialization_function_name(lean_object*);
uint32_t l_String_Iterator_curr(lean_object*);
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__2;
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux_match__2(lean_object*);
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object*);
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__1;
lean_object* lean_name_mangle(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__3;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux_match__1(lean_object*);
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11811____closed__19;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_apply_3(x_5, x_9, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = lean_apply_2(x_4, x_2, x_3);
return x_11;
}
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux_match__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux_match__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_u");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_x");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("__");
return x_1;
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = lean_unsigned_to_nat(255u);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; lean_object* x_34; lean_object* x_35; 
x_16 = l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__1;
x_17 = lean_string_append(x_3, x_16);
x_18 = lean_unsigned_to_nat(4096u);
x_19 = lean_nat_div(x_13, x_18);
x_20 = l_Nat_digitChar(x_19);
lean_dec(x_19);
x_21 = lean_string_push(x_17, x_20);
x_22 = lean_nat_mod(x_13, x_18);
lean_dec(x_13);
x_23 = lean_unsigned_to_nat(256u);
x_24 = lean_nat_div(x_22, x_23);
x_25 = l_Nat_digitChar(x_24);
lean_dec(x_24);
x_26 = lean_string_push(x_21, x_25);
x_27 = lean_nat_mod(x_22, x_23);
lean_dec(x_22);
x_28 = lean_unsigned_to_nat(16u);
x_29 = lean_nat_div(x_27, x_28);
x_30 = l_Nat_digitChar(x_29);
lean_dec(x_29);
x_31 = lean_string_push(x_26, x_30);
x_32 = lean_nat_mod(x_27, x_28);
lean_dec(x_27);
x_33 = l_Nat_digitChar(x_32);
lean_dec(x_32);
x_34 = lean_string_push(x_31, x_33);
x_35 = l_String_Iterator_next(x_2);
x_1 = x_7;
x_2 = x_35;
x_3 = x_34;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint32_t x_41; lean_object* x_42; lean_object* x_43; uint32_t x_44; lean_object* x_45; lean_object* x_46; 
x_37 = l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__2;
x_38 = lean_string_append(x_3, x_37);
x_39 = lean_unsigned_to_nat(16u);
x_40 = lean_nat_div(x_13, x_39);
x_41 = l_Nat_digitChar(x_40);
lean_dec(x_40);
x_42 = lean_string_push(x_38, x_41);
x_43 = lean_nat_mod(x_13, x_39);
lean_dec(x_13);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = l_String_Iterator_next(x_2);
x_49 = l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__3;
x_50 = lean_string_append(x_3, x_49);
x_1 = x_7;
x_2 = x_48;
x_3 = x_50;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_String_Iterator_next(x_2);
x_53 = lean_string_push(x_3, x_8);
x_1 = x_7;
x_2 = x_52;
x_3 = x_53;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_String_Iterator_next(x_2);
x_56 = lean_string_push(x_3, x_8);
x_1 = x_7;
x_2 = x_55;
x_3 = x_56;
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
lean_object* l_Lean_String_mangle(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_instInhabitedParserDescr___closed__1;
x_6 = l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux(x_2, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_3(x_3, x_7, x_8, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_15 = lean_box_usize(x_14);
x_16 = lean_apply_3(x_4, x_12, x_13, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux_match__2___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
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
x_5 = l_Lean_String_mangle(x_4);
if (lean_obj_tag(x_3) == 0)
{
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_3);
x_7 = l_myMacro____x40_Init_Notation___hyg_11811____closed__19;
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
x_13 = l_myMacro____x40_Init_Notation___hyg_11811____closed__19;
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
lean_object* lean_name_mangle(lean_object* x_1, lean_object* x_2) {
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
lean_object* lean_mk_module_initialization_function_name(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
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
lean_object* initialize_Lean_Compiler_NameMangling(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__1);
l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__2 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__2);
l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__3 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_String_mangleAux___closed__3);
l_Lean_mkModuleInitializationFunctionName___closed__1 = _init_l_Lean_mkModuleInitializationFunctionName___closed__1();
lean_mark_persistent(l_Lean_mkModuleInitializationFunctionName___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

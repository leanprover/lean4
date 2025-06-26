// Lean compiler output
// Module: Lean.Compiler.NameMangling
// Imports: Lean.Data.Name
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
lean_object* l_List_lengthTR___redArg(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_module_initialization_function_name(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2;
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lean_mkModuleInitializationFunctionName___closed__0;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint32_t l_Nat_digitChar(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1;
static lean_object* l_String_mangle___closed__0;
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0;
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeatTR_loop___at_____private_Lean_Compiler_NameMangling_0__String_mangleAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lean_Compiler_NameMangling_0__String_mangleAux_spec__1(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0;
LEAN_EXPORT lean_object* lean_name_mangle(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mangle(lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeatTR_loop___at_____private_Lean_Compiler_NameMangling_0__String_mangleAux_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 1)
{
lean_dec(x_1);
return x_2;
}
else
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
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lean_Compiler_NameMangling_0__String_mangleAux_spec__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_U", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_u", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_x", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("__", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint8_t x_17; uint8_t x_80; uint8_t x_86; uint32_t x_92; uint8_t x_93; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_8 = x_2;
} else {
 lean_dec_ref(x_2);
 x_8 = lean_box(0);
}
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_1, x_9);
lean_dec(x_1);
x_11 = lean_string_utf8_get(x_6, x_7);
x_92 = 65;
x_93 = lean_uint32_dec_le(x_92, x_11);
if (x_93 == 0)
{
x_86 = x_93;
goto block_91;
}
else
{
uint32_t x_94; uint8_t x_95; 
x_94 = 90;
x_95 = lean_uint32_dec_le(x_11, x_94);
x_86 = x_95;
goto block_91;
}
block_16:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
if (lean_is_scalar(x_8)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_8;
}
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_string_push(x_3, x_11);
x_1 = x_10;
x_2 = x_13;
x_3 = x_14;
goto _start;
}
block_79:
{
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
lean_dec(x_8);
x_18 = 95;
x_19 = lean_uint32_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_uint32_to_nat(x_11);
x_21 = lean_unsigned_to_nat(256u);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_unsigned_to_nat(65536u);
x_24 = lean_nat_dec_lt(x_20, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0;
x_26 = lean_string_append(x_3, x_25);
x_27 = lean_unsigned_to_nat(16u);
x_28 = l_Nat_toDigits(x_27, x_20);
x_29 = lean_unsigned_to_nat(8u);
x_30 = l_List_lengthTR___redArg(x_28);
x_31 = lean_nat_sub(x_29, x_30);
lean_dec(x_30);
x_32 = l_Nat_repeatTR_loop___at_____private_Lean_Compiler_NameMangling_0__String_mangleAux_spec__0(x_31, x_26);
x_33 = l_List_foldl___at_____private_Lean_Compiler_NameMangling_0__String_mangleAux_spec__1(x_32, x_28);
x_34 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_6);
lean_ctor_set(x_35, 1, x_34);
x_1 = x_10;
x_2 = x_35;
x_3 = x_33;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint32_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint32_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint32_t x_53; lean_object* x_54; lean_object* x_55; uint32_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_37 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1;
x_38 = lean_string_append(x_3, x_37);
x_39 = lean_unsigned_to_nat(4096u);
x_40 = lean_unsigned_to_nat(12u);
x_41 = lean_nat_shiftr(x_20, x_40);
x_42 = l_Nat_digitChar(x_41);
lean_dec(x_41);
x_43 = lean_string_push(x_38, x_42);
x_44 = lean_nat_mod(x_20, x_39);
lean_dec(x_20);
x_45 = lean_unsigned_to_nat(8u);
x_46 = lean_nat_shiftr(x_44, x_45);
x_47 = l_Nat_digitChar(x_46);
lean_dec(x_46);
x_48 = lean_string_push(x_43, x_47);
x_49 = lean_nat_mod(x_44, x_21);
lean_dec(x_44);
x_50 = lean_unsigned_to_nat(16u);
x_51 = lean_unsigned_to_nat(4u);
x_52 = lean_nat_shiftr(x_49, x_51);
x_53 = l_Nat_digitChar(x_52);
lean_dec(x_52);
x_54 = lean_string_push(x_48, x_53);
x_55 = lean_nat_mod(x_49, x_50);
lean_dec(x_49);
x_56 = l_Nat_digitChar(x_55);
lean_dec(x_55);
x_57 = lean_string_push(x_54, x_56);
x_58 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_6);
lean_ctor_set(x_59, 1, x_58);
x_1 = x_10;
x_2 = x_59;
x_3 = x_57;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint32_t x_66; lean_object* x_67; lean_object* x_68; uint32_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_61 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2;
x_62 = lean_string_append(x_3, x_61);
x_63 = lean_unsigned_to_nat(16u);
x_64 = lean_unsigned_to_nat(4u);
x_65 = lean_nat_shiftr(x_20, x_64);
x_66 = l_Nat_digitChar(x_65);
lean_dec(x_65);
x_67 = lean_string_push(x_62, x_66);
x_68 = lean_nat_mod(x_20, x_63);
lean_dec(x_20);
x_69 = l_Nat_digitChar(x_68);
lean_dec(x_68);
x_70 = lean_string_push(x_67, x_69);
x_71 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_6);
lean_ctor_set(x_72, 1, x_71);
x_1 = x_10;
x_2 = x_72;
x_3 = x_70;
goto _start;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_6);
lean_ctor_set(x_75, 1, x_74);
x_76 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
x_77 = lean_string_append(x_3, x_76);
x_1 = x_10;
x_2 = x_75;
x_3 = x_77;
goto _start;
}
}
else
{
goto block_16;
}
}
block_85:
{
if (x_80 == 0)
{
uint32_t x_81; uint8_t x_82; 
x_81 = 48;
x_82 = lean_uint32_dec_le(x_81, x_11);
if (x_82 == 0)
{
x_17 = x_82;
goto block_79;
}
else
{
uint32_t x_83; uint8_t x_84; 
x_83 = 57;
x_84 = lean_uint32_dec_le(x_11, x_83);
x_17 = x_84;
goto block_79;
}
}
else
{
goto block_16;
}
}
block_91:
{
if (x_86 == 0)
{
uint32_t x_87; uint8_t x_88; 
x_87 = 97;
x_88 = lean_uint32_dec_le(x_87, x_11);
if (x_88 == 0)
{
x_80 = x_88;
goto block_85;
}
else
{
uint32_t x_89; uint8_t x_90; 
x_89 = 122;
x_90 = lean_uint32_dec_le(x_11, x_89);
x_80 = x_90;
goto block_85;
}
}
else
{
goto block_16;
}
}
}
}
}
static lean_object* _init_l_String_mangle___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
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
x_5 = l_String_mangle___closed__0;
x_6 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(x_2, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
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
x_2 = l_String_mangle___closed__0;
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
x_7 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0;
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
x_13 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Nat_reprFast(x_11);
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
static lean_object* _init_l_Lean_mkModuleInitializationFunctionName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initialize_", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_mk_module_initialization_function_name(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_mkModuleInitializationFunctionName___closed__0;
x_3 = l_String_mangle___closed__0;
x_4 = lean_name_mangle(x_1, x_3);
x_5 = lean_string_append(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* initialize_Lean_Data_Name(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_NameMangling(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0 = _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0);
l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1 = _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1);
l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2 = _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2);
l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3 = _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3);
l_String_mangle___closed__0 = _init_l_String_mangle___closed__0();
lean_mark_persistent(l_String_mangle___closed__0);
l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0);
l_Lean_mkModuleInitializationFunctionName___closed__0 = _init_l_Lean_mkModuleInitializationFunctionName___closed__0();
lean_mark_persistent(l_Lean_mkModuleInitializationFunctionName___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lean.Compiler.NameMangling
// Imports: public import Init.Prelude import Init.Data.String.Basic
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
uint8_t l_exists__prop__decidable___redArg(uint8_t, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l___private_Lean_Compiler_NameMangling_0__String_digitChar(uint32_t, lean_object*);
uint32_t lean_uint32_shift_right(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* lean_mk_module_initialization_function_name(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_ValidPos_remainingBytes(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg___boxed(lean_object*);
LEAN_EXPORT uint32_t l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(uint32_t);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkModuleInitializationFunctionName___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_digitChar___boxed(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_ValidPos_remainingBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_String_mangle___closed__0;
static lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2;
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_next___redArg(lean_object*, lean_object*);
uint32_t lean_uint32_sub(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
uint32_t lean_uint32_land(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0;
LEAN_EXPORT lean_object* l_Lean_Name_demangle(lean_object*);
LEAN_EXPORT lean_object* lean_name_mangle(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex(lean_object*, uint32_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mangle(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__0(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 10;
x_3 = lean_uint32_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint32_t x_5; 
x_4 = 87;
x_5 = lean_uint32_add(x_1, x_4);
return x_5;
}
else
{
uint32_t x_6; uint32_t x_7; 
x_6 = 48;
x_7 = lean_uint32_add(x_1, x_6);
return x_7;
}
}
}
LEAN_EXPORT uint32_t l___private_Lean_Compiler_NameMangling_0__String_digitChar(uint32_t x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; 
x_3 = l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_digitChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Compiler_NameMangling_0__String_digitChar(x_3, x_2);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; uint32_t x_8; uint32_t x_9; uint32_t x_10; uint32_t x_11; uint32_t x_12; uint32_t x_13; uint32_t x_14; lean_object* x_15; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_8 = lean_uint32_of_nat(x_7);
x_9 = 2;
x_10 = lean_uint32_shift_left(x_8, x_9);
x_11 = lean_uint32_shift_right(x_2, x_10);
x_12 = 15;
x_13 = lean_uint32_land(x_11, x_12);
x_14 = l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(x_13);
x_15 = lean_string_push(x_3, x_14);
x_1 = x_7;
x_3 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Compiler_NameMangling_0__String_pushHex(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_ValidPos_remainingBytes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_nat_sub(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_ValidPos_remainingBytes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_NameMangling_0__String_ValidPos_remainingBytes(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
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
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_13; uint8_t x_40; uint8_t x_46; uint32_t x_52; uint8_t x_53; 
x_6 = lean_string_utf8_get(x_1, x_2);
x_7 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_4);
x_9 = l_String_Slice_Pos_next___redArg(x_8, x_2);
lean_dec(x_2);
lean_dec_ref(x_8);
x_52 = 65;
x_53 = lean_uint32_dec_le(x_52, x_6);
if (x_53 == 0)
{
x_46 = x_53;
goto block_51;
}
else
{
uint32_t x_54; uint8_t x_55; 
x_54 = 90;
x_55 = lean_uint32_dec_le(x_6, x_54);
x_46 = x_55;
goto block_51;
}
block_12:
{
lean_object* x_10; 
x_10 = lean_string_push(x_3, x_6);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
block_39:
{
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 95;
x_15 = lean_uint32_dec_eq(x_6, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_uint32_to_nat(x_6);
x_17 = lean_unsigned_to_nat(256u);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(65536u);
x_20 = lean_nat_dec_lt(x_16, x_19);
lean_dec(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_unsigned_to_nat(8u);
x_22 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0;
x_23 = lean_string_append(x_3, x_22);
x_24 = l___private_Lean_Compiler_NameMangling_0__String_pushHex(x_21, x_6, x_23);
x_2 = x_9;
x_3 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_unsigned_to_nat(4u);
x_27 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1;
x_28 = lean_string_append(x_3, x_27);
x_29 = l___private_Lean_Compiler_NameMangling_0__String_pushHex(x_26, x_6, x_28);
x_2 = x_9;
x_3 = x_29;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
x_31 = lean_unsigned_to_nat(2u);
x_32 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2;
x_33 = lean_string_append(x_3, x_32);
x_34 = l___private_Lean_Compiler_NameMangling_0__String_pushHex(x_31, x_6, x_33);
x_2 = x_9;
x_3 = x_34;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
x_37 = lean_string_append(x_3, x_36);
x_2 = x_9;
x_3 = x_37;
goto _start;
}
}
else
{
goto block_12;
}
}
block_45:
{
if (x_40 == 0)
{
uint32_t x_41; uint8_t x_42; 
x_41 = 48;
x_42 = lean_uint32_dec_le(x_41, x_6);
if (x_42 == 0)
{
x_13 = x_42;
goto block_39;
}
else
{
uint32_t x_43; uint8_t x_44; 
x_43 = 57;
x_44 = lean_uint32_dec_le(x_6, x_43);
x_13 = x_44;
goto block_39;
}
}
else
{
goto block_12;
}
}
block_51:
{
if (x_46 == 0)
{
uint32_t x_47; uint8_t x_48; 
x_47 = 97;
x_48 = lean_uint32_dec_le(x_47, x_6);
if (x_48 == 0)
{
x_40 = x_48;
goto block_45;
}
else
{
uint32_t x_49; uint8_t x_50; 
x_49 = 122;
x_50 = lean_uint32_dec_le(x_6, x_49);
x_40 = x_50;
goto block_45;
}
}
else
{
goto block_12;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_String_mangle___closed__0;
x_4 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_string_utf8_byte_size(x_2);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; uint32_t x_16; uint8_t x_17; uint32_t x_23; uint8_t x_24; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
lean_dec(x_1);
x_16 = lean_string_utf8_get(x_2, x_3);
x_23 = 48;
x_24 = lean_uint32_dec_le(x_23, x_16);
if (x_24 == 0)
{
x_17 = x_24;
goto block_22;
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = 57;
x_26 = lean_uint32_dec_le(x_16, x_25);
x_17 = x_26;
goto block_22;
}
block_13:
{
lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_6);
x_11 = l_String_Slice_Pos_next___redArg(x_10, x_3);
lean_dec(x_3);
lean_dec_ref(x_10);
x_1 = x_9;
x_3 = x_11;
goto _start;
}
block_15:
{
if (x_14 == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
else
{
goto block_13;
}
}
block_22:
{
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = 97;
x_19 = lean_uint32_dec_le(x_18, x_16);
if (x_19 == 0)
{
x_14 = x_19;
goto block_15;
}
else
{
uint32_t x_20; uint8_t x_21; 
x_20 = 102;
x_21 = lean_uint32_dec_le(x_16, x_20);
x_14 = x_21;
goto block_15;
}
}
else
{
goto block_13;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 1)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_apply_2(x_4, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_1, x_9);
x_11 = lean_apply_3(x_5, x_10, x_2, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 1)
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint32_t x_29; uint8_t x_30; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
lean_dec(x_1);
x_9 = lean_string_utf8_get(x_2, x_3);
x_10 = lean_string_utf8_byte_size(x_2);
lean_inc_ref(x_2);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_String_Slice_Pos_next___redArg(x_11, x_3);
lean_dec(x_3);
lean_dec_ref(x_11);
x_29 = 48;
x_30 = lean_uint32_dec_le(x_29, x_9);
if (x_30 == 0)
{
x_13 = x_30;
goto block_28;
}
else
{
uint32_t x_31; uint8_t x_32; 
x_31 = 57;
x_32 = lean_uint32_dec_le(x_9, x_31);
x_13 = x_32;
goto block_28;
}
block_28:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint32_t x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_nat_shiftl(x_4, x_14);
lean_dec(x_4);
x_16 = 87;
x_17 = lean_uint32_sub(x_9, x_16);
x_18 = lean_uint32_to_nat(x_17);
x_19 = lean_nat_lor(x_15, x_18);
lean_dec(x_18);
lean_dec(x_15);
x_1 = x_8;
x_3 = x_12;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; uint32_t x_23; uint32_t x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_unsigned_to_nat(4u);
x_22 = lean_nat_shiftl(x_4, x_21);
lean_dec(x_4);
x_23 = 48;
x_24 = lean_uint32_sub(x_9, x_23);
x_25 = lean_uint32_to_nat(x_24);
x_26 = lean_nat_lor(x_22, x_25);
lean_dec(x_25);
lean_dec(x_22);
x_1 = x_8;
x_3 = x_12;
x_4 = x_26;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_nat_dec_eq(x_2, x_3);
x_5 = l_instDecidableNot___redArg(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_6 = 1;
return x_6;
}
else
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get(x_1, x_2);
x_8 = 95;
x_9 = lean_uint32_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 120;
x_11 = lean_uint32_dec_eq(x_7, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 117;
x_13 = lean_uint32_dec_eq(x_7, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 85;
x_15 = lean_uint32_dec_eq(x_7, x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_16 = 48;
x_17 = lean_uint32_dec_le(x_16, x_7);
if (x_17 == 0)
{
return x_17;
}
else
{
uint32_t x_18; uint8_t x_19; 
x_18 = 57;
x_19 = lean_uint32_dec_le(x_7, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_unsigned_to_nat(8u);
x_21 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_1);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_3);
x_23 = l_String_Slice_Pos_next___redArg(x_22, x_2);
lean_dec(x_2);
lean_dec_ref(x_22);
x_24 = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(x_20, x_1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_unsigned_to_nat(4u);
x_26 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_1);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_3);
x_28 = l_String_Slice_Pos_next___redArg(x_27, x_2);
lean_dec(x_2);
lean_dec_ref(x_27);
x_29 = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(x_25, x_1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_1);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_3);
x_33 = l_String_Slice_Pos_next___redArg(x_32, x_2);
lean_dec(x_2);
lean_dec_ref(x_32);
x_34 = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(x_30, x_1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_1);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_3);
x_37 = l_String_Slice_Pos_next___redArg(x_36, x_2);
lean_dec(x_2);
lean_dec_ref(x_36);
x_2 = x_37;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = l_String_Slice_Pos_prevAux_go___redArg(x_5, x_7);
lean_dec_ref(x_5);
x_9 = lean_string_utf8_get(x_1, x_8);
lean_dec(x_8);
lean_dec_ref(x_1);
x_10 = 95;
x_11 = lean_uint32_dec_eq(x_9, x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_string_utf8_byte_size(x_6);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___lam__0___boxed), 3, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_7, x_9);
lean_dec(x_7);
x_11 = l_instDecidableNot___redArg(x_10);
x_12 = l_exists__prop__decidable___redArg(x_11, x_8);
if (x_12 == 0)
{
goto block_5;
}
else
{
lean_dec_ref(x_2);
return x_12;
}
}
else
{
lean_dec(x_1);
goto block_5;
}
block_5:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(x_2, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("00", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_00", 3, 3);
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
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = l_String_mangle(x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_5);
x_7 = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(x_5, x_6);
if (x_7 == 0)
{
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0;
x_9 = lean_string_append(x_8, x_5);
lean_dec_ref(x_5);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_15; 
lean_inc(x_3);
x_10 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_3);
lean_inc_ref(x_5);
x_15 = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(x_3, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
x_11 = x_16;
goto block_14;
}
else
{
lean_object* x_17; 
x_17 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2;
x_11 = x_17;
goto block_14;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = lean_string_append(x_12, x_5);
lean_dec_ref(x_5);
return x_13;
}
}
}
default: 
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec_ref(x_1);
x_20 = l_Nat_reprFast(x_19);
x_21 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
x_22 = lean_string_append(x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_18);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec_ref(x_1);
x_24 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_18);
x_25 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Nat_reprFast(x_23);
x_28 = lean_string_append(x_26, x_27);
lean_dec_ref(x_27);
x_29 = lean_string_append(x_28, x_25);
return x_29;
}
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
lean_dec_ref(x_3);
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
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint32_t x_24; uint8_t x_25; 
x_7 = lean_string_utf8_get(x_1, x_2);
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
lean_inc_ref(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_5);
x_10 = l_String_Slice_Pos_next___redArg(x_9, x_2);
lean_dec(x_2);
x_24 = 48;
x_25 = lean_uint32_dec_le(x_24, x_7);
if (x_25 == 0)
{
x_11 = x_25;
goto block_23;
}
else
{
uint32_t x_26; uint8_t x_27; 
x_26 = 57;
x_27 = lean_uint32_dec_le(x_7, x_26);
x_11 = x_27;
goto block_23;
}
block_23:
{
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Name_num___override(x_3, x_4);
x_13 = lean_nat_dec_eq(x_10, x_5);
lean_dec(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_String_Slice_Pos_next___redArg(x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
x_15 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(x_1, x_14, x_12);
lean_dec(x_14);
return x_15;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
return x_12;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint32_t x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_9);
lean_dec(x_5);
x_16 = lean_unsigned_to_nat(10u);
x_17 = lean_nat_mul(x_4, x_16);
lean_dec(x_4);
x_18 = 48;
x_19 = lean_uint32_sub(x_7, x_18);
x_20 = lean_uint32_to_nat(x_19);
x_21 = lean_nat_add(x_17, x_20);
lean_dec(x_20);
lean_dec(x_17);
x_2 = x_10;
x_4 = x_21;
goto _start;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_28 = l_Lean_Name_num___override(x_3, x_4);
return x_28;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint32_t x_5; uint8_t x_6; 
x_4 = lean_string_utf8_get(x_1, x_2);
x_5 = 48;
x_6 = lean_uint32_dec_eq(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_15; uint8_t x_16; uint32_t x_34; uint8_t x_35; 
x_6 = lean_string_utf8_get(x_1, x_2);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
lean_inc_ref(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_4);
x_9 = l_String_Slice_Pos_next___redArg(x_8, x_2);
lean_inc(x_9);
lean_inc_ref(x_1);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___lam__0___boxed), 3, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_9);
x_34 = 48;
x_35 = lean_uint32_dec_le(x_34, x_6);
if (x_35 == 0)
{
x_16 = x_35;
goto block_33;
}
else
{
uint32_t x_36; uint8_t x_37; 
x_36 = 57;
x_37 = lean_uint32_dec_le(x_6, x_36);
x_16 = x_37;
goto block_33;
}
block_14:
{
uint32_t x_10; uint32_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = 48;
x_11 = lean_uint32_sub(x_6, x_10);
x_12 = lean_uint32_to_nat(x_11);
x_13 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(x_1, x_9, x_3, x_12);
return x_13;
}
block_33:
{
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
lean_dec_ref(x_15);
lean_dec_ref(x_8);
lean_dec(x_4);
x_17 = 95;
x_18 = lean_uint32_dec_eq(x_6, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_String_mangle___closed__0;
x_20 = lean_string_push(x_19, x_6);
x_21 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(x_1, x_9, x_3, x_20, x_7);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_String_mangle___closed__0;
x_23 = lean_unsigned_to_nat(1u);
x_24 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(x_1, x_9, x_3, x_22, x_23);
return x_24;
}
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = 48;
x_26 = lean_uint32_dec_eq(x_6, x_25);
if (x_26 == 0)
{
lean_dec_ref(x_15);
lean_dec_ref(x_8);
lean_dec(x_4);
goto block_14;
}
else
{
uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_27 = lean_nat_dec_eq(x_9, x_4);
lean_dec(x_4);
x_28 = l_instDecidableNot___redArg(x_27);
x_29 = l_exists__prop__decidable___redArg(x_28, x_15);
if (x_29 == 0)
{
lean_dec_ref(x_8);
goto block_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_String_Slice_Pos_next___redArg(x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
x_31 = l_String_mangle___closed__0;
x_32 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(x_1, x_30, x_3, x_31, x_7);
return x_32;
}
}
}
}
}
else
{
lean_dec(x_4);
lean_dec_ref(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__0(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = lean_string_push(x_3, x_1);
x_2 = x_7;
x_3 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_string_utf8_byte_size(x_1);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_18; uint8_t x_53; 
x_8 = lean_string_utf8_get(x_1, x_2);
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
lean_inc_ref(x_1);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_6);
x_11 = l_String_Slice_Pos_next___redArg(x_10, x_2);
lean_dec(x_2);
x_18 = 95;
x_53 = lean_uint32_dec_eq(x_8, x_18);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_nat_mod(x_5, x_54);
x_56 = lean_nat_dec_eq(x_55, x_9);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; uint32_t x_83; uint8_t x_84; 
lean_inc(x_11);
lean_inc_ref(x_1);
x_57 = lean_alloc_closure((void*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___lam__0___boxed), 3, 2);
lean_closure_set(x_57, 0, x_1);
lean_closure_set(x_57, 1, x_11);
x_83 = 48;
x_84 = lean_uint32_dec_le(x_83, x_8);
if (x_84 == 0)
{
x_58 = x_84;
goto block_82;
}
else
{
uint32_t x_85; uint8_t x_86; 
x_85 = 57;
x_86 = lean_uint32_dec_le(x_8, x_85);
x_58 = x_86;
goto block_82;
}
block_82:
{
if (x_58 == 0)
{
uint32_t x_59; uint8_t x_60; 
lean_dec_ref(x_57);
lean_dec_ref(x_10);
lean_dec(x_6);
x_59 = 120;
x_60 = lean_uint32_dec_eq(x_8, x_59);
if (x_60 == 0)
{
goto block_52;
}
else
{
uint8_t x_61; 
lean_inc(x_11);
lean_inc_ref(x_1);
x_61 = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(x_54, x_1, x_11);
if (x_61 == 0)
{
goto block_52;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint32_t x_67; lean_object* x_68; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_shiftr(x_5, x_62);
lean_dec(x_5);
x_64 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__0(x_18, x_63, x_4);
x_65 = lean_nat_add(x_11, x_54);
lean_inc_ref(x_1);
x_66 = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex___redArg(x_54, x_1, x_11, x_9);
x_67 = l_Char_ofNat(x_66);
lean_dec(x_66);
x_68 = lean_string_push(x_64, x_67);
x_2 = x_65;
x_4 = x_68;
x_5 = x_9;
goto _start;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint32_t x_74; uint8_t x_75; 
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_shiftr(x_5, x_70);
lean_dec(x_5);
x_72 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__0(x_18, x_71, x_4);
x_73 = l_Lean_Name_str___override(x_3, x_72);
x_74 = 48;
x_75 = lean_uint32_dec_eq(x_8, x_74);
if (x_75 == 0)
{
lean_dec_ref(x_57);
lean_dec_ref(x_10);
lean_dec(x_6);
x_12 = x_73;
goto block_17;
}
else
{
uint8_t x_76; uint8_t x_77; uint8_t x_78; 
x_76 = lean_nat_dec_eq(x_11, x_6);
lean_dec(x_6);
x_77 = l_instDecidableNot___redArg(x_76);
x_78 = l_exists__prop__decidable___redArg(x_77, x_57);
if (x_78 == 0)
{
lean_dec_ref(x_10);
x_12 = x_73;
goto block_17;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_String_Slice_Pos_next___redArg(x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
x_80 = l_String_mangle___closed__0;
x_2 = x_79;
x_3 = x_73;
x_4 = x_80;
x_5 = x_9;
goto _start;
}
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_10);
lean_dec(x_6);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_shiftr(x_5, x_87);
lean_dec(x_5);
x_89 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__0(x_18, x_88, x_4);
x_90 = lean_string_push(x_89, x_8);
x_2 = x_11;
x_4 = x_90;
x_5 = x_9;
goto _start;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_10);
lean_dec(x_6);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_add(x_5, x_92);
lean_dec(x_5);
x_2 = x_11;
x_5 = x_93;
goto _start;
}
block_17:
{
uint32_t x_13; uint32_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 48;
x_14 = lean_uint32_sub(x_8, x_13);
x_15 = lean_uint32_to_nat(x_14);
x_16 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(x_1, x_11, x_12, x_15);
return x_16;
}
block_26:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = l_Lean_Name_str___override(x_3, x_4);
x_20 = l_String_mangle___closed__0;
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_shiftr(x_5, x_21);
lean_dec(x_5);
x_23 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__0(x_18, x_22, x_20);
x_24 = lean_string_push(x_23, x_8);
x_2 = x_11;
x_3 = x_19;
x_4 = x_24;
x_5 = x_9;
goto _start;
}
block_39:
{
uint32_t x_27; uint8_t x_28; 
x_27 = 85;
x_28 = lean_uint32_dec_eq(x_8, x_27);
if (x_28 == 0)
{
goto block_26;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_unsigned_to_nat(8u);
lean_inc(x_11);
lean_inc_ref(x_1);
x_30 = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(x_29, x_1, x_11);
if (x_30 == 0)
{
goto block_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint32_t x_36; lean_object* x_37; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_shiftr(x_5, x_31);
lean_dec(x_5);
x_33 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__0(x_18, x_32, x_4);
x_34 = lean_nat_add(x_11, x_29);
lean_inc_ref(x_1);
x_35 = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex___redArg(x_29, x_1, x_11, x_9);
x_36 = l_Char_ofNat(x_35);
lean_dec(x_35);
x_37 = lean_string_push(x_33, x_36);
x_2 = x_34;
x_4 = x_37;
x_5 = x_9;
goto _start;
}
}
}
block_52:
{
uint32_t x_40; uint8_t x_41; 
x_40 = 117;
x_41 = lean_uint32_dec_eq(x_8, x_40);
if (x_41 == 0)
{
goto block_39;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_unsigned_to_nat(4u);
lean_inc(x_11);
lean_inc_ref(x_1);
x_43 = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(x_42, x_1, x_11);
if (x_43 == 0)
{
goto block_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint32_t x_49; lean_object* x_50; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_shiftr(x_5, x_44);
lean_dec(x_5);
x_46 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__0(x_18, x_45, x_4);
x_47 = lean_nat_add(x_11, x_42);
lean_inc_ref(x_1);
x_48 = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex___redArg(x_42, x_1, x_11, x_9);
x_49 = l_Char_ofNat(x_48);
lean_dec(x_48);
x_50 = lean_string_push(x_46, x_49);
x_2 = x_47;
x_4 = x_50;
x_5 = x_9;
goto _start;
}
}
}
}
else
{
uint32_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
x_95 = 95;
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_shiftr(x_5, x_96);
lean_dec(x_5);
x_98 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__0(x_95, x_97, x_4);
x_99 = l_Lean_Name_str___override(x_3, x_98);
return x_99;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__0(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
lean_inc_ref(x_1);
x_2 = l_Lean_Name_demangle(x_1);
lean_inc(x_2);
x_3 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_2);
x_4 = lean_string_dec_eq(x_3, x_1);
lean_dec_ref(x_1);
lean_dec_ref(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
}
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_NameMangling(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
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
l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1);
l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2);
l_Lean_mkModuleInitializationFunctionName___closed__0 = _init_l_Lean_mkModuleInitializationFunctionName___closed__0();
lean_mark_persistent(l_Lean_mkModuleInitializationFunctionName___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lean.Compiler.NameMangling
// Imports: public import Lean.Setup import Init.Data.String.Termination
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
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationFunctionName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed__const__1;
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l___private_Lean_Compiler_NameMangling_0__String_digitChar(uint32_t, lean_object*);
uint32_t lean_uint32_shift_right(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(uint32_t, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationStem(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationFunctionName(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg___boxed(lean_object*);
LEAN_EXPORT uint32_t l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(uint32_t);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkModuleInitializationFunctionName___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_digitChar___boxed(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPackageSymbolPrefix(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_mangle___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationStem___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2;
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed__const__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed__const__1;
static lean_object* l_Lean_mkPackageSymbolPrefix___closed__0;
LEAN_EXPORT lean_object* l_String_mangle___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_sub(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(uint32_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
static lean_object* l_Lean_mkPackageSymbolPrefix___closed__1;
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_demangle___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_land(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0;
LEAN_EXPORT lean_object* l_Lean_Name_demangle(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_mangle(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex(lean_object*, uint32_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPackageSymbolPrefix___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(uint32_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mangle(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
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
LEAN_EXPORT uint32_t l___private_Lean_Compiler_NameMangling_0__String_digitChar(uint32_t x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; 
x_3 = l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(x_1);
return x_3;
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
uint32_t x_6; lean_object* x_7; uint8_t x_11; uint8_t x_38; uint32_t x_49; uint8_t x_50; 
x_6 = lean_string_utf8_get_fast(x_1, x_2);
x_7 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_49 = 65;
x_50 = lean_uint32_dec_le(x_49, x_6);
if (x_50 == 0)
{
goto block_48;
}
else
{
uint32_t x_51; uint8_t x_52; 
x_51 = 90;
x_52 = lean_uint32_dec_le(x_6, x_51);
if (x_52 == 0)
{
goto block_48;
}
else
{
goto block_10;
}
}
block_10:
{
lean_object* x_8; 
x_8 = lean_string_push(x_3, x_6);
x_2 = x_7;
x_3 = x_8;
goto _start;
}
block_37:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 95;
x_13 = lean_uint32_dec_eq(x_6, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_uint32_to_nat(x_6);
x_15 = lean_unsigned_to_nat(256u);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(65536u);
x_18 = lean_nat_dec_lt(x_14, x_17);
lean_dec(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_unsigned_to_nat(8u);
x_20 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0;
x_21 = lean_string_append(x_3, x_20);
x_22 = l___private_Lean_Compiler_NameMangling_0__String_pushHex(x_19, x_6, x_21);
x_2 = x_7;
x_3 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_unsigned_to_nat(4u);
x_25 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1;
x_26 = lean_string_append(x_3, x_25);
x_27 = l___private_Lean_Compiler_NameMangling_0__String_pushHex(x_24, x_6, x_26);
x_2 = x_7;
x_3 = x_27;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_14);
x_29 = lean_unsigned_to_nat(2u);
x_30 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2;
x_31 = lean_string_append(x_3, x_30);
x_32 = l___private_Lean_Compiler_NameMangling_0__String_pushHex(x_29, x_6, x_31);
x_2 = x_7;
x_3 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
x_35 = lean_string_append(x_3, x_34);
x_2 = x_7;
x_3 = x_35;
goto _start;
}
}
else
{
goto block_10;
}
}
block_43:
{
if (x_38 == 0)
{
uint32_t x_39; uint8_t x_40; 
x_39 = 48;
x_40 = lean_uint32_dec_le(x_39, x_6);
if (x_40 == 0)
{
x_11 = x_40;
goto block_37;
}
else
{
uint32_t x_41; uint8_t x_42; 
x_41 = 57;
x_42 = lean_uint32_dec_le(x_6, x_41);
x_11 = x_42;
goto block_37;
}
}
else
{
goto block_10;
}
}
block_48:
{
uint32_t x_44; uint8_t x_45; 
x_44 = 97;
x_45 = lean_uint32_dec_le(x_44, x_6);
if (x_45 == 0)
{
x_38 = x_45;
goto block_43;
}
else
{
uint32_t x_46; uint8_t x_47; 
x_46 = 122;
x_47 = lean_uint32_dec_le(x_6, x_46);
x_38 = x_47;
goto block_43;
}
}
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
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
LEAN_EXPORT lean_object* l_String_mangle___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_mangle(x_1);
lean_dec_ref(x_1);
return x_2;
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
lean_object* x_8; lean_object* x_9; uint8_t x_13; uint32_t x_15; uint8_t x_16; uint32_t x_22; uint8_t x_23; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
lean_dec(x_1);
x_15 = lean_string_utf8_get_fast(x_2, x_3);
x_22 = 48;
x_23 = lean_uint32_dec_le(x_22, x_15);
if (x_23 == 0)
{
x_16 = x_23;
goto block_21;
}
else
{
uint32_t x_24; uint8_t x_25; 
x_24 = 57;
x_25 = lean_uint32_dec_le(x_15, x_24);
x_16 = x_25;
goto block_21;
}
block_12:
{
lean_object* x_10; 
x_10 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_1 = x_9;
x_3 = x_10;
goto _start;
}
block_14:
{
if (x_13 == 0)
{
lean_dec(x_9);
lean_dec(x_3);
return x_13;
}
else
{
goto block_12;
}
}
block_21:
{
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 97;
x_18 = lean_uint32_dec_le(x_17, x_15);
if (x_18 == 0)
{
x_13 = x_18;
goto block_14;
}
else
{
uint32_t x_19; uint8_t x_20; 
x_19 = 102;
x_20 = lean_uint32_dec_le(x_15, x_19);
x_13 = x_20;
goto block_14;
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
lean_dec(x_3);
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
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(uint32_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_9; uint32_t x_19; uint8_t x_20; 
x_19 = 48;
x_20 = lean_uint32_dec_le(x_19, x_1);
if (x_20 == 0)
{
x_9 = x_20;
goto block_18;
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 57;
x_22 = lean_uint32_dec_le(x_1, x_21);
x_9 = x_22;
goto block_18;
}
block_8:
{
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint32_t x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = 87;
x_5 = lean_uint32_sub(x_1, x_4);
x_6 = lean_uint32_to_nat(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
block_18:
{
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 97;
x_11 = lean_uint32_dec_le(x_10, x_1);
if (x_11 == 0)
{
x_2 = x_11;
goto block_8;
}
else
{
uint32_t x_12; uint8_t x_13; 
x_12 = 102;
x_13 = lean_uint32_dec_le(x_1, x_12);
x_2 = x_13;
goto block_8;
}
}
else
{
uint32_t x_14; uint32_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = 48;
x_15 = lean_uint32_sub(x_1, x_14);
x_16 = lean_uint32_to_nat(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_string_utf8_byte_size(x_2);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
uint32_t x_11; lean_object* x_12; 
x_11 = lean_string_utf8_get_fast(x_2, x_3);
x_12 = l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_1, x_15);
lean_dec(x_1);
x_17 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_18 = lean_unsigned_to_nat(4u);
x_19 = lean_nat_shiftl(x_4, x_18);
lean_dec(x_4);
x_20 = lean_nat_lor(x_19, x_14);
lean_dec(x_14);
lean_dec(x_19);
x_1 = x_16;
x_3 = x_17;
x_4 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = lean_box(0);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get_fast(x_1, x_2);
x_6 = 95;
x_7 = lean_uint32_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 120;
x_9 = lean_uint32_dec_eq(x_5, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 117;
x_11 = lean_uint32_dec_eq(x_5, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 85;
x_13 = lean_uint32_dec_eq(x_5, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
lean_dec(x_2);
x_14 = 48;
x_15 = lean_uint32_dec_le(x_14, x_5);
if (x_15 == 0)
{
return x_15;
}
else
{
uint32_t x_16; uint8_t x_17; 
x_16 = 57;
x_17 = lean_uint32_dec_le(x_5, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(8u);
x_19 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_20 = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(x_18, x_1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(4u);
x_22 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_23 = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(x_21, x_1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(2u);
x_25 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_26 = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(x_24, x_1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_2 = x_27;
goto _start;
}
}
else
{
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_string_utf8_byte_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; uint32_t x_15; uint8_t x_16; 
lean_inc_ref(x_6);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_7, x_11);
x_13 = l_String_Slice_Pos_prevAux_go___redArg(x_10, x_12);
lean_dec_ref(x_10);
x_14 = lean_string_utf8_get_fast(x_6, x_13);
lean_dec(x_13);
x_15 = 95;
x_16 = lean_uint32_dec_eq(x_14, x_15);
if (x_16 == 0)
{
goto block_5;
}
else
{
return x_16;
}
}
else
{
goto block_5;
}
}
else
{
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
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
lean_dec_ref(x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
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
x_15 = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(x_3, x_5);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Name_mangle(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_1);
x_4 = lean_string_append(x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationStem(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_String_mangle___closed__0;
x_4 = l_Lean_Name_mangle(x_1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_String_mangle(x_5);
x_7 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Lean_Name_mangle(x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationStem___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkModuleInitializationStem(x_1, x_2);
lean_dec(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationFunctionName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_mkModuleInitializationFunctionName___closed__0;
x_4 = l_Lean_mkModuleInitializationStem(x_1, x_2);
x_5 = lean_string_append(x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationFunctionName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkModuleInitializationFunctionName(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkPackageSymbolPrefix___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("l_", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_mkPackageSymbolPrefix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lp_", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPackageSymbolPrefix(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_mkPackageSymbolPrefix___closed__0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_mkPackageSymbolPrefix___closed__1;
x_5 = l_String_mangle(x_3);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkPackageSymbolPrefix___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkPackageSymbolPrefix(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(x_4, x_2, x_3);
return x_5;
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
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_16; uint8_t x_17; 
x_8 = lean_string_utf8_get_fast(x_1, x_2);
x_9 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_16 = 95;
x_17 = lean_uint32_dec_eq(x_8, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_57; uint8_t x_58; uint8_t x_66; uint8_t x_87; 
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_mod(x_5, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_87 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_87 == 0)
{
uint32_t x_88; uint8_t x_89; 
x_88 = 48;
x_89 = lean_uint32_dec_le(x_88, x_8);
if (x_89 == 0)
{
x_66 = x_89;
goto block_86;
}
else
{
uint32_t x_90; uint8_t x_91; 
x_90 = 57;
x_91 = lean_uint32_dec_le(x_8, x_90);
x_66 = x_91;
goto block_86;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_shiftr(x_5, x_92);
lean_dec(x_5);
x_94 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(x_16, x_93, x_4);
x_95 = lean_string_push(x_94, x_8);
x_2 = x_9;
x_4 = x_95;
x_5 = x_20;
goto _start;
}
block_28:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = l_Lean_Name_str___override(x_3, x_4);
x_22 = l_String_mangle___closed__0;
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_shiftr(x_5, x_23);
lean_dec(x_5);
x_25 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(x_16, x_24, x_22);
x_26 = lean_string_push(x_25, x_8);
x_2 = x_9;
x_3 = x_21;
x_4 = x_26;
x_5 = x_20;
goto _start;
}
block_42:
{
uint32_t x_29; uint8_t x_30; 
x_29 = 85;
x_30 = lean_uint32_dec_eq(x_8, x_29);
if (x_30 == 0)
{
goto block_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_unsigned_to_nat(8u);
x_32 = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(x_31, x_1, x_9, x_20);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint32_t x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_shiftr(x_5, x_36);
lean_dec(x_5);
x_38 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(x_16, x_37, x_4);
x_39 = l_Char_ofNat(x_35);
lean_dec(x_35);
x_40 = lean_string_push(x_38, x_39);
x_2 = x_34;
x_4 = x_40;
x_5 = x_20;
goto _start;
}
else
{
lean_dec(x_32);
goto block_28;
}
}
}
block_56:
{
uint32_t x_43; uint8_t x_44; 
x_43 = 117;
x_44 = lean_uint32_dec_eq(x_8, x_43);
if (x_44 == 0)
{
goto block_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_unsigned_to_nat(4u);
x_46 = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(x_45, x_1, x_9, x_20);
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint32_t x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_shiftr(x_5, x_50);
lean_dec(x_5);
x_52 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(x_16, x_51, x_4);
x_53 = l_Char_ofNat(x_49);
lean_dec(x_49);
x_54 = lean_string_push(x_52, x_53);
x_2 = x_48;
x_4 = x_54;
x_5 = x_20;
goto _start;
}
else
{
lean_dec(x_46);
goto block_42;
}
}
}
block_65:
{
if (x_58 == 0)
{
x_10 = x_57;
goto block_15;
}
else
{
uint32_t x_59; uint32_t x_60; uint8_t x_61; 
x_59 = lean_string_utf8_get_fast(x_1, x_9);
x_60 = 48;
x_61 = lean_uint32_dec_eq(x_59, x_60);
if (x_61 == 0)
{
x_10 = x_57;
goto block_15;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_string_utf8_next_fast(x_1, x_9);
x_63 = l_String_mangle___closed__0;
x_2 = x_62;
x_3 = x_57;
x_4 = x_63;
x_5 = x_20;
goto _start;
}
}
}
block_86:
{
if (x_66 == 0)
{
uint32_t x_67; uint8_t x_68; 
x_67 = 120;
x_68 = lean_uint32_dec_eq(x_8, x_67);
if (x_68 == 0)
{
goto block_56;
}
else
{
lean_object* x_69; 
x_69 = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(x_18, x_1, x_9, x_20);
if (lean_obj_tag(x_69) == 1)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint32_t x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_shiftr(x_5, x_73);
lean_dec(x_5);
x_75 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(x_16, x_74, x_4);
x_76 = l_Char_ofNat(x_72);
lean_dec(x_72);
x_77 = lean_string_push(x_75, x_76);
x_2 = x_71;
x_4 = x_77;
x_5 = x_20;
goto _start;
}
else
{
lean_dec(x_69);
goto block_56;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint32_t x_83; uint8_t x_84; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_shiftr(x_5, x_79);
lean_dec(x_5);
x_81 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(x_16, x_80, x_4);
x_82 = l_Lean_Name_str___override(x_3, x_81);
x_83 = 48;
x_84 = lean_uint32_dec_eq(x_8, x_83);
if (x_84 == 0)
{
x_10 = x_82;
goto block_15;
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_eq(x_9, x_6);
if (x_85 == 0)
{
x_57 = x_82;
x_58 = x_84;
goto block_65;
}
else
{
x_57 = x_82;
x_58 = x_17;
goto block_65;
}
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_add(x_5, x_97);
lean_dec(x_5);
x_2 = x_9;
x_5 = x_98;
goto _start;
}
block_15:
{
uint32_t x_11; uint32_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = 48;
x_12 = lean_uint32_sub(x_8, x_11);
x_13 = lean_uint32_to_nat(x_12);
x_14 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(x_1, x_9, x_10, x_13);
return x_14;
}
}
else
{
uint32_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_2);
x_100 = 95;
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_shiftr(x_5, x_101);
lean_dec(x_5);
x_103 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(x_100, x_102, x_4);
x_104 = l_Lean_Name_str___override(x_3, x_103);
return x_104;
}
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
uint32_t x_6; lean_object* x_7; uint8_t x_13; uint8_t x_22; uint32_t x_36; uint8_t x_37; 
x_6 = lean_string_utf8_get_fast(x_1, x_2);
x_7 = lean_string_utf8_next_fast(x_1, x_2);
x_36 = 48;
x_37 = lean_uint32_dec_le(x_36, x_6);
if (x_37 == 0)
{
x_22 = x_37;
goto block_35;
}
else
{
uint32_t x_38; uint8_t x_39; 
x_38 = 57;
x_39 = lean_uint32_dec_le(x_6, x_38);
x_22 = x_39;
goto block_35;
}
block_12:
{
uint32_t x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 48;
x_9 = lean_uint32_sub(x_6, x_8);
x_10 = lean_uint32_to_nat(x_9);
x_11 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(x_1, x_7, x_3, x_10);
return x_11;
}
block_21:
{
if (x_13 == 0)
{
goto block_12;
}
else
{
uint32_t x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_string_utf8_get_fast(x_1, x_7);
x_15 = 48;
x_16 = lean_uint32_dec_eq(x_14, x_15);
if (x_16 == 0)
{
goto block_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_string_utf8_next_fast(x_1, x_7);
x_18 = l_String_mangle___closed__0;
x_19 = lean_unsigned_to_nat(0u);
x_20 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(x_1, x_17, x_3, x_18, x_19);
return x_20;
}
}
}
block_35:
{
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 95;
x_24 = lean_uint32_dec_eq(x_6, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l_String_mangle___closed__0;
x_26 = lean_string_push(x_25, x_6);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(x_1, x_7, x_3, x_26, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_String_mangle___closed__0;
x_30 = lean_unsigned_to_nat(1u);
x_31 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(x_1, x_7, x_3, x_29, x_30);
return x_31;
}
}
else
{
uint32_t x_32; uint8_t x_33; 
x_32 = 48;
x_33 = lean_uint32_dec_eq(x_6, x_32);
if (x_33 == 0)
{
goto block_12;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_eq(x_7, x_4);
if (x_34 == 0)
{
x_13 = x_33;
goto block_21;
}
else
{
x_13 = x_5;
goto block_21;
}
}
}
}
}
else
{
return x_3;
}
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
uint32_t x_7; lean_object* x_8; uint8_t x_9; uint32_t x_22; uint8_t x_23; 
x_7 = lean_string_utf8_get_fast(x_1, x_2);
x_8 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_22 = 48;
x_23 = lean_uint32_dec_le(x_22, x_7);
if (x_23 == 0)
{
x_9 = x_23;
goto block_21;
}
else
{
uint32_t x_24; uint8_t x_25; 
x_24 = 57;
x_25 = lean_uint32_dec_le(x_7, x_24);
x_9 = x_25;
goto block_21;
}
block_21:
{
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Name_num___override(x_3, x_4);
x_11 = lean_nat_dec_eq(x_8, x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_string_utf8_next_fast(x_1, x_8);
x_13 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(x_1, x_12, x_10);
return x_13;
}
else
{
return x_10;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint32_t x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(10u);
x_15 = lean_nat_mul(x_4, x_14);
lean_dec(x_4);
x_16 = 48;
x_17 = lean_uint32_sub(x_7, x_16);
x_18 = lean_uint32_to_nat(x_17);
x_19 = lean_nat_add(x_15, x_18);
lean_dec(x_18);
lean_dec(x_15);
x_2 = x_8;
x_4 = x_19;
goto _start;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_2);
x_26 = l_Lean_Name_num___override(x_3, x_4);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 120;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; 
x_5 = 120;
x_6 = lean_uint32_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box_uint32(x_1);
x_8 = lean_apply_4(x_4, x_7, x_2, lean_box(0), lean_box(0));
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_3(x_3, x_10, x_11, lean_box(0));
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
x_14 = lean_apply_4(x_4, x_13, x_2, lean_box(0), lean_box(0));
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 120;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; uint8_t x_8; 
x_7 = 120;
x_8 = lean_uint32_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_box_uint32(x_3);
x_10 = lean_apply_4(x_6, x_9, x_4, lean_box(0), lean_box(0));
return x_10;
}
else
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_3(x_5, x_12, x_13, lean_box(0));
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed__const__1;
x_16 = lean_apply_4(x_6, x_15, x_4, lean_box(0), lean_box(0));
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 117;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; 
x_5 = 117;
x_6 = lean_uint32_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box_uint32(x_1);
x_8 = lean_apply_4(x_4, x_7, x_2, lean_box(0), lean_box(0));
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_3(x_3, x_10, x_11, lean_box(0));
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1;
x_14 = lean_apply_4(x_4, x_13, x_2, lean_box(0), lean_box(0));
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 117;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; uint8_t x_8; 
x_7 = 117;
x_8 = lean_uint32_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_box_uint32(x_3);
x_10 = lean_apply_4(x_6, x_9, x_4, lean_box(0), lean_box(0));
return x_10;
}
else
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_3(x_5, x_12, x_13, lean_box(0));
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed__const__1;
x_16 = lean_apply_4(x_6, x_15, x_4, lean_box(0), lean_box(0));
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 85;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; 
x_5 = 85;
x_6 = lean_uint32_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box_uint32(x_1);
x_8 = lean_apply_4(x_4, x_7, x_2, lean_box(0), lean_box(0));
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_3(x_3, x_10, x_11, lean_box(0));
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
x_14 = lean_apply_4(x_4, x_13, x_2, lean_box(0), lean_box(0));
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 85;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; uint8_t x_8; 
x_7 = 85;
x_8 = lean_uint32_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_box_uint32(x_3);
x_10 = lean_apply_4(x_6, x_9, x_4, lean_box(0), lean_box(0));
return x_10;
}
else
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_3(x_5, x_12, x_13, lean_box(0));
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed__const__1;
x_16 = lean_apply_4(x_6, x_15, x_4, lean_box(0), lean_box(0));
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_Name_demangle___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Name_demangle(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Name_demangle(x_1);
lean_inc(x_2);
x_3 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_2);
x_4 = lean_string_dec_eq(x_3, x_1);
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
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Name_demangle_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Setup(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_NameMangling(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Setup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
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
l_Lean_mkPackageSymbolPrefix___closed__0 = _init_l_Lean_mkPackageSymbolPrefix___closed__0();
lean_mark_persistent(l_Lean_mkPackageSymbolPrefix___closed__0);
l_Lean_mkPackageSymbolPrefix___closed__1 = _init_l_Lean_mkPackageSymbolPrefix___closed__1();
lean_mark_persistent(l_Lean_mkPackageSymbolPrefix___closed__1);
l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1);
l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed__const__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed__const__1);
l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1);
l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed__const__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed__const__1);
l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1);
l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed__const__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

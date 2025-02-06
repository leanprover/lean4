// Lean compiler output
// Module: Lean.Data.Json.Parser
// Imports: Lean.Data.Json.Basic Lean.Data.RBMap Std.Internal.Parsec
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
static lean_object* l_Lean_Json_Parser_exponent___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Json_Parser_anyCore___closed__9;
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_numWithDecimals___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Std_Internal_Parsec_expectedEndOfInput;
static lean_object* l_Lean_Json_Parser_objectCore___closed__5;
lean_object* l_Lean_JsonNumber_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__4;
static lean_object* l_Lean_Json_Parser_anyCore___closed__5;
static lean_object* l_Lean_Json_Parser_numSign___closed__1;
static lean_object* l_Lean_Json_Parser_natMaybeZero___closed__1;
static lean_object* l_Lean_Json_Parser_numWithDecimals___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNumDigits(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_hexChar(lean_object*);
static lean_object* l_Lean_Json_Parser_arrayCore___closed__1;
static lean_object* l_Lean_Json_Parser_objectCore___closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__7;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__3;
static lean_object* l_Lean_Json_Parser_natMaybeZero___closed__2;
static lean_object* l_Lean_Json_Parser_anyCore___closed__6;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar(lean_object*);
static lean_object* l_Lean_Json_Parser_objectCore___closed__4;
static lean_object* l_Lean_Json_Parser_anyCore___closed__10;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCoreNumDigits(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_shiftl(lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_strCore___closed__1;
static lean_object* l_Lean_Json_Parser_natNumDigits___closed__1;
static lean_object* l_Lean_Json_Parser_anyCore___closed__4;
extern lean_object* l_Std_Internal_Parsec_unexpectedEndOfInput;
static lean_object* l_Lean_Json_Parser_objectCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent(lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_anyCore___closed__3;
static lean_object* l_Lean_Json_Parser_numSign___closed__2;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__5;
static lean_object* l_Lean_Json_Parser_lookahead___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNonZero(lean_object*);
extern lean_object* l_System_Platform_numBits;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_natNumDigits___closed__2;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead(lean_object*);
static lean_object* l_Lean_Json_Parser_anyCore___closed__8;
uint32_t lean_uint32_sub(uint32_t, uint32_t);
static lean_object* l_Lean_Json_Parser_objectCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_strCore(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lean_Json_Parser_escapedChar___closed__1;
static lean_object* l_Lean_Json_parse___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_anyCore___closed__7;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_num(lean_object*);
static lean_object* l_Lean_Json_Parser_natNonZero___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_anyCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numSign(lean_object*);
lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__1;
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_nat(lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
static lean_object* l_Lean_Json_Parser_hexChar___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_anyCore___closed__2;
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_str___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_str(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__8;
static lean_object* l_Lean_Json_Parser_natNonZero___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__6;
lean_object* l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object*);
static lean_object* _init_l_Lean_Json_Parser_hexChar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid hex character", 21, 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_hexChar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; lean_object* x_13; uint32_t x_50; uint8_t x_51; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_string_utf8_get_fast(x_2, x_3);
x_12 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_12);
x_50 = 48;
x_51 = lean_uint32_dec_le(x_50, x_11);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_box(0);
x_13 = x_52;
goto block_49;
}
else
{
uint32_t x_53; uint8_t x_54; 
x_53 = 57;
x_54 = lean_uint32_dec_le(x_11, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_box(0);
x_13 = x_55;
goto block_49;
}
else
{
uint32_t x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_uint32_sub(x_11, x_50);
x_57 = lean_uint32_to_nat(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
block_49:
{
uint32_t x_14; uint8_t x_15; 
lean_dec(x_13);
x_14 = 97;
x_15 = lean_uint32_dec_le(x_14, x_11);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 65;
x_17 = lean_uint32_dec_le(x_16, x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Json_Parser_hexChar___closed__1;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
uint32_t x_20; uint8_t x_21; 
x_20 = 70;
x_21 = lean_uint32_dec_le(x_11, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Json_Parser_hexChar___closed__1;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
uint32_t x_24; uint32_t x_25; uint32_t x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_uint32_sub(x_11, x_16);
x_25 = 10;
x_26 = lean_uint32_add(x_24, x_25);
x_27 = lean_uint32_to_nat(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint32_t x_29; uint8_t x_30; 
x_29 = 102;
x_30 = lean_uint32_dec_le(x_11, x_29);
if (x_30 == 0)
{
uint32_t x_31; uint8_t x_32; 
x_31 = 65;
x_32 = lean_uint32_dec_le(x_31, x_11);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Json_Parser_hexChar___closed__1;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
else
{
uint32_t x_35; uint8_t x_36; 
x_35 = 70;
x_36 = lean_uint32_dec_le(x_11, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Json_Parser_hexChar___closed__1;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
else
{
uint32_t x_39; uint32_t x_40; uint32_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_uint32_sub(x_11, x_31);
x_40 = 10;
x_41 = lean_uint32_add(x_39, x_40);
x_42 = lean_uint32_to_nat(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint32_t x_44; uint32_t x_45; uint32_t x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_uint32_sub(x_11, x_14);
x_45 = 10;
x_46 = lean_uint32_add(x_44, x_45);
x_47 = lean_uint32_to_nat(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint32_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint32_t x_99; uint8_t x_100; 
lean_dec(x_1);
x_59 = lean_string_utf8_get_fast(x_2, x_3);
x_60 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_2);
lean_ctor_set(x_61, 1, x_60);
x_99 = 48;
x_100 = lean_uint32_dec_le(x_99, x_59);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_box(0);
x_62 = x_101;
goto block_98;
}
else
{
uint32_t x_102; uint8_t x_103; 
x_102 = 57;
x_103 = lean_uint32_dec_le(x_59, x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_box(0);
x_62 = x_104;
goto block_98;
}
else
{
uint32_t x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_uint32_sub(x_59, x_99);
x_106 = lean_uint32_to_nat(x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_61);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
block_98:
{
uint32_t x_63; uint8_t x_64; 
lean_dec(x_62);
x_63 = 97;
x_64 = lean_uint32_dec_le(x_63, x_59);
if (x_64 == 0)
{
uint32_t x_65; uint8_t x_66; 
x_65 = 65;
x_66 = lean_uint32_dec_le(x_65, x_59);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_Json_Parser_hexChar___closed__1;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
else
{
uint32_t x_69; uint8_t x_70; 
x_69 = 70;
x_70 = lean_uint32_dec_le(x_59, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Lean_Json_Parser_hexChar___closed__1;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_61);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
else
{
uint32_t x_73; uint32_t x_74; uint32_t x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_uint32_sub(x_59, x_65);
x_74 = 10;
x_75 = lean_uint32_add(x_73, x_74);
x_76 = lean_uint32_to_nat(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_61);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint32_t x_78; uint8_t x_79; 
x_78 = 102;
x_79 = lean_uint32_dec_le(x_59, x_78);
if (x_79 == 0)
{
uint32_t x_80; uint8_t x_81; 
x_80 = 65;
x_81 = lean_uint32_dec_le(x_80, x_59);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = l_Lean_Json_Parser_hexChar___closed__1;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_61);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
else
{
uint32_t x_84; uint8_t x_85; 
x_84 = 70;
x_85 = lean_uint32_dec_le(x_59, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Lean_Json_Parser_hexChar___closed__1;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_61);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
else
{
uint32_t x_88; uint32_t x_89; uint32_t x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_uint32_sub(x_59, x_80);
x_89 = 10;
x_90 = lean_uint32_add(x_88, x_89);
x_91 = lean_uint32_to_nat(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_61);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint32_t x_93; uint32_t x_94; uint32_t x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_uint32_sub(x_59, x_63);
x_94 = 10;
x_95 = lean_uint32_add(x_93, x_94);
x_96 = lean_uint32_to_nat(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_61);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("illegal \\u escape", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 9;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 13;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__3() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__4() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 12;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__5() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 8;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__6() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__7() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 34;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__8() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_string_utf8_get_fast(x_2, x_3);
x_12 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_12);
x_13 = 92;
x_14 = lean_uint32_dec_eq(x_11, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 34;
x_16 = lean_uint32_dec_eq(x_11, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 47;
x_18 = lean_uint32_dec_eq(x_11, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 98;
x_20 = lean_uint32_dec_eq(x_11, x_19);
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 102;
x_22 = lean_uint32_dec_eq(x_11, x_21);
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 110;
x_24 = lean_uint32_dec_eq(x_11, x_23);
if (x_24 == 0)
{
uint32_t x_25; uint8_t x_26; 
x_25 = 114;
x_26 = lean_uint32_dec_eq(x_11, x_25);
if (x_26 == 0)
{
uint32_t x_27; uint8_t x_28; 
x_27 = 116;
x_28 = lean_uint32_dec_eq(x_11, x_27);
if (x_28 == 0)
{
uint32_t x_29; uint8_t x_30; 
x_29 = 117;
x_30 = lean_uint32_dec_eq(x_11, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Json_Parser_escapedChar___closed__1;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Json_Parser_hexChar(x_1);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Json_Parser_hexChar(x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Json_Parser_hexChar(x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Json_Parser_hexChar(x_40);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint32_t x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_42, 1);
x_45 = lean_unsigned_to_nat(4096u);
x_46 = lean_nat_mul(x_45, x_35);
lean_dec(x_35);
x_47 = lean_unsigned_to_nat(256u);
x_48 = lean_nat_mul(x_47, x_38);
lean_dec(x_38);
x_49 = lean_nat_add(x_46, x_48);
lean_dec(x_48);
lean_dec(x_46);
x_50 = lean_unsigned_to_nat(16u);
x_51 = lean_nat_mul(x_50, x_41);
lean_dec(x_41);
x_52 = lean_nat_add(x_49, x_51);
lean_dec(x_51);
lean_dec(x_49);
x_53 = lean_nat_add(x_52, x_44);
lean_dec(x_44);
lean_dec(x_52);
x_54 = l_Char_ofNat(x_53);
lean_dec(x_53);
x_55 = lean_unbox_uint32(x_54);
lean_dec(x_54);
x_56 = lean_box_uint32(x_55);
lean_ctor_set(x_42, 1, x_56);
return x_42;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint32_t x_69; lean_object* x_70; lean_object* x_71; 
x_57 = lean_ctor_get(x_42, 0);
x_58 = lean_ctor_get(x_42, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_42);
x_59 = lean_unsigned_to_nat(4096u);
x_60 = lean_nat_mul(x_59, x_35);
lean_dec(x_35);
x_61 = lean_unsigned_to_nat(256u);
x_62 = lean_nat_mul(x_61, x_38);
lean_dec(x_38);
x_63 = lean_nat_add(x_60, x_62);
lean_dec(x_62);
lean_dec(x_60);
x_64 = lean_unsigned_to_nat(16u);
x_65 = lean_nat_mul(x_64, x_41);
lean_dec(x_41);
x_66 = lean_nat_add(x_63, x_65);
lean_dec(x_65);
lean_dec(x_63);
x_67 = lean_nat_add(x_66, x_58);
lean_dec(x_58);
lean_dec(x_66);
x_68 = l_Char_ofNat(x_67);
lean_dec(x_67);
x_69 = lean_unbox_uint32(x_68);
lean_dec(x_68);
x_70 = lean_box_uint32(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_35);
x_72 = !lean_is_exclusive(x_42);
if (x_72 == 0)
{
return x_42;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_42, 0);
x_74 = lean_ctor_get(x_42, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_42);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_38);
lean_dec(x_35);
x_76 = !lean_is_exclusive(x_39);
if (x_76 == 0)
{
return x_39;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_39, 0);
x_78 = lean_ctor_get(x_39, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_39);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_35);
x_80 = !lean_is_exclusive(x_36);
if (x_80 == 0)
{
return x_36;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_36, 0);
x_82 = lean_ctor_get(x_36, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_36);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_33);
if (x_84 == 0)
{
return x_33;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_33, 0);
x_86 = lean_ctor_get(x_33, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_33);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Lean_Json_Parser_escapedChar___boxed__const__1;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = l_Lean_Json_Parser_escapedChar___boxed__const__2;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = l_Lean_Json_Parser_escapedChar___boxed__const__3;
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = l_Lean_Json_Parser_escapedChar___boxed__const__4;
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = l_Lean_Json_Parser_escapedChar___boxed__const__5;
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = l_Lean_Json_Parser_escapedChar___boxed__const__6;
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_1);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = l_Lean_Json_Parser_escapedChar___boxed__const__7;
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_1);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = l_Lean_Json_Parser_escapedChar___boxed__const__8;
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
else
{
uint32_t x_104; lean_object* x_105; lean_object* x_106; uint32_t x_107; uint8_t x_108; 
lean_dec(x_1);
x_104 = lean_string_utf8_get_fast(x_2, x_3);
x_105 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_2);
lean_ctor_set(x_106, 1, x_105);
x_107 = 92;
x_108 = lean_uint32_dec_eq(x_104, x_107);
if (x_108 == 0)
{
uint32_t x_109; uint8_t x_110; 
x_109 = 34;
x_110 = lean_uint32_dec_eq(x_104, x_109);
if (x_110 == 0)
{
uint32_t x_111; uint8_t x_112; 
x_111 = 47;
x_112 = lean_uint32_dec_eq(x_104, x_111);
if (x_112 == 0)
{
uint32_t x_113; uint8_t x_114; 
x_113 = 98;
x_114 = lean_uint32_dec_eq(x_104, x_113);
if (x_114 == 0)
{
uint32_t x_115; uint8_t x_116; 
x_115 = 102;
x_116 = lean_uint32_dec_eq(x_104, x_115);
if (x_116 == 0)
{
uint32_t x_117; uint8_t x_118; 
x_117 = 110;
x_118 = lean_uint32_dec_eq(x_104, x_117);
if (x_118 == 0)
{
uint32_t x_119; uint8_t x_120; 
x_119 = 114;
x_120 = lean_uint32_dec_eq(x_104, x_119);
if (x_120 == 0)
{
uint32_t x_121; uint8_t x_122; 
x_121 = 116;
x_122 = lean_uint32_dec_eq(x_104, x_121);
if (x_122 == 0)
{
uint32_t x_123; uint8_t x_124; 
x_123 = 117;
x_124 = lean_uint32_dec_eq(x_104, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = l_Lean_Json_Parser_escapedChar___closed__1;
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_106);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
else
{
lean_object* x_127; 
x_127 = l_Lean_Json_Parser_hexChar(x_106);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = l_Lean_Json_Parser_hexChar(x_128);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Lean_Json_Parser_hexChar(x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Json_Parser_hexChar(x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint32_t x_150; lean_object* x_151; lean_object* x_152; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
x_140 = lean_unsigned_to_nat(4096u);
x_141 = lean_nat_mul(x_140, x_129);
lean_dec(x_129);
x_142 = lean_unsigned_to_nat(256u);
x_143 = lean_nat_mul(x_142, x_132);
lean_dec(x_132);
x_144 = lean_nat_add(x_141, x_143);
lean_dec(x_143);
lean_dec(x_141);
x_145 = lean_unsigned_to_nat(16u);
x_146 = lean_nat_mul(x_145, x_135);
lean_dec(x_135);
x_147 = lean_nat_add(x_144, x_146);
lean_dec(x_146);
lean_dec(x_144);
x_148 = lean_nat_add(x_147, x_138);
lean_dec(x_138);
lean_dec(x_147);
x_149 = l_Char_ofNat(x_148);
lean_dec(x_148);
x_150 = lean_unbox_uint32(x_149);
lean_dec(x_149);
x_151 = lean_box_uint32(x_150);
if (lean_is_scalar(x_139)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_139;
}
lean_ctor_set(x_152, 0, x_137);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_135);
lean_dec(x_132);
lean_dec(x_129);
x_153 = lean_ctor_get(x_136, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_136, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_155 = x_136;
} else {
 lean_dec_ref(x_136);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_132);
lean_dec(x_129);
x_157 = lean_ctor_get(x_133, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_133, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_159 = x_133;
} else {
 lean_dec_ref(x_133);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_129);
x_161 = lean_ctor_get(x_130, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_130, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_163 = x_130;
} else {
 lean_dec_ref(x_130);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_127, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_127, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_167 = x_127;
} else {
 lean_dec_ref(x_127);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = l_Lean_Json_Parser_escapedChar___boxed__const__1;
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_106);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = l_Lean_Json_Parser_escapedChar___boxed__const__2;
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_106);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = l_Lean_Json_Parser_escapedChar___boxed__const__3;
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_106);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Lean_Json_Parser_escapedChar___boxed__const__4;
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_106);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = l_Lean_Json_Parser_escapedChar___boxed__const__5;
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_106);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = l_Lean_Json_Parser_escapedChar___boxed__const__6;
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_106);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = l_Lean_Json_Parser_escapedChar___boxed__const__7;
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_106);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = l_Lean_Json_Parser_escapedChar___boxed__const__8;
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_106);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_strCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected character in string", 30, 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_strCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint32_t x_12; uint32_t x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 0);
lean_dec(x_11);
x_12 = lean_string_utf8_get_fast(x_3, x_4);
x_13 = 34;
x_14 = lean_uint32_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_15 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_15);
x_16 = 92;
x_17 = lean_uint32_dec_eq(x_12, x_16);
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = 32;
x_19 = lean_uint32_dec_le(x_18, x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = l_Lean_Json_Parser_strCore___closed__1;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
uint32_t x_22; uint8_t x_23; 
x_22 = 1114111;
x_23 = lean_uint32_dec_le(x_12, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = l_Lean_Json_Parser_strCore___closed__1;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_string_push(x_1, x_12);
x_1 = x_26;
goto _start;
}
}
}
else
{
lean_object* x_28; 
x_28 = l_Lean_Json_Parser_escapedChar(x_2);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unbox_uint32(x_30);
lean_dec(x_30);
x_32 = lean_string_push(x_1, x_31);
x_1 = x_32;
x_2 = x_29;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_1);
return x_39;
}
}
else
{
uint32_t x_40; uint32_t x_41; uint8_t x_42; 
lean_dec(x_2);
x_40 = lean_string_utf8_get_fast(x_3, x_4);
x_41 = 34;
x_42 = lean_uint32_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint32_t x_45; uint8_t x_46; 
x_43 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_43);
x_45 = 92;
x_46 = lean_uint32_dec_eq(x_40, x_45);
if (x_46 == 0)
{
uint32_t x_47; uint8_t x_48; 
x_47 = 32;
x_48 = lean_uint32_dec_le(x_47, x_40);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_1);
x_49 = l_Lean_Json_Parser_strCore___closed__1;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
else
{
uint32_t x_51; uint8_t x_52; 
x_51 = 1114111;
x_52 = lean_uint32_dec_le(x_40, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_53 = l_Lean_Json_Parser_strCore___closed__1;
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
else
{
lean_object* x_55; 
x_55 = lean_string_push(x_1, x_40);
x_1 = x_55;
x_2 = x_44;
goto _start;
}
}
}
else
{
lean_object* x_57; 
x_57 = l_Lean_Json_Parser_escapedChar(x_44);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint32_t x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unbox_uint32(x_59);
lean_dec(x_59);
x_61 = lean_string_push(x_1, x_60);
x_1 = x_61;
x_2 = x_58;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_1);
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_65 = x_57;
} else {
 lean_dec_ref(x_57);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_3);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_1);
return x_69;
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_str___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_str(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Json_Parser_str___closed__1;
x_3 = l_Lean_Json_Parser_strCore(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_1);
return x_7;
}
else
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_3, x_4);
x_9 = 48;
x_10 = lean_uint32_dec_le(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_1);
return x_11;
}
else
{
uint32_t x_12; uint8_t x_13; 
x_12 = 57;
x_13 = lean_uint32_dec_le(x_8, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_1);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint32_t x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_2, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 0);
lean_dec(x_17);
x_18 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_18);
x_19 = lean_unsigned_to_nat(10u);
x_20 = lean_nat_mul(x_19, x_1);
lean_dec(x_1);
x_21 = lean_uint32_sub(x_8, x_9);
x_22 = lean_uint32_to_nat(x_21);
x_23 = lean_nat_add(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
x_1 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint32_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_25 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_unsigned_to_nat(10u);
x_28 = lean_nat_mul(x_27, x_1);
lean_dec(x_1);
x_29 = lean_uint32_sub(x_8, x_9);
x_30 = lean_uint32_to_nat(x_29);
x_31 = lean_nat_add(x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_1 = x_31;
x_2 = x_26;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCoreNumDigits(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = lean_string_utf8_get_fast(x_4, x_5);
x_11 = 48;
x_12 = lean_uint32_dec_le(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 57;
x_16 = lean_uint32_dec_le(x_10, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_3, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 0);
lean_dec(x_21);
x_22 = lean_string_utf8_next_fast(x_4, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_22);
x_23 = lean_unsigned_to_nat(10u);
x_24 = lean_nat_mul(x_23, x_1);
lean_dec(x_1);
x_25 = lean_uint32_sub(x_10, x_11);
x_26 = lean_uint32_to_nat(x_25);
x_27 = lean_nat_add(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_2, x_28);
lean_dec(x_2);
x_1 = x_27;
x_2 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint32_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_3);
x_31 = lean_string_utf8_next_fast(x_4, x_5);
lean_dec(x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_unsigned_to_nat(10u);
x_34 = lean_nat_mul(x_33, x_1);
lean_dec(x_1);
x_35 = lean_uint32_sub(x_10, x_11);
x_36 = lean_uint32_to_nat(x_35);
x_37 = lean_nat_add(x_34, x_36);
lean_dec(x_36);
lean_dec(x_34);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_2, x_38);
lean_dec(x_2);
x_1 = x_37;
x_2 = x_39;
x_3 = x_32;
goto _start;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_lookahead___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected ", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint32_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_string_utf8_get_fast(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_box_uint32(x_10);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Json_Parser_lookahead___rarg___closed__1;
x_15 = lean_string_append(x_14, x_1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Json_Parser_lookahead___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Json_Parser_lookahead___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Json_Parser_natNonZero___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("1-9", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_natNonZero___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Json_Parser_lookahead___rarg___closed__1;
x_2 = l_Lean_Json_Parser_natNonZero___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNonZero(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_9 = 49;
x_10 = lean_uint32_dec_le(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Json_Parser_natNonZero___closed__2;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 57;
x_14 = lean_uint32_dec_le(x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Json_Parser_natNonZero___closed__2;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Json_Parser_natCore(x_17, x_1);
return x_18;
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_natNumDigits___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("digit", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_natNumDigits___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Json_Parser_lookahead___rarg___closed__1;
x_2 = l_Lean_Json_Parser_natNumDigits___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNumDigits(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_9 = 48;
x_10 = lean_uint32_dec_le(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 57;
x_14 = lean_uint32_dec_le(x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Json_Parser_natCoreNumDigits(x_17, x_17, x_1);
return x_18;
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_natMaybeZero___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("0-9", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_natMaybeZero___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Json_Parser_lookahead___rarg___closed__1;
x_2 = l_Lean_Json_Parser_natMaybeZero___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_9 = 48;
x_10 = lean_uint32_dec_le(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Json_Parser_natMaybeZero___closed__2;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 57;
x_14 = lean_uint32_dec_le(x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Json_Parser_natMaybeZero___closed__2;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Json_Parser_natCore(x_17, x_1);
return x_18;
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_Parser_numSign___closed__1;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numSign(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_2, x_3);
x_9 = 45;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = l_Lean_Json_Parser_numSign___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
x_16 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_16);
x_17 = l_Lean_Json_Parser_numSign___closed__2;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_19 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Json_Parser_numSign___closed__2;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_nat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_2, x_3);
x_9 = 48;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = 49;
x_12 = lean_uint32_dec_le(x_11, x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Json_Parser_natNonZero___closed__2;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 57;
x_16 = lean_uint32_dec_le(x_8, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Json_Parser_natNonZero___closed__2;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Json_Parser_natCore(x_19, x_1);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_24);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_27 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_nat_to_int(x_1);
x_8 = lean_unsigned_to_nat(10u);
x_9 = lean_nat_pow(x_8, x_2);
x_10 = lean_nat_to_int(x_9);
x_11 = lean_int_mul(x_7, x_10);
lean_dec(x_10);
lean_dec(x_7);
x_12 = lean_nat_to_int(x_3);
x_13 = lean_int_add(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = lean_int_mul(x_4, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
static lean_object* _init_l_Lean_Json_Parser_numWithDecimals___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_System_Platform_numBits;
x_3 = lean_nat_pow(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_Parser_numWithDecimals___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("too many decimals", 17, 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_1, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_1, 1);
lean_inc(x_131);
x_132 = lean_string_utf8_byte_size(x_130);
x_133 = lean_nat_dec_lt(x_131, x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_131);
lean_dec(x_130);
x_134 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_1);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
else
{
uint32_t x_136; uint32_t x_137; uint8_t x_138; 
x_136 = lean_string_utf8_get_fast(x_130, x_131);
x_137 = 45;
x_138 = lean_uint32_dec_eq(x_136, x_137);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec(x_131);
lean_dec(x_130);
x_139 = l_Lean_Json_Parser_numSign___closed__1;
x_2 = x_1;
x_3 = x_139;
goto block_129;
}
else
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_1);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_1, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_1, 0);
lean_dec(x_142);
x_143 = lean_string_utf8_next_fast(x_130, x_131);
lean_dec(x_131);
lean_ctor_set(x_1, 1, x_143);
x_144 = l_Lean_Json_Parser_numSign___closed__2;
x_2 = x_1;
x_3 = x_144;
goto block_129;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_1);
x_145 = lean_string_utf8_next_fast(x_130, x_131);
lean_dec(x_131);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_130);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_Json_Parser_numSign___closed__2;
x_2 = x_146;
x_3 = x_147;
goto block_129;
}
}
}
block_129:
{
lean_object* x_4; lean_object* x_5; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_2, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_2, 1);
lean_inc(x_101);
x_102 = lean_string_utf8_byte_size(x_100);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_3);
x_104 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_2);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
else
{
uint32_t x_106; uint32_t x_107; uint8_t x_108; 
x_106 = lean_string_utf8_get_fast(x_100, x_101);
x_107 = 48;
x_108 = lean_uint32_dec_eq(x_106, x_107);
if (x_108 == 0)
{
uint32_t x_109; uint8_t x_110; 
lean_dec(x_101);
lean_dec(x_100);
x_109 = 49;
x_110 = lean_uint32_dec_le(x_109, x_106);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_3);
x_111 = l_Lean_Json_Parser_natNonZero___closed__2;
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_2);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
else
{
uint32_t x_113; uint8_t x_114; 
x_113 = 57;
x_114 = lean_uint32_dec_le(x_106, x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_3);
x_115 = l_Lean_Json_Parser_natNonZero___closed__2;
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_2);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_unsigned_to_nat(0u);
x_118 = l_Lean_Json_Parser_natCore(x_117, x_2);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_4 = x_119;
x_5 = x_120;
goto block_99;
}
}
}
else
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_2);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_2, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_2, 0);
lean_dec(x_123);
x_124 = lean_string_utf8_next_fast(x_100, x_101);
lean_dec(x_101);
lean_ctor_set(x_2, 1, x_124);
x_125 = lean_unsigned_to_nat(0u);
x_4 = x_2;
x_5 = x_125;
goto block_99;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_2);
x_126 = lean_string_utf8_next_fast(x_100, x_101);
lean_dec(x_101);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_100);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_unsigned_to_nat(0u);
x_4 = x_127;
x_5 = x_128;
goto block_99;
}
}
}
block_99:
{
lean_object* x_6; uint8_t x_7; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_4, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_4, 1);
lean_inc(x_94);
x_95 = lean_string_utf8_byte_size(x_93);
lean_dec(x_93);
x_96 = lean_nat_dec_lt(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
uint8_t x_97; 
x_97 = 1;
x_6 = x_4;
x_7 = x_97;
goto block_92;
}
else
{
uint8_t x_98; 
x_98 = 0;
x_6 = x_4;
x_7 = x_98;
goto block_92;
}
block_92:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_12 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint32_t x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_string_utf8_get_fast(x_8, x_9);
x_15 = 46;
x_16 = lean_uint32_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_17 = lean_nat_to_int(x_5);
x_18 = lean_int_mul(x_3, x_17);
lean_dec(x_17);
lean_dec(x_3);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_6, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_6, 0);
lean_dec(x_24);
x_25 = lean_string_utf8_next_fast(x_8, x_9);
lean_dec(x_9);
lean_inc(x_25);
lean_inc(x_8);
lean_ctor_set(x_6, 1, x_25);
x_26 = lean_nat_dec_lt(x_25, x_10);
lean_dec(x_10);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_27 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
else
{
uint32_t x_29; uint32_t x_30; uint8_t x_31; 
x_29 = lean_string_utf8_get_fast(x_8, x_25);
lean_dec(x_25);
lean_dec(x_8);
x_30 = 48;
x_31 = lean_uint32_dec_le(x_30, x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_3);
x_32 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
uint32_t x_34; uint8_t x_35; 
x_34 = 57;
x_35 = lean_uint32_dec_le(x_29, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_5);
lean_dec(x_3);
x_36 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_6);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Json_Parser_natCoreNumDigits(x_38, x_38, x_6);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_39, 1);
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l_Lean_Json_Parser_numWithDecimals___closed__1;
x_46 = lean_nat_dec_lt(x_45, x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_free_object(x_39);
x_47 = lean_box(0);
x_48 = l_Lean_Json_Parser_numWithDecimals___lambda__1(x_5, x_44, x_43, x_3, x_47, x_42);
lean_dec(x_3);
return x_48;
}
else
{
lean_object* x_49; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_3);
x_49 = l_Lean_Json_Parser_numWithDecimals___closed__2;
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 1, x_49);
return x_39;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_39, 1);
x_51 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
lean_inc(x_51);
lean_dec(x_39);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l_Lean_Json_Parser_numWithDecimals___closed__1;
x_55 = lean_nat_dec_lt(x_54, x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_box(0);
x_57 = l_Lean_Json_Parser_numWithDecimals___lambda__1(x_5, x_53, x_52, x_3, x_56, x_51);
lean_dec(x_3);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_5);
lean_dec(x_3);
x_58 = l_Lean_Json_Parser_numWithDecimals___closed__2;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_6);
x_60 = lean_string_utf8_next_fast(x_8, x_9);
lean_dec(x_9);
lean_inc(x_60);
lean_inc(x_8);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_8);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_nat_dec_lt(x_60, x_10);
lean_dec(x_10);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_63 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
else
{
uint32_t x_65; uint32_t x_66; uint8_t x_67; 
x_65 = lean_string_utf8_get_fast(x_8, x_60);
lean_dec(x_60);
lean_dec(x_8);
x_66 = 48;
x_67 = lean_uint32_dec_le(x_66, x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_5);
lean_dec(x_3);
x_68 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
else
{
uint32_t x_70; uint8_t x_71; 
x_70 = 57;
x_71 = lean_uint32_dec_le(x_65, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_5);
lean_dec(x_3);
x_72 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_74 = lean_unsigned_to_nat(0u);
x_75 = l_Lean_Json_Parser_natCoreNumDigits(x_74, x_74, x_61);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = l_Lean_Json_Parser_numWithDecimals___closed__1;
x_82 = lean_nat_dec_lt(x_81, x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_78);
x_83 = lean_box(0);
x_84 = l_Lean_Json_Parser_numWithDecimals___lambda__1(x_5, x_80, x_79, x_3, x_83, x_77);
lean_dec(x_3);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_5);
lean_dec(x_3);
x_85 = l_Lean_Json_Parser_numWithDecimals___closed__2;
if (lean_is_scalar(x_78)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_78;
 lean_ctor_set_tag(x_86, 1);
}
lean_ctor_set(x_86, 0, x_77);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_nat_to_int(x_5);
x_88 = lean_int_mul(x_3, x_87);
lean_dec(x_87);
lean_dec(x_3);
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_6);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Json_Parser_numWithDecimals___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_JsonNumber_shiftl(x_1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Json_Parser_exponent___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exp too large", 13, 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_8 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = lean_string_utf8_get_fast(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_11 = 48;
x_12 = lean_uint32_dec_le(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = l_Lean_Json_Parser_natMaybeZero___closed__2;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 57;
x_16 = lean_uint32_dec_le(x_10, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = l_Lean_Json_Parser_natMaybeZero___closed__2;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Json_Parser_natCore(x_19, x_3);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Lean_Json_Parser_numWithDecimals___closed__1;
x_25 = lean_nat_dec_lt(x_24, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_20);
x_26 = lean_box(0);
x_27 = l_Lean_Json_Parser_exponent___lambda__1(x_1, x_23, x_26, x_22);
lean_dec(x_23);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_1);
x_28 = l_Lean_Json_Parser_exponent___lambda__2___closed__1;
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 1, x_28);
return x_20;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = l_Lean_Json_Parser_numWithDecimals___closed__1;
x_32 = lean_nat_dec_lt(x_31, x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = l_Lean_Json_Parser_exponent___lambda__1(x_1, x_30, x_33, x_29);
lean_dec(x_30);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
lean_dec(x_1);
x_35 = l_Lean_Json_Parser_exponent___lambda__2___closed__1;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_2, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 1);
lean_inc(x_81);
x_82 = lean_string_utf8_byte_size(x_80);
x_83 = lean_nat_dec_lt(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_2);
lean_ctor_set(x_84, 1, x_1);
return x_84;
}
else
{
uint32_t x_85; uint32_t x_86; uint8_t x_87; 
x_85 = lean_string_utf8_get_fast(x_80, x_81);
x_86 = 101;
x_87 = lean_uint32_dec_eq(x_85, x_86);
if (x_87 == 0)
{
uint32_t x_88; uint8_t x_89; 
x_88 = 69;
x_89 = lean_uint32_dec_eq(x_85, x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_2);
lean_ctor_set(x_90, 1, x_1);
return x_90;
}
else
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_2);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_2, 1);
lean_dec(x_92);
x_93 = lean_ctor_get(x_2, 0);
lean_dec(x_93);
x_94 = lean_string_utf8_next_fast(x_80, x_81);
lean_dec(x_81);
lean_inc(x_94);
lean_inc(x_80);
lean_ctor_set(x_2, 1, x_94);
x_95 = lean_nat_dec_lt(x_94, x_82);
lean_dec(x_82);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_94);
lean_dec(x_80);
lean_dec(x_1);
x_96 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_2);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
else
{
uint32_t x_98; 
x_98 = lean_string_utf8_get_fast(x_80, x_94);
lean_dec(x_94);
lean_dec(x_80);
x_3 = x_2;
x_4 = x_98;
goto block_79;
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_2);
x_99 = lean_string_utf8_next_fast(x_80, x_81);
lean_dec(x_81);
lean_inc(x_99);
lean_inc(x_80);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_80);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_nat_dec_lt(x_99, x_82);
lean_dec(x_82);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_99);
lean_dec(x_80);
lean_dec(x_1);
x_102 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
else
{
uint32_t x_104; 
x_104 = lean_string_utf8_get_fast(x_80, x_99);
lean_dec(x_99);
lean_dec(x_80);
x_3 = x_100;
x_4 = x_104;
goto block_79;
}
}
}
}
else
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_2);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_2, 1);
lean_dec(x_106);
x_107 = lean_ctor_get(x_2, 0);
lean_dec(x_107);
x_108 = lean_string_utf8_next_fast(x_80, x_81);
lean_dec(x_81);
lean_inc(x_108);
lean_inc(x_80);
lean_ctor_set(x_2, 1, x_108);
x_109 = lean_nat_dec_lt(x_108, x_82);
lean_dec(x_82);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_108);
lean_dec(x_80);
lean_dec(x_1);
x_110 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_2);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
else
{
uint32_t x_112; 
x_112 = lean_string_utf8_get_fast(x_80, x_108);
lean_dec(x_108);
lean_dec(x_80);
x_3 = x_2;
x_4 = x_112;
goto block_79;
}
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_dec(x_2);
x_113 = lean_string_utf8_next_fast(x_80, x_81);
lean_dec(x_81);
lean_inc(x_113);
lean_inc(x_80);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_80);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_nat_dec_lt(x_113, x_82);
lean_dec(x_82);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_113);
lean_dec(x_80);
lean_dec(x_1);
x_116 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
else
{
uint32_t x_118; 
x_118 = lean_string_utf8_get_fast(x_80, x_113);
lean_dec(x_113);
lean_dec(x_80);
x_3 = x_114;
x_4 = x_118;
goto block_79;
}
}
}
}
block_79:
{
uint32_t x_5; uint8_t x_6; 
x_5 = 45;
x_6 = lean_uint32_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 43;
x_8 = lean_uint32_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Json_Parser_exponent___lambda__2(x_1, x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_string_utf8_byte_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_15 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_3, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 0);
lean_dec(x_19);
x_20 = lean_string_utf8_next_fast(x_11, x_12);
lean_dec(x_12);
lean_ctor_set(x_3, 1, x_20);
x_21 = lean_box(0);
x_22 = l_Lean_Json_Parser_exponent___lambda__2(x_1, x_21, x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
x_23 = lean_string_utf8_next_fast(x_11, x_12);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = l_Lean_Json_Parser_exponent___lambda__2(x_1, x_25, x_24);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
x_29 = lean_string_utf8_byte_size(x_27);
x_30 = lean_nat_dec_lt(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_31 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_3, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_3, 0);
lean_dec(x_35);
x_36 = lean_string_utf8_next_fast(x_27, x_28);
lean_dec(x_28);
lean_inc(x_36);
lean_inc(x_27);
lean_ctor_set(x_3, 1, x_36);
x_37 = lean_nat_dec_lt(x_36, x_29);
lean_dec(x_29);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_1);
x_38 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
uint32_t x_40; uint32_t x_41; uint8_t x_42; 
x_40 = lean_string_utf8_get_fast(x_27, x_36);
lean_dec(x_36);
lean_dec(x_27);
x_41 = 48;
x_42 = lean_uint32_dec_le(x_41, x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_43 = l_Lean_Json_Parser_natMaybeZero___closed__2;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
uint32_t x_45; uint8_t x_46; 
x_45 = 57;
x_46 = lean_uint32_dec_le(x_40, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_47 = l_Lean_Json_Parser_natMaybeZero___closed__2;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_3);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Lean_Json_Parser_natCore(x_49, x_3);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 1);
x_53 = l_Lean_JsonNumber_shiftr(x_1, x_52);
lean_dec(x_52);
lean_ctor_set(x_50, 1, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = l_Lean_JsonNumber_shiftr(x_1, x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_3);
x_58 = lean_string_utf8_next_fast(x_27, x_28);
lean_dec(x_28);
lean_inc(x_58);
lean_inc(x_27);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_27);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_nat_dec_lt(x_58, x_29);
lean_dec(x_29);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_58);
lean_dec(x_27);
lean_dec(x_1);
x_61 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
else
{
uint32_t x_63; uint32_t x_64; uint8_t x_65; 
x_63 = lean_string_utf8_get_fast(x_27, x_58);
lean_dec(x_58);
lean_dec(x_27);
x_64 = 48;
x_65 = lean_uint32_dec_le(x_64, x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_1);
x_66 = l_Lean_Json_Parser_natMaybeZero___closed__2;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
else
{
uint32_t x_68; uint8_t x_69; 
x_68 = 57;
x_69 = lean_uint32_dec_le(x_63, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_1);
x_70 = l_Lean_Json_Parser_natMaybeZero___closed__2;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_unsigned_to_nat(0u);
x_73 = l_Lean_Json_Parser_natCore(x_72, x_59);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = l_Lean_JsonNumber_shiftr(x_1, x_75);
lean_dec(x_75);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Json_Parser_exponent___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Json_Parser_exponent___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_num(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_121; lean_object* x_122; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_253 = lean_ctor_get(x_1, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_1, 1);
lean_inc(x_254);
x_255 = lean_string_utf8_byte_size(x_253);
x_256 = lean_nat_dec_lt(x_254, x_255);
lean_dec(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_254);
lean_dec(x_253);
x_257 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_1);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
else
{
uint32_t x_259; uint32_t x_260; uint8_t x_261; 
x_259 = lean_string_utf8_get_fast(x_253, x_254);
x_260 = 45;
x_261 = lean_uint32_dec_eq(x_259, x_260);
if (x_261 == 0)
{
lean_object* x_262; 
lean_dec(x_254);
lean_dec(x_253);
x_262 = l_Lean_Json_Parser_numSign___closed__1;
x_121 = x_1;
x_122 = x_262;
goto block_252;
}
else
{
uint8_t x_263; 
x_263 = !lean_is_exclusive(x_1);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_1, 1);
lean_dec(x_264);
x_265 = lean_ctor_get(x_1, 0);
lean_dec(x_265);
x_266 = lean_string_utf8_next_fast(x_253, x_254);
lean_dec(x_254);
lean_ctor_set(x_1, 1, x_266);
x_267 = l_Lean_Json_Parser_numSign___closed__2;
x_121 = x_1;
x_122 = x_267;
goto block_252;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_1);
x_268 = lean_string_utf8_next_fast(x_253, x_254);
lean_dec(x_254);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_253);
lean_ctor_set(x_269, 1, x_268);
x_270 = l_Lean_Json_Parser_numSign___closed__2;
x_121 = x_269;
x_122 = x_270;
goto block_252;
}
}
}
block_120:
{
lean_object* x_4; uint32_t x_5; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
x_83 = lean_string_utf8_byte_size(x_81);
x_84 = lean_nat_dec_lt(x_82, x_83);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_2);
lean_ctor_set(x_85, 1, x_3);
return x_85;
}
else
{
uint32_t x_86; uint32_t x_87; uint8_t x_88; 
x_86 = lean_string_utf8_get_fast(x_81, x_82);
x_87 = 101;
x_88 = lean_uint32_dec_eq(x_86, x_87);
if (x_88 == 0)
{
uint32_t x_89; uint8_t x_90; 
x_89 = 69;
x_90 = lean_uint32_dec_eq(x_86, x_89);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_2);
lean_ctor_set(x_91, 1, x_3);
return x_91;
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_2);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_2, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_2, 0);
lean_dec(x_94);
x_95 = lean_string_utf8_next_fast(x_81, x_82);
lean_dec(x_82);
lean_inc(x_95);
lean_inc(x_81);
lean_ctor_set(x_2, 1, x_95);
x_96 = lean_nat_dec_lt(x_95, x_83);
lean_dec(x_83);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_95);
lean_dec(x_81);
lean_dec(x_3);
x_97 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_2);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
else
{
uint32_t x_99; 
x_99 = lean_string_utf8_get_fast(x_81, x_95);
lean_dec(x_95);
lean_dec(x_81);
x_4 = x_2;
x_5 = x_99;
goto block_80;
}
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_2);
x_100 = lean_string_utf8_next_fast(x_81, x_82);
lean_dec(x_82);
lean_inc(x_100);
lean_inc(x_81);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_81);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_nat_dec_lt(x_100, x_83);
lean_dec(x_83);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_100);
lean_dec(x_81);
lean_dec(x_3);
x_103 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
else
{
uint32_t x_105; 
x_105 = lean_string_utf8_get_fast(x_81, x_100);
lean_dec(x_100);
lean_dec(x_81);
x_4 = x_101;
x_5 = x_105;
goto block_80;
}
}
}
}
else
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_2);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_2, 1);
lean_dec(x_107);
x_108 = lean_ctor_get(x_2, 0);
lean_dec(x_108);
x_109 = lean_string_utf8_next_fast(x_81, x_82);
lean_dec(x_82);
lean_inc(x_109);
lean_inc(x_81);
lean_ctor_set(x_2, 1, x_109);
x_110 = lean_nat_dec_lt(x_109, x_83);
lean_dec(x_83);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_109);
lean_dec(x_81);
lean_dec(x_3);
x_111 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_2);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
else
{
uint32_t x_113; 
x_113 = lean_string_utf8_get_fast(x_81, x_109);
lean_dec(x_109);
lean_dec(x_81);
x_4 = x_2;
x_5 = x_113;
goto block_80;
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_2);
x_114 = lean_string_utf8_next_fast(x_81, x_82);
lean_dec(x_82);
lean_inc(x_114);
lean_inc(x_81);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_81);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_nat_dec_lt(x_114, x_83);
lean_dec(x_83);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_114);
lean_dec(x_81);
lean_dec(x_3);
x_117 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
else
{
uint32_t x_119; 
x_119 = lean_string_utf8_get_fast(x_81, x_114);
lean_dec(x_114);
lean_dec(x_81);
x_4 = x_115;
x_5 = x_119;
goto block_80;
}
}
}
}
block_80:
{
uint32_t x_6; uint8_t x_7; 
x_6 = 45;
x_7 = lean_uint32_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 43;
x_9 = lean_uint32_dec_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Json_Parser_exponent___lambda__2(x_3, x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = lean_string_utf8_byte_size(x_12);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_16 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_4, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 0);
lean_dec(x_20);
x_21 = lean_string_utf8_next_fast(x_12, x_13);
lean_dec(x_13);
lean_ctor_set(x_4, 1, x_21);
x_22 = lean_box(0);
x_23 = l_Lean_Json_Parser_exponent___lambda__2(x_3, x_22, x_4);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
x_24 = lean_string_utf8_next_fast(x_12, x_13);
lean_dec(x_13);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = l_Lean_Json_Parser_exponent___lambda__2(x_3, x_26, x_25);
return x_27;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
x_30 = lean_string_utf8_byte_size(x_28);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_3);
x_32 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_4);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_4, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_4, 0);
lean_dec(x_36);
x_37 = lean_string_utf8_next_fast(x_28, x_29);
lean_dec(x_29);
lean_inc(x_37);
lean_inc(x_28);
lean_ctor_set(x_4, 1, x_37);
x_38 = lean_nat_dec_lt(x_37, x_30);
lean_dec(x_30);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_37);
lean_dec(x_28);
lean_dec(x_3);
x_39 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
else
{
uint32_t x_41; uint32_t x_42; uint8_t x_43; 
x_41 = lean_string_utf8_get_fast(x_28, x_37);
lean_dec(x_37);
lean_dec(x_28);
x_42 = 48;
x_43 = lean_uint32_dec_le(x_42, x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_3);
x_44 = l_Lean_Json_Parser_natMaybeZero___closed__2;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
else
{
uint32_t x_46; uint8_t x_47; 
x_46 = 57;
x_47 = lean_uint32_dec_le(x_41, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
x_48 = l_Lean_Json_Parser_natMaybeZero___closed__2;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_4);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_Json_Parser_natCore(x_50, x_4);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 1);
x_54 = l_Lean_JsonNumber_shiftr(x_3, x_53);
lean_dec(x_53);
lean_ctor_set(x_51, 1, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = l_Lean_JsonNumber_shiftr(x_3, x_56);
lean_dec(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_4);
x_59 = lean_string_utf8_next_fast(x_28, x_29);
lean_dec(x_29);
lean_inc(x_59);
lean_inc(x_28);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_28);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_nat_dec_lt(x_59, x_30);
lean_dec(x_30);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_59);
lean_dec(x_28);
lean_dec(x_3);
x_62 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
else
{
uint32_t x_64; uint32_t x_65; uint8_t x_66; 
x_64 = lean_string_utf8_get_fast(x_28, x_59);
lean_dec(x_59);
lean_dec(x_28);
x_65 = 48;
x_66 = lean_uint32_dec_le(x_65, x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_3);
x_67 = l_Lean_Json_Parser_natMaybeZero___closed__2;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
else
{
uint32_t x_69; uint8_t x_70; 
x_69 = 57;
x_70 = lean_uint32_dec_le(x_64, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_3);
x_71 = l_Lean_Json_Parser_natMaybeZero___closed__2;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_60);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Lean_Json_Parser_natCore(x_73, x_60);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = l_Lean_JsonNumber_shiftr(x_3, x_76);
lean_dec(x_76);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
}
}
}
block_252:
{
lean_object* x_123; lean_object* x_124; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_223 = lean_ctor_get(x_121, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_121, 1);
lean_inc(x_224);
x_225 = lean_string_utf8_byte_size(x_223);
x_226 = lean_nat_dec_lt(x_224, x_225);
lean_dec(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_122);
x_227 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_121);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
else
{
uint32_t x_229; uint32_t x_230; uint8_t x_231; 
x_229 = lean_string_utf8_get_fast(x_223, x_224);
x_230 = 48;
x_231 = lean_uint32_dec_eq(x_229, x_230);
if (x_231 == 0)
{
uint32_t x_232; uint8_t x_233; 
lean_dec(x_224);
lean_dec(x_223);
x_232 = 49;
x_233 = lean_uint32_dec_le(x_232, x_229);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_122);
x_234 = l_Lean_Json_Parser_natNonZero___closed__2;
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_121);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
else
{
uint32_t x_236; uint8_t x_237; 
x_236 = 57;
x_237 = lean_uint32_dec_le(x_229, x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_122);
x_238 = l_Lean_Json_Parser_natNonZero___closed__2;
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_121);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_240 = lean_unsigned_to_nat(0u);
x_241 = l_Lean_Json_Parser_natCore(x_240, x_121);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_123 = x_242;
x_124 = x_243;
goto block_222;
}
}
}
else
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_121);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_121, 1);
lean_dec(x_245);
x_246 = lean_ctor_get(x_121, 0);
lean_dec(x_246);
x_247 = lean_string_utf8_next_fast(x_223, x_224);
lean_dec(x_224);
lean_ctor_set(x_121, 1, x_247);
x_248 = lean_unsigned_to_nat(0u);
x_123 = x_121;
x_124 = x_248;
goto block_222;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_121);
x_249 = lean_string_utf8_next_fast(x_223, x_224);
lean_dec(x_224);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_223);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_unsigned_to_nat(0u);
x_123 = x_250;
x_124 = x_251;
goto block_222;
}
}
}
block_222:
{
lean_object* x_125; uint8_t x_126; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_216 = lean_ctor_get(x_123, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_123, 1);
lean_inc(x_217);
x_218 = lean_string_utf8_byte_size(x_216);
lean_dec(x_216);
x_219 = lean_nat_dec_lt(x_217, x_218);
lean_dec(x_218);
lean_dec(x_217);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = 1;
x_125 = x_123;
x_126 = x_220;
goto block_215;
}
else
{
uint8_t x_221; 
x_221 = 0;
x_125 = x_123;
x_126 = x_221;
goto block_215;
}
block_215:
{
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
x_129 = lean_string_utf8_byte_size(x_127);
x_130 = lean_nat_dec_lt(x_128, x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_124);
lean_dec(x_122);
x_131 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_125);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
else
{
uint32_t x_133; uint32_t x_134; uint8_t x_135; 
x_133 = lean_string_utf8_get_fast(x_127, x_128);
x_134 = 46;
x_135 = lean_uint32_dec_eq(x_133, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_136 = lean_nat_to_int(x_124);
x_137 = lean_int_mul(x_122, x_136);
lean_dec(x_136);
lean_dec(x_122);
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_2 = x_125;
x_3 = x_139;
goto block_120;
}
else
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_125);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = lean_ctor_get(x_125, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_125, 0);
lean_dec(x_142);
x_143 = lean_string_utf8_next_fast(x_127, x_128);
lean_dec(x_128);
lean_inc(x_143);
lean_inc(x_127);
lean_ctor_set(x_125, 1, x_143);
x_144 = lean_nat_dec_lt(x_143, x_129);
lean_dec(x_129);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_143);
lean_dec(x_127);
lean_dec(x_124);
lean_dec(x_122);
x_145 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_125);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
else
{
uint32_t x_147; uint32_t x_148; uint8_t x_149; 
x_147 = lean_string_utf8_get_fast(x_127, x_143);
lean_dec(x_143);
lean_dec(x_127);
x_148 = 48;
x_149 = lean_uint32_dec_le(x_148, x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_124);
lean_dec(x_122);
x_150 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_125);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
else
{
uint32_t x_152; uint8_t x_153; 
x_152 = 57;
x_153 = lean_uint32_dec_le(x_147, x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_124);
lean_dec(x_122);
x_154 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_125);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = lean_unsigned_to_nat(0u);
x_157 = l_Lean_Json_Parser_natCoreNumDigits(x_156, x_156, x_125);
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_159 = lean_ctor_get(x_157, 1);
x_160 = lean_ctor_get(x_157, 0);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
x_163 = l_Lean_Json_Parser_numWithDecimals___closed__1;
x_164 = lean_nat_dec_lt(x_163, x_162);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_free_object(x_157);
x_165 = lean_box(0);
x_166 = l_Lean_Json_Parser_numWithDecimals___lambda__1(x_124, x_162, x_161, x_122, x_165, x_160);
lean_dec(x_122);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_2 = x_167;
x_3 = x_168;
goto block_120;
}
else
{
lean_object* x_169; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_124);
lean_dec(x_122);
x_169 = l_Lean_Json_Parser_numWithDecimals___closed__2;
lean_ctor_set_tag(x_157, 1);
lean_ctor_set(x_157, 1, x_169);
return x_157;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_170 = lean_ctor_get(x_157, 1);
x_171 = lean_ctor_get(x_157, 0);
lean_inc(x_170);
lean_inc(x_171);
lean_dec(x_157);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_174 = l_Lean_Json_Parser_numWithDecimals___closed__1;
x_175 = lean_nat_dec_lt(x_174, x_173);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_box(0);
x_177 = l_Lean_Json_Parser_numWithDecimals___lambda__1(x_124, x_173, x_172, x_122, x_176, x_171);
lean_dec(x_122);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_2 = x_178;
x_3 = x_179;
goto block_120;
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_124);
lean_dec(x_122);
x_180 = l_Lean_Json_Parser_numWithDecimals___closed__2;
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_171);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_dec(x_125);
x_182 = lean_string_utf8_next_fast(x_127, x_128);
lean_dec(x_128);
lean_inc(x_182);
lean_inc(x_127);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_127);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_nat_dec_lt(x_182, x_129);
lean_dec(x_129);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_182);
lean_dec(x_127);
lean_dec(x_124);
lean_dec(x_122);
x_185 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
else
{
uint32_t x_187; uint32_t x_188; uint8_t x_189; 
x_187 = lean_string_utf8_get_fast(x_127, x_182);
lean_dec(x_182);
lean_dec(x_127);
x_188 = 48;
x_189 = lean_uint32_dec_le(x_188, x_187);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_124);
lean_dec(x_122);
x_190 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_183);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
else
{
uint32_t x_192; uint8_t x_193; 
x_192 = 57;
x_193 = lean_uint32_dec_le(x_187, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_124);
lean_dec(x_122);
x_194 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_183);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_196 = lean_unsigned_to_nat(0u);
x_197 = l_Lean_Json_Parser_natCoreNumDigits(x_196, x_196, x_183);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_200 = x_197;
} else {
 lean_dec_ref(x_197);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_198, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_198, 1);
lean_inc(x_202);
lean_dec(x_198);
x_203 = l_Lean_Json_Parser_numWithDecimals___closed__1;
x_204 = lean_nat_dec_lt(x_203, x_202);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_200);
x_205 = lean_box(0);
x_206 = l_Lean_Json_Parser_numWithDecimals___lambda__1(x_124, x_202, x_201, x_122, x_205, x_199);
lean_dec(x_122);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_2 = x_207;
x_3 = x_208;
goto block_120;
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_124);
lean_dec(x_122);
x_209 = l_Lean_Json_Parser_numWithDecimals___closed__2;
if (lean_is_scalar(x_200)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_200;
 lean_ctor_set_tag(x_210, 1);
}
lean_ctor_set(x_210, 0, x_199);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
}
}
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_211 = lean_nat_to_int(x_124);
x_212 = lean_int_mul(x_122, x_211);
lean_dec(x_211);
lean_dec(x_122);
x_213 = lean_unsigned_to_nat(0u);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_2 = x_125;
x_3 = x_214;
goto block_120;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_arrayCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected character in array", 29, 29);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_Parser_anyCore(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_push(x_1, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_12 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_12);
return x_3;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_5, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
x_16 = lean_string_utf8_get_fast(x_8, x_9);
x_17 = lean_string_utf8_next_fast(x_8, x_9);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_17);
x_18 = 93;
x_19 = lean_uint32_dec_eq(x_16, x_18);
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 44;
x_21 = lean_uint32_dec_eq(x_16, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_7);
x_22 = l_Lean_Json_Parser_arrayCore___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_22);
return x_3;
}
else
{
lean_object* x_23; 
lean_free_object(x_3);
x_23 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_5);
x_1 = x_7;
x_2 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; 
x_25 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_5);
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_3, 0, x_25);
return x_3;
}
}
else
{
uint32_t x_26; lean_object* x_27; lean_object* x_28; uint32_t x_29; uint8_t x_30; 
lean_dec(x_5);
x_26 = lean_string_utf8_get_fast(x_8, x_9);
x_27 = lean_string_utf8_next_fast(x_8, x_9);
lean_dec(x_9);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_27);
x_29 = 93;
x_30 = lean_uint32_dec_eq(x_26, x_29);
if (x_30 == 0)
{
uint32_t x_31; uint8_t x_32; 
x_31 = 44;
x_32 = lean_uint32_dec_eq(x_26, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_7);
x_33 = l_Lean_Json_Parser_arrayCore___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_33);
lean_ctor_set(x_3, 0, x_28);
return x_3;
}
else
{
lean_object* x_34; 
lean_free_object(x_3);
x_34 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_28);
x_1 = x_7;
x_2 = x_34;
goto _start;
}
}
else
{
lean_object* x_36; 
x_36 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_28);
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_3, 0, x_36);
return x_3;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_ctor_get(x_3, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_3);
x_39 = lean_array_push(x_1, x_38);
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
x_42 = lean_string_utf8_byte_size(x_40);
x_43 = lean_nat_dec_lt(x_41, x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
x_44 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
else
{
lean_object* x_46; uint32_t x_47; lean_object* x_48; lean_object* x_49; uint32_t x_50; uint8_t x_51; 
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_46 = x_37;
} else {
 lean_dec_ref(x_37);
 x_46 = lean_box(0);
}
x_47 = lean_string_utf8_get_fast(x_40, x_41);
x_48 = lean_string_utf8_next_fast(x_40, x_41);
lean_dec(x_41);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_48);
x_50 = 93;
x_51 = lean_uint32_dec_eq(x_47, x_50);
if (x_51 == 0)
{
uint32_t x_52; uint8_t x_53; 
x_52 = 44;
x_53 = lean_uint32_dec_eq(x_47, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_39);
x_54 = l_Lean_Json_Parser_arrayCore___closed__1;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
else
{
lean_object* x_56; 
x_56 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_49);
x_1 = x_39;
x_2 = x_56;
goto _start;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_49);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_39);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_3);
if (x_60 == 0)
{
return x_3;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_3, 0);
x_62 = lean_ctor_get(x_3, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_3);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected input", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_Parser_anyCore___closed__9;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_2, x_3);
x_9 = 91;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 123;
x_12 = lean_uint32_dec_eq(x_8, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 34;
x_14 = lean_uint32_dec_eq(x_8, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = 102;
x_16 = lean_uint32_dec_eq(x_8, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 116;
x_18 = lean_uint32_dec_eq(x_8, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 110;
x_20 = lean_uint32_dec_eq(x_8, x_19);
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 45;
x_22 = lean_uint32_dec_eq(x_8, x_21);
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 48;
x_24 = lean_uint32_dec_le(x_23, x_8);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Json_Parser_anyCore___closed__1;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
uint32_t x_27; uint8_t x_28; 
x_27 = 57;
x_28 = lean_uint32_dec_le(x_8, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Json_Parser_anyCore___closed__1;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = l_Lean_Json_Parser_num(x_1);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_33);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_31, 1, x_36);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_37);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_31);
if (x_42 == 0)
{
return x_31;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 0);
x_44 = lean_ctor_get(x_31, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_31);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
else
{
lean_object* x_46; 
x_46 = l_Lean_Json_Parser_num(x_1);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_48);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_46, 1, x_51);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_46);
x_54 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_52);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_46);
if (x_57 == 0)
{
return x_46;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Json_Parser_anyCore___closed__2;
x_62 = l_Std_Internal_Parsec_String_pstring(x_61, x_1);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
lean_dec(x_65);
x_66 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_64);
x_67 = lean_box(0);
lean_ctor_set(x_62, 1, x_67);
lean_ctor_set(x_62, 0, x_66);
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
lean_dec(x_62);
x_69 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_68);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_62);
if (x_72 == 0)
{
return x_62;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_62, 0);
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_62);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Lean_Json_Parser_anyCore___closed__3;
x_77 = l_Std_Internal_Parsec_String_pstring(x_76, x_1);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
lean_dec(x_80);
x_81 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_79);
x_82 = l_Lean_Json_Parser_anyCore___closed__4;
lean_ctor_set(x_77, 1, x_82);
lean_ctor_set(x_77, 0, x_81);
return x_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
lean_dec(x_77);
x_84 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_83);
x_85 = l_Lean_Json_Parser_anyCore___closed__4;
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_77);
if (x_87 == 0)
{
return x_77;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_77, 0);
x_89 = lean_ctor_get(x_77, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_77);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = l_Lean_Json_Parser_anyCore___closed__5;
x_92 = l_Std_Internal_Parsec_String_pstring(x_91, x_1);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_ctor_get(x_92, 1);
lean_dec(x_95);
x_96 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_94);
x_97 = l_Lean_Json_Parser_anyCore___closed__6;
lean_ctor_set(x_92, 1, x_97);
lean_ctor_set(x_92, 0, x_96);
return x_92;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_92, 0);
lean_inc(x_98);
lean_dec(x_92);
x_99 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_98);
x_100 = l_Lean_Json_Parser_anyCore___closed__6;
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_92);
if (x_102 == 0)
{
return x_92;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_92, 0);
x_104 = lean_ctor_get(x_92, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_92);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
else
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_1);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_1, 1);
lean_dec(x_107);
x_108 = lean_ctor_get(x_1, 0);
lean_dec(x_108);
x_109 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_109);
x_110 = l_Lean_Json_Parser_str___closed__1;
x_111 = l_Lean_Json_Parser_strCore(x_110, x_1);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_ctor_get(x_111, 1);
x_115 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_113);
x_116 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_111, 1, x_116);
lean_ctor_set(x_111, 0, x_115);
return x_111;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_111, 0);
x_118 = lean_ctor_get(x_111, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_111);
x_119 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_117);
x_120 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_120, 0, x_118);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
else
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_111);
if (x_122 == 0)
{
return x_111;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_111, 0);
x_124 = lean_ctor_get(x_111, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_111);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_1);
x_126 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_2);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_Json_Parser_str___closed__1;
x_129 = l_Lean_Json_Parser_strCore(x_128, x_127);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
x_133 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_130);
x_134 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_134, 0, x_131);
if (lean_is_scalar(x_132)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_132;
}
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_129, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_129, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_138 = x_129;
} else {
 lean_dec_ref(x_129);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
}
else
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_1);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_141 = lean_ctor_get(x_1, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_1, 0);
lean_dec(x_142);
x_143 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_143);
x_144 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_1);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
x_147 = lean_string_utf8_byte_size(x_145);
x_148 = lean_nat_dec_lt(x_146, x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_146);
lean_dec(x_145);
x_149 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_144);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
else
{
uint32_t x_151; uint32_t x_152; uint8_t x_153; 
x_151 = lean_string_utf8_get_fast(x_145, x_146);
x_152 = 125;
x_153 = lean_uint32_dec_eq(x_151, x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_146);
lean_dec(x_145);
x_154 = lean_box(0);
x_155 = l_Lean_Json_Parser_objectCore(x_154, x_144);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_155, 1);
x_158 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_155, 1, x_158);
return x_155;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_155, 0);
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_155);
x_161 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_155);
if (x_163 == 0)
{
return x_155;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_155, 0);
x_165 = lean_ctor_get(x_155, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_155);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_144);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_168 = lean_ctor_get(x_144, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_144, 0);
lean_dec(x_169);
x_170 = lean_string_utf8_next_fast(x_145, x_146);
lean_dec(x_146);
lean_ctor_set(x_144, 1, x_170);
x_171 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_144);
x_172 = l_Lean_Json_Parser_anyCore___closed__7;
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_144);
x_174 = lean_string_utf8_next_fast(x_145, x_146);
lean_dec(x_146);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_145);
lean_ctor_set(x_175, 1, x_174);
x_176 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_175);
x_177 = l_Lean_Json_Parser_anyCore___closed__7;
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_1);
x_179 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_2);
lean_ctor_set(x_180, 1, x_179);
x_181 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_180);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
x_184 = lean_string_utf8_byte_size(x_182);
x_185 = lean_nat_dec_lt(x_183, x_184);
lean_dec(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_183);
lean_dec(x_182);
x_186 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_181);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
else
{
uint32_t x_188; uint32_t x_189; uint8_t x_190; 
x_188 = lean_string_utf8_get_fast(x_182, x_183);
x_189 = 125;
x_190 = lean_uint32_dec_eq(x_188, x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_183);
lean_dec(x_182);
x_191 = lean_box(0);
x_192 = l_Lean_Json_Parser_objectCore(x_191, x_181);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_195 = x_192;
} else {
 lean_dec_ref(x_192);
 x_195 = lean_box(0);
}
x_196 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_196, 0, x_194);
if (lean_is_scalar(x_195)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_195;
}
lean_ctor_set(x_197, 0, x_193);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_192, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_192, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_200 = x_192;
} else {
 lean_dec_ref(x_192);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_202 = x_181;
} else {
 lean_dec_ref(x_181);
 x_202 = lean_box(0);
}
x_203 = lean_string_utf8_next_fast(x_182, x_183);
lean_dec(x_183);
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_202;
}
lean_ctor_set(x_204, 0, x_182);
lean_ctor_set(x_204, 1, x_203);
x_205 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_204);
x_206 = l_Lean_Json_Parser_anyCore___closed__7;
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
}
}
else
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_1);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_209 = lean_ctor_get(x_1, 1);
lean_dec(x_209);
x_210 = lean_ctor_get(x_1, 0);
lean_dec(x_210);
x_211 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_211);
x_212 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_1);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
x_215 = lean_string_utf8_byte_size(x_213);
x_216 = lean_nat_dec_lt(x_214, x_215);
lean_dec(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_214);
lean_dec(x_213);
x_217 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_212);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
else
{
uint32_t x_219; uint32_t x_220; uint8_t x_221; 
x_219 = lean_string_utf8_get_fast(x_213, x_214);
x_220 = 93;
x_221 = lean_uint32_dec_eq(x_219, x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_214);
lean_dec(x_213);
x_222 = l_Lean_Json_Parser_anyCore___closed__8;
x_223 = l_Lean_Json_Parser_arrayCore(x_222, x_212);
if (lean_obj_tag(x_223) == 0)
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_223, 1);
x_226 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_223, 1, x_226);
return x_223;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_227 = lean_ctor_get(x_223, 0);
x_228 = lean_ctor_get(x_223, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_223);
x_229 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_229, 0, x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
else
{
uint8_t x_231; 
x_231 = !lean_is_exclusive(x_223);
if (x_231 == 0)
{
return x_223;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_223, 0);
x_233 = lean_ctor_get(x_223, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_223);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
else
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_212);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_ctor_get(x_212, 1);
lean_dec(x_236);
x_237 = lean_ctor_get(x_212, 0);
lean_dec(x_237);
x_238 = lean_string_utf8_next_fast(x_213, x_214);
lean_dec(x_214);
lean_ctor_set(x_212, 1, x_238);
x_239 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_212);
x_240 = l_Lean_Json_Parser_anyCore___closed__10;
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_212);
x_242 = lean_string_utf8_next_fast(x_213, x_214);
lean_dec(x_214);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_213);
lean_ctor_set(x_243, 1, x_242);
x_244 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_243);
x_245 = l_Lean_Json_Parser_anyCore___closed__10;
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
lean_dec(x_1);
x_247 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_2);
lean_ctor_set(x_248, 1, x_247);
x_249 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_248);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
x_252 = lean_string_utf8_byte_size(x_250);
x_253 = lean_nat_dec_lt(x_251, x_252);
lean_dec(x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_251);
lean_dec(x_250);
x_254 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_249);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
else
{
uint32_t x_256; uint32_t x_257; uint8_t x_258; 
x_256 = lean_string_utf8_get_fast(x_250, x_251);
x_257 = 93;
x_258 = lean_uint32_dec_eq(x_256, x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_251);
lean_dec(x_250);
x_259 = l_Lean_Json_Parser_anyCore___closed__8;
x_260 = l_Lean_Json_Parser_arrayCore(x_259, x_249);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_263 = x_260;
} else {
 lean_dec_ref(x_260);
 x_263 = lean_box(0);
}
x_264 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_264, 0, x_262);
if (lean_is_scalar(x_263)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_263;
}
lean_ctor_set(x_265, 0, x_261);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_260, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_260, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_268 = x_260;
} else {
 lean_dec_ref(x_260);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_270 = x_249;
} else {
 lean_dec_ref(x_249);
 x_270 = lean_box(0);
}
x_271 = lean_string_utf8_next_fast(x_250, x_251);
lean_dec(x_251);
if (lean_is_scalar(x_270)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_270;
}
lean_ctor_set(x_272, 0, x_250);
lean_ctor_set(x_272, 1, x_271);
x_273 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_272);
x_274 = l_Lean_Json_Parser_anyCore___closed__10;
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_objectCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_objectCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Json_Parser_lookahead___rarg___closed__1;
x_2 = l_Lean_Json_Parser_objectCore___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_Parser_objectCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_objectCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Json_Parser_lookahead___rarg___closed__1;
x_2 = l_Lean_Json_Parser_objectCore___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_Parser_objectCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected character in object", 30, 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_string_utf8_get_fast(x_3, x_4);
x_10 = 34;
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = l_Lean_Json_Parser_objectCore___closed__2;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 0);
lean_dec(x_16);
x_17 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_17);
x_18 = l_Lean_Json_Parser_str___closed__1;
x_19 = l_Lean_Json_Parser_strCore(x_18, x_2);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = lean_string_utf8_byte_size(x_24);
x_27 = lean_nat_dec_lt(x_25, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_1);
x_28 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_28);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
uint32_t x_29; uint32_t x_30; uint8_t x_31; 
x_29 = lean_string_utf8_get_fast(x_24, x_25);
x_30 = 58;
x_31 = lean_uint32_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_1);
x_32 = l_Lean_Json_Parser_objectCore___closed__4;
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_32);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
uint8_t x_33; 
lean_free_object(x_19);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_23, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_23, 0);
lean_dec(x_35);
x_36 = lean_string_utf8_next_fast(x_24, x_25);
lean_dec(x_25);
lean_ctor_set(x_23, 1, x_36);
x_37 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_23);
x_38 = l_Lean_Json_Parser_anyCore(x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_string_utf8_byte_size(x_42);
x_45 = lean_nat_dec_lt(x_43, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_22);
lean_dec(x_1);
x_46 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_46);
return x_38;
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint32_t x_50; lean_object* x_51; uint32_t x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_40, 1);
lean_dec(x_48);
x_49 = lean_ctor_get(x_40, 0);
lean_dec(x_49);
x_50 = lean_string_utf8_get_fast(x_42, x_43);
x_51 = lean_string_utf8_next_fast(x_42, x_43);
lean_dec(x_43);
lean_ctor_set(x_40, 1, x_51);
x_52 = 125;
x_53 = lean_uint32_dec_eq(x_50, x_52);
if (x_53 == 0)
{
uint32_t x_54; uint8_t x_55; 
x_54 = 44;
x_55 = lean_uint32_dec_eq(x_50, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_41);
lean_dec(x_22);
lean_dec(x_1);
x_56 = l_Lean_Json_Parser_objectCore___closed__5;
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_56);
return x_38;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_free_object(x_38);
x_57 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_40);
x_58 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_1, x_22, x_41);
x_1 = x_58;
x_2 = x_57;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_40);
x_61 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_1, x_22, x_41);
lean_ctor_set(x_38, 1, x_61);
lean_ctor_set(x_38, 0, x_60);
return x_38;
}
}
else
{
uint32_t x_62; lean_object* x_63; lean_object* x_64; uint32_t x_65; uint8_t x_66; 
lean_dec(x_40);
x_62 = lean_string_utf8_get_fast(x_42, x_43);
x_63 = lean_string_utf8_next_fast(x_42, x_43);
lean_dec(x_43);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_42);
lean_ctor_set(x_64, 1, x_63);
x_65 = 125;
x_66 = lean_uint32_dec_eq(x_62, x_65);
if (x_66 == 0)
{
uint32_t x_67; uint8_t x_68; 
x_67 = 44;
x_68 = lean_uint32_dec_eq(x_62, x_67);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_41);
lean_dec(x_22);
lean_dec(x_1);
x_69 = l_Lean_Json_Parser_objectCore___closed__5;
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_69);
lean_ctor_set(x_38, 0, x_64);
return x_38;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_free_object(x_38);
x_70 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_64);
x_71 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_1, x_22, x_41);
x_1 = x_71;
x_2 = x_70;
goto _start;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_64);
x_74 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_1, x_22, x_41);
lean_ctor_set(x_38, 1, x_74);
lean_ctor_set(x_38, 0, x_73);
return x_38;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_38, 0);
x_76 = lean_ctor_get(x_38, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_38);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
x_79 = lean_string_utf8_byte_size(x_77);
x_80 = lean_nat_dec_lt(x_78, x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_22);
lean_dec(x_1);
x_81 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
else
{
lean_object* x_83; uint32_t x_84; lean_object* x_85; lean_object* x_86; uint32_t x_87; uint8_t x_88; 
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_83 = x_75;
} else {
 lean_dec_ref(x_75);
 x_83 = lean_box(0);
}
x_84 = lean_string_utf8_get_fast(x_77, x_78);
x_85 = lean_string_utf8_next_fast(x_77, x_78);
lean_dec(x_78);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_83;
}
lean_ctor_set(x_86, 0, x_77);
lean_ctor_set(x_86, 1, x_85);
x_87 = 125;
x_88 = lean_uint32_dec_eq(x_84, x_87);
if (x_88 == 0)
{
uint32_t x_89; uint8_t x_90; 
x_89 = 44;
x_90 = lean_uint32_dec_eq(x_84, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_76);
lean_dec(x_22);
lean_dec(x_1);
x_91 = l_Lean_Json_Parser_objectCore___closed__5;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_86);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_86);
x_94 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_1, x_22, x_76);
x_1 = x_94;
x_2 = x_93;
goto _start;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_86);
x_97 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_1, x_22, x_76);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_22);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_38);
if (x_99 == 0)
{
return x_38;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_38, 0);
x_101 = lean_ctor_get(x_38, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_38);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_23);
x_103 = lean_string_utf8_next_fast(x_24, x_25);
lean_dec(x_25);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_24);
lean_ctor_set(x_104, 1, x_103);
x_105 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_104);
x_106 = l_Lean_Json_Parser_anyCore(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
x_112 = lean_string_utf8_byte_size(x_110);
x_113 = lean_nat_dec_lt(x_111, x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_22);
lean_dec(x_1);
x_114 = l_Std_Internal_Parsec_unexpectedEndOfInput;
if (lean_is_scalar(x_109)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_109;
 lean_ctor_set_tag(x_115, 1);
}
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
else
{
lean_object* x_116; uint32_t x_117; lean_object* x_118; lean_object* x_119; uint32_t x_120; uint8_t x_121; 
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_116 = x_107;
} else {
 lean_dec_ref(x_107);
 x_116 = lean_box(0);
}
x_117 = lean_string_utf8_get_fast(x_110, x_111);
x_118 = lean_string_utf8_next_fast(x_110, x_111);
lean_dec(x_111);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_110);
lean_ctor_set(x_119, 1, x_118);
x_120 = 125;
x_121 = lean_uint32_dec_eq(x_117, x_120);
if (x_121 == 0)
{
uint32_t x_122; uint8_t x_123; 
x_122 = 44;
x_123 = lean_uint32_dec_eq(x_117, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_108);
lean_dec(x_22);
lean_dec(x_1);
x_124 = l_Lean_Json_Parser_objectCore___closed__5;
if (lean_is_scalar(x_109)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_109;
 lean_ctor_set_tag(x_125, 1);
}
lean_ctor_set(x_125, 0, x_119);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_109);
x_126 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_119);
x_127 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_1, x_22, x_108);
x_1 = x_127;
x_2 = x_126;
goto _start;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_119);
x_130 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_1, x_22, x_108);
if (lean_is_scalar(x_109)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_109;
}
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_22);
lean_dec(x_1);
x_132 = lean_ctor_get(x_106, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_106, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_134 = x_106;
} else {
 lean_dec_ref(x_106);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_136 = lean_ctor_get(x_19, 0);
x_137 = lean_ctor_get(x_19, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_19);
x_138 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_136);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
x_141 = lean_string_utf8_byte_size(x_139);
x_142 = lean_nat_dec_lt(x_140, x_141);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_1);
x_143 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_138);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
else
{
uint32_t x_145; uint32_t x_146; uint8_t x_147; 
x_145 = lean_string_utf8_get_fast(x_139, x_140);
x_146 = 58;
x_147 = lean_uint32_dec_eq(x_145, x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_1);
x_148 = l_Lean_Json_Parser_objectCore___closed__4;
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_138);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_150 = x_138;
} else {
 lean_dec_ref(x_138);
 x_150 = lean_box(0);
}
x_151 = lean_string_utf8_next_fast(x_139, x_140);
lean_dec(x_140);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_150;
}
lean_ctor_set(x_152, 0, x_139);
lean_ctor_set(x_152, 1, x_151);
x_153 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_152);
x_154 = l_Lean_Json_Parser_anyCore(x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_155, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
x_160 = lean_string_utf8_byte_size(x_158);
x_161 = lean_nat_dec_lt(x_159, x_160);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_137);
lean_dec(x_1);
x_162 = l_Std_Internal_Parsec_unexpectedEndOfInput;
if (lean_is_scalar(x_157)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_157;
 lean_ctor_set_tag(x_163, 1);
}
lean_ctor_set(x_163, 0, x_155);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
else
{
lean_object* x_164; uint32_t x_165; lean_object* x_166; lean_object* x_167; uint32_t x_168; uint8_t x_169; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_164 = x_155;
} else {
 lean_dec_ref(x_155);
 x_164 = lean_box(0);
}
x_165 = lean_string_utf8_get_fast(x_158, x_159);
x_166 = lean_string_utf8_next_fast(x_158, x_159);
lean_dec(x_159);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_158);
lean_ctor_set(x_167, 1, x_166);
x_168 = 125;
x_169 = lean_uint32_dec_eq(x_165, x_168);
if (x_169 == 0)
{
uint32_t x_170; uint8_t x_171; 
x_170 = 44;
x_171 = lean_uint32_dec_eq(x_165, x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_156);
lean_dec(x_137);
lean_dec(x_1);
x_172 = l_Lean_Json_Parser_objectCore___closed__5;
if (lean_is_scalar(x_157)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_157;
 lean_ctor_set_tag(x_173, 1);
}
lean_ctor_set(x_173, 0, x_167);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_157);
x_174 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_167);
x_175 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_1, x_137, x_156);
x_1 = x_175;
x_2 = x_174;
goto _start;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_167);
x_178 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_1, x_137, x_156);
if (lean_is_scalar(x_157)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_157;
}
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_137);
lean_dec(x_1);
x_180 = lean_ctor_get(x_154, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_154, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_182 = x_154;
} else {
 lean_dec_ref(x_154);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_19);
if (x_184 == 0)
{
return x_19;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_19, 0);
x_186 = lean_ctor_get(x_19, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_19);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_2);
x_188 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_3);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Lean_Json_Parser_str___closed__1;
x_191 = l_Lean_Json_Parser_strCore(x_190, x_189);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_194 = x_191;
} else {
 lean_dec_ref(x_191);
 x_194 = lean_box(0);
}
x_195 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_192);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
x_198 = lean_string_utf8_byte_size(x_196);
x_199 = lean_nat_dec_lt(x_197, x_198);
lean_dec(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_193);
lean_dec(x_1);
x_200 = l_Std_Internal_Parsec_unexpectedEndOfInput;
if (lean_is_scalar(x_194)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_194;
 lean_ctor_set_tag(x_201, 1);
}
lean_ctor_set(x_201, 0, x_195);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
else
{
uint32_t x_202; uint32_t x_203; uint8_t x_204; 
x_202 = lean_string_utf8_get_fast(x_196, x_197);
x_203 = 58;
x_204 = lean_uint32_dec_eq(x_202, x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_193);
lean_dec(x_1);
x_205 = l_Lean_Json_Parser_objectCore___closed__4;
if (lean_is_scalar(x_194)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_194;
 lean_ctor_set_tag(x_206, 1);
}
lean_ctor_set(x_206, 0, x_195);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_194);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_207 = x_195;
} else {
 lean_dec_ref(x_195);
 x_207 = lean_box(0);
}
x_208 = lean_string_utf8_next_fast(x_196, x_197);
lean_dec(x_197);
if (lean_is_scalar(x_207)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_207;
}
lean_ctor_set(x_209, 0, x_196);
lean_ctor_set(x_209, 1, x_208);
x_210 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_209);
x_211 = l_Lean_Json_Parser_anyCore(x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_214 = x_211;
} else {
 lean_dec_ref(x_211);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_212, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
x_217 = lean_string_utf8_byte_size(x_215);
x_218 = lean_nat_dec_lt(x_216, x_217);
lean_dec(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_193);
lean_dec(x_1);
x_219 = l_Std_Internal_Parsec_unexpectedEndOfInput;
if (lean_is_scalar(x_214)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_214;
 lean_ctor_set_tag(x_220, 1);
}
lean_ctor_set(x_220, 0, x_212);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
else
{
lean_object* x_221; uint32_t x_222; lean_object* x_223; lean_object* x_224; uint32_t x_225; uint8_t x_226; 
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_221 = x_212;
} else {
 lean_dec_ref(x_212);
 x_221 = lean_box(0);
}
x_222 = lean_string_utf8_get_fast(x_215, x_216);
x_223 = lean_string_utf8_next_fast(x_215, x_216);
lean_dec(x_216);
if (lean_is_scalar(x_221)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_221;
}
lean_ctor_set(x_224, 0, x_215);
lean_ctor_set(x_224, 1, x_223);
x_225 = 125;
x_226 = lean_uint32_dec_eq(x_222, x_225);
if (x_226 == 0)
{
uint32_t x_227; uint8_t x_228; 
x_227 = 44;
x_228 = lean_uint32_dec_eq(x_222, x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_213);
lean_dec(x_193);
lean_dec(x_1);
x_229 = l_Lean_Json_Parser_objectCore___closed__5;
if (lean_is_scalar(x_214)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_214;
 lean_ctor_set_tag(x_230, 1);
}
lean_ctor_set(x_230, 0, x_224);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_214);
x_231 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_224);
x_232 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_1, x_193, x_213);
x_1 = x_232;
x_2 = x_231;
goto _start;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_224);
x_235 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_1, x_193, x_213);
if (lean_is_scalar(x_214)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_214;
}
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_193);
lean_dec(x_1);
x_237 = lean_ctor_get(x_211, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_211, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_239 = x_211;
} else {
 lean_dec_ref(x_211);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_1);
x_241 = lean_ctor_get(x_191, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_191, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_243 = x_191;
} else {
 lean_dec_ref(x_191);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_1);
x_3 = l_Lean_Json_Parser_anyCore(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_string_utf8_byte_size(x_7);
lean_dec(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; 
lean_dec(x_6);
x_11 = l_Std_Internal_Parsec_expectedEndOfInput;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_string_utf8_byte_size(x_14);
lean_dec(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_19 = l_Std_Internal_Parsec_expectedEndOfInput;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Json_parse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Json_parse___closed__1;
x_3 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Lean_Data_Json_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_Parser(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Json_Parser_hexChar___closed__1 = _init_l_Lean_Json_Parser_hexChar___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_hexChar___closed__1);
l_Lean_Json_Parser_escapedChar___closed__1 = _init_l_Lean_Json_Parser_escapedChar___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___closed__1);
l_Lean_Json_Parser_escapedChar___boxed__const__1 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__1();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__1);
l_Lean_Json_Parser_escapedChar___boxed__const__2 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__2();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__2);
l_Lean_Json_Parser_escapedChar___boxed__const__3 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__3();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__3);
l_Lean_Json_Parser_escapedChar___boxed__const__4 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__4();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__4);
l_Lean_Json_Parser_escapedChar___boxed__const__5 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__5();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__5);
l_Lean_Json_Parser_escapedChar___boxed__const__6 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__6();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__6);
l_Lean_Json_Parser_escapedChar___boxed__const__7 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__7();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__7);
l_Lean_Json_Parser_escapedChar___boxed__const__8 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__8();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__8);
l_Lean_Json_Parser_strCore___closed__1 = _init_l_Lean_Json_Parser_strCore___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_strCore___closed__1);
l_Lean_Json_Parser_str___closed__1 = _init_l_Lean_Json_Parser_str___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_str___closed__1);
l_Lean_Json_Parser_lookahead___rarg___closed__1 = _init_l_Lean_Json_Parser_lookahead___rarg___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_lookahead___rarg___closed__1);
l_Lean_Json_Parser_natNonZero___closed__1 = _init_l_Lean_Json_Parser_natNonZero___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_natNonZero___closed__1);
l_Lean_Json_Parser_natNonZero___closed__2 = _init_l_Lean_Json_Parser_natNonZero___closed__2();
lean_mark_persistent(l_Lean_Json_Parser_natNonZero___closed__2);
l_Lean_Json_Parser_natNumDigits___closed__1 = _init_l_Lean_Json_Parser_natNumDigits___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_natNumDigits___closed__1);
l_Lean_Json_Parser_natNumDigits___closed__2 = _init_l_Lean_Json_Parser_natNumDigits___closed__2();
lean_mark_persistent(l_Lean_Json_Parser_natNumDigits___closed__2);
l_Lean_Json_Parser_natMaybeZero___closed__1 = _init_l_Lean_Json_Parser_natMaybeZero___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_natMaybeZero___closed__1);
l_Lean_Json_Parser_natMaybeZero___closed__2 = _init_l_Lean_Json_Parser_natMaybeZero___closed__2();
lean_mark_persistent(l_Lean_Json_Parser_natMaybeZero___closed__2);
l_Lean_Json_Parser_numSign___closed__1 = _init_l_Lean_Json_Parser_numSign___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_numSign___closed__1);
l_Lean_Json_Parser_numSign___closed__2 = _init_l_Lean_Json_Parser_numSign___closed__2();
lean_mark_persistent(l_Lean_Json_Parser_numSign___closed__2);
l_Lean_Json_Parser_numWithDecimals___closed__1 = _init_l_Lean_Json_Parser_numWithDecimals___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_numWithDecimals___closed__1);
l_Lean_Json_Parser_numWithDecimals___closed__2 = _init_l_Lean_Json_Parser_numWithDecimals___closed__2();
lean_mark_persistent(l_Lean_Json_Parser_numWithDecimals___closed__2);
l_Lean_Json_Parser_exponent___lambda__2___closed__1 = _init_l_Lean_Json_Parser_exponent___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_exponent___lambda__2___closed__1);
l_Lean_Json_Parser_arrayCore___closed__1 = _init_l_Lean_Json_Parser_arrayCore___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_arrayCore___closed__1);
l_Lean_Json_Parser_anyCore___closed__1 = _init_l_Lean_Json_Parser_anyCore___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___closed__1);
l_Lean_Json_Parser_anyCore___closed__2 = _init_l_Lean_Json_Parser_anyCore___closed__2();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___closed__2);
l_Lean_Json_Parser_anyCore___closed__3 = _init_l_Lean_Json_Parser_anyCore___closed__3();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___closed__3);
l_Lean_Json_Parser_anyCore___closed__4 = _init_l_Lean_Json_Parser_anyCore___closed__4();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___closed__4);
l_Lean_Json_Parser_anyCore___closed__5 = _init_l_Lean_Json_Parser_anyCore___closed__5();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___closed__5);
l_Lean_Json_Parser_anyCore___closed__6 = _init_l_Lean_Json_Parser_anyCore___closed__6();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___closed__6);
l_Lean_Json_Parser_anyCore___closed__7 = _init_l_Lean_Json_Parser_anyCore___closed__7();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___closed__7);
l_Lean_Json_Parser_anyCore___closed__8 = _init_l_Lean_Json_Parser_anyCore___closed__8();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___closed__8);
l_Lean_Json_Parser_anyCore___closed__9 = _init_l_Lean_Json_Parser_anyCore___closed__9();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___closed__9);
l_Lean_Json_Parser_anyCore___closed__10 = _init_l_Lean_Json_Parser_anyCore___closed__10();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___closed__10);
l_Lean_Json_Parser_objectCore___closed__1 = _init_l_Lean_Json_Parser_objectCore___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_objectCore___closed__1);
l_Lean_Json_Parser_objectCore___closed__2 = _init_l_Lean_Json_Parser_objectCore___closed__2();
lean_mark_persistent(l_Lean_Json_Parser_objectCore___closed__2);
l_Lean_Json_Parser_objectCore___closed__3 = _init_l_Lean_Json_Parser_objectCore___closed__3();
lean_mark_persistent(l_Lean_Json_Parser_objectCore___closed__3);
l_Lean_Json_Parser_objectCore___closed__4 = _init_l_Lean_Json_Parser_objectCore___closed__4();
lean_mark_persistent(l_Lean_Json_Parser_objectCore___closed__4);
l_Lean_Json_Parser_objectCore___closed__5 = _init_l_Lean_Json_Parser_objectCore___closed__5();
lean_mark_persistent(l_Lean_Json_Parser_objectCore___closed__5);
l_Lean_Json_parse___closed__1 = _init_l_Lean_Json_parse___closed__1();
lean_mark_persistent(l_Lean_Json_parse___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

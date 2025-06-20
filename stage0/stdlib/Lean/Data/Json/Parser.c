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
static lean_object* l_Lean_Json_Parser_escapedChar___closed__0;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Json_Parser_exponent___closed__0;
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_Lean_Json_Parser_natNonZero___closed__0;
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
static lean_object* l_Lean_Json_Parser_any___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_shiftr(lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_strCore___closed__0;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__4;
static lean_object* l_Lean_Json_Parser_anyCore___closed__5;
static lean_object* l_Lean_Json_Parser_numSign___closed__1;
static lean_object* l_Lean_Json_Parser_numWithDecimals___closed__1;
static lean_object* l_Lean_Json_Parser_objectCore___closed__0;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNumDigits(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_hexChar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_numWithDecimals___closed__0;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__7;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__3;
lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_anyCore___closed__6;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar(lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCoreNumDigits(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Json_Parser_arrayCore___closed__0;
lean_object* l_Lean_JsonNumber_shiftl(lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_anyCore___closed__4;
static lean_object* l_Lean_Json_Parser_numSign___closed__0;
uint16_t lean_uint32_to_uint16(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_natNumDigits___closed__0;
static lean_object* l_Lean_Json_Parser_objectCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent(lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_anyCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__5;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNonZero(lean_object*);
extern lean_object* l_System_Platform_numBits;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_finishSurrogatePair___closed__0;
static lean_object* l_Lean_Json_Parser_natMaybeZero___closed__0;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_sub(uint32_t, uint32_t);
static lean_object* l_Lean_Json_Parser_objectCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__9;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_strCore(lean_object*, lean_object*);
uint16_t lean_uint16_lor(uint16_t, uint16_t);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_anyCore___closed__0;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lean_Json_Parser_anyCore___closed__7;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_num(lean_object*);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_anyCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numSign(lean_object*);
lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__1;
uint32_t lean_uint32_land(uint32_t, uint32_t);
static lean_object* l_Lean_Json_Parser_hexChar___closed__0;
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_nat(lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
static lean_object* l_Lean_Json_Parser_hexChar___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Json_Parser_anyCore___closed__2;
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_str(lean_object*);
static lean_object* l_Lean_Json_Parser_lookahead___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint16_t lean_uint16_shift_left(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__8;
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__6;
uint32_t lean_uint16_to_uint32(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair(uint16_t, lean_object*);
static lean_object* _init_l_Lean_Json_Parser_hexChar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
return x_1;
}
}
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
x_6 = l_Lean_Json_Parser_hexChar___closed__0;
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
lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; uint32_t x_24; uint8_t x_25; uint32_t x_37; uint8_t x_38; uint8_t x_48; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_string_utf8_get_fast(x_2, x_3);
x_12 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_12);
x_37 = 48;
x_48 = lean_uint32_dec_le(x_37, x_11);
if (x_48 == 0)
{
x_38 = x_48;
goto block_47;
}
else
{
uint32_t x_49; uint8_t x_50; 
x_49 = 57;
x_50 = lean_uint32_dec_le(x_11, x_49);
x_38 = x_50;
goto block_47;
}
block_23:
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Json_Parser_hexChar___closed__1;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
uint32_t x_17; uint32_t x_18; uint32_t x_19; uint16_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_uint32_sub(x_11, x_13);
x_18 = 10;
x_19 = lean_uint32_add(x_17, x_18);
x_20 = lean_uint32_to_uint16(x_19);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
block_36:
{
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = 65;
x_27 = lean_uint32_dec_le(x_26, x_11);
if (x_27 == 0)
{
x_13 = x_26;
x_14 = x_27;
goto block_23;
}
else
{
uint32_t x_28; uint8_t x_29; 
x_28 = 70;
x_29 = lean_uint32_dec_le(x_11, x_28);
x_13 = x_26;
x_14 = x_29;
goto block_23;
}
}
else
{
uint32_t x_30; uint32_t x_31; uint32_t x_32; uint16_t x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_uint32_sub(x_11, x_24);
x_31 = 10;
x_32 = lean_uint32_add(x_30, x_31);
x_33 = lean_uint32_to_uint16(x_32);
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
block_47:
{
if (x_38 == 0)
{
uint32_t x_39; uint8_t x_40; 
x_39 = 97;
x_40 = lean_uint32_dec_le(x_39, x_11);
if (x_40 == 0)
{
x_24 = x_39;
x_25 = x_40;
goto block_36;
}
else
{
uint32_t x_41; uint8_t x_42; 
x_41 = 102;
x_42 = lean_uint32_dec_le(x_11, x_41);
x_24 = x_39;
x_25 = x_42;
goto block_36;
}
}
else
{
uint32_t x_43; uint16_t x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_uint32_sub(x_11, x_37);
x_44 = lean_uint32_to_uint16(x_43);
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint32_t x_51; lean_object* x_52; lean_object* x_53; uint32_t x_54; uint8_t x_55; uint32_t x_65; uint8_t x_66; uint32_t x_78; uint8_t x_79; uint8_t x_89; 
lean_dec(x_1);
x_51 = lean_string_utf8_get_fast(x_2, x_3);
x_52 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set(x_53, 1, x_52);
x_78 = 48;
x_89 = lean_uint32_dec_le(x_78, x_51);
if (x_89 == 0)
{
x_79 = x_89;
goto block_88;
}
else
{
uint32_t x_90; uint8_t x_91; 
x_90 = 57;
x_91 = lean_uint32_dec_le(x_51, x_90);
x_79 = x_91;
goto block_88;
}
block_64:
{
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lean_Json_Parser_hexChar___closed__1;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
else
{
uint32_t x_58; uint32_t x_59; uint32_t x_60; uint16_t x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_uint32_sub(x_51, x_54);
x_59 = 10;
x_60 = lean_uint32_add(x_58, x_59);
x_61 = lean_uint32_to_uint16(x_60);
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
block_77:
{
if (x_66 == 0)
{
uint32_t x_67; uint8_t x_68; 
x_67 = 65;
x_68 = lean_uint32_dec_le(x_67, x_51);
if (x_68 == 0)
{
x_54 = x_67;
x_55 = x_68;
goto block_64;
}
else
{
uint32_t x_69; uint8_t x_70; 
x_69 = 70;
x_70 = lean_uint32_dec_le(x_51, x_69);
x_54 = x_67;
x_55 = x_70;
goto block_64;
}
}
else
{
uint32_t x_71; uint32_t x_72; uint32_t x_73; uint16_t x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_uint32_sub(x_51, x_65);
x_72 = 10;
x_73 = lean_uint32_add(x_71, x_72);
x_74 = lean_uint32_to_uint16(x_73);
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_53);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
block_88:
{
if (x_79 == 0)
{
uint32_t x_80; uint8_t x_81; 
x_80 = 97;
x_81 = lean_uint32_dec_le(x_80, x_51);
if (x_81 == 0)
{
x_65 = x_80;
x_66 = x_81;
goto block_77;
}
else
{
uint32_t x_82; uint8_t x_83; 
x_82 = 102;
x_83 = lean_uint32_dec_le(x_51, x_82);
x_65 = x_80;
x_66 = x_83;
goto block_77;
}
}
else
{
uint32_t x_84; uint16_t x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_uint32_sub(x_51, x_78);
x_85 = lean_uint32_to_uint16(x_84);
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_53);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_finishSurrogatePair___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair(uint16_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; lean_object* x_98; uint32_t x_99; uint8_t x_100; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_121; 
x_106 = lean_ctor_get(x_2, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_2, 1);
lean_inc(x_107);
x_108 = lean_string_utf8_byte_size(x_106);
x_121 = lean_nat_dec_lt(x_107, x_108);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
x_122 = l_Lean_Json_Parser_hexChar___closed__0;
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_2);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_2);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint32_t x_127; lean_object* x_128; uint8_t x_129; uint32_t x_141; uint8_t x_142; 
x_125 = lean_ctor_get(x_2, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_2, 0);
lean_dec(x_126);
x_127 = lean_string_utf8_get_fast(x_106, x_107);
x_128 = lean_string_utf8_next_fast(x_106, x_107);
lean_dec(x_107);
lean_inc(x_128);
lean_inc(x_106);
lean_ctor_set(x_2, 1, x_128);
x_141 = 92;
x_142 = lean_uint32_dec_eq(x_127, x_141);
if (x_142 == 0)
{
if (x_121 == 0)
{
x_129 = x_121;
goto block_140;
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_128);
lean_dec(x_108);
lean_dec(x_106);
x_143 = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_2);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
else
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_box(0);
x_146 = lean_unbox(x_145);
x_129 = x_146;
goto block_140;
}
block_140:
{
uint8_t x_130; 
x_130 = lean_nat_dec_lt(x_128, x_108);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_128);
lean_dec(x_108);
lean_dec(x_106);
x_131 = l_Lean_Json_Parser_hexChar___closed__0;
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_2);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
else
{
uint32_t x_133; lean_object* x_134; lean_object* x_135; uint32_t x_136; uint8_t x_137; 
lean_dec(x_2);
x_133 = lean_string_utf8_get_fast(x_106, x_128);
x_134 = lean_string_utf8_next_fast(x_106, x_128);
lean_dec(x_128);
lean_inc(x_134);
lean_inc(x_106);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_106);
lean_ctor_set(x_135, 1, x_134);
x_136 = 117;
x_137 = lean_uint32_dec_eq(x_133, x_136);
if (x_137 == 0)
{
if (x_130 == 0)
{
x_109 = x_134;
x_110 = x_135;
x_111 = x_130;
goto block_120;
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_134);
lean_dec(x_108);
lean_dec(x_106);
x_138 = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
else
{
x_109 = x_134;
x_110 = x_135;
x_111 = x_129;
goto block_120;
}
}
}
}
else
{
uint32_t x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; uint32_t x_162; uint8_t x_163; 
lean_dec(x_2);
x_147 = lean_string_utf8_get_fast(x_106, x_107);
x_148 = lean_string_utf8_next_fast(x_106, x_107);
lean_dec(x_107);
lean_inc(x_148);
lean_inc(x_106);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_106);
lean_ctor_set(x_149, 1, x_148);
x_162 = 92;
x_163 = lean_uint32_dec_eq(x_147, x_162);
if (x_163 == 0)
{
if (x_121 == 0)
{
x_150 = x_121;
goto block_161;
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_148);
lean_dec(x_108);
lean_dec(x_106);
x_164 = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_149);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
else
{
lean_object* x_166; uint8_t x_167; 
x_166 = lean_box(0);
x_167 = lean_unbox(x_166);
x_150 = x_167;
goto block_161;
}
block_161:
{
uint8_t x_151; 
x_151 = lean_nat_dec_lt(x_148, x_108);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_148);
lean_dec(x_108);
lean_dec(x_106);
x_152 = l_Lean_Json_Parser_hexChar___closed__0;
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
else
{
uint32_t x_154; lean_object* x_155; lean_object* x_156; uint32_t x_157; uint8_t x_158; 
lean_dec(x_149);
x_154 = lean_string_utf8_get_fast(x_106, x_148);
x_155 = lean_string_utf8_next_fast(x_106, x_148);
lean_dec(x_148);
lean_inc(x_155);
lean_inc(x_106);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_106);
lean_ctor_set(x_156, 1, x_155);
x_157 = 117;
x_158 = lean_uint32_dec_eq(x_154, x_157);
if (x_158 == 0)
{
if (x_151 == 0)
{
x_109 = x_155;
x_110 = x_156;
x_111 = x_151;
goto block_120;
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_155);
lean_dec(x_108);
lean_dec(x_106);
x_159 = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
else
{
x_109 = x_155;
x_110 = x_156;
x_111 = x_150;
goto block_120;
}
}
}
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
block_97:
{
lean_object* x_8; 
x_8 = l_Lean_Json_Parser_hexChar(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Json_Parser_hexChar(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Json_Parser_hexChar(x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint16_t x_18; uint16_t x_19; uint16_t x_20; uint16_t x_21; uint16_t x_22; uint16_t x_23; uint16_t x_24; uint16_t x_25; uint16_t x_26; uint16_t x_27; uint8_t x_28; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = 8;
x_19 = lean_unbox(x_10);
lean_dec(x_10);
x_20 = lean_uint16_shift_left(x_19, x_18);
x_21 = 4;
x_22 = lean_unbox(x_13);
lean_dec(x_13);
x_23 = lean_uint16_shift_left(x_22, x_21);
x_24 = lean_uint16_lor(x_20, x_23);
x_25 = lean_unbox(x_17);
lean_dec(x_17);
x_26 = lean_uint16_lor(x_24, x_25);
x_27 = 3072;
x_28 = lean_uint16_dec_lt(x_26, x_27);
if (x_28 == 0)
{
uint32_t x_29; uint32_t x_30; uint32_t x_31; uint32_t x_32; uint32_t x_33; uint32_t x_34; uint32_t x_35; uint32_t x_36; uint32_t x_37; uint32_t x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_29 = lean_uint16_to_uint32(x_1);
x_30 = 1023;
x_31 = lean_uint32_land(x_29, x_30);
x_32 = 10;
x_33 = lean_uint32_shift_left(x_31, x_32);
x_34 = lean_uint16_to_uint32(x_26);
x_35 = lean_uint32_land(x_34, x_30);
x_36 = lean_uint32_lor(x_33, x_35);
x_37 = 65536;
x_38 = lean_uint32_add(x_36, x_37);
x_39 = lean_uint32_to_nat(x_38);
x_40 = lean_unsigned_to_nat(55296u);
x_41 = lean_nat_dec_lt(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_unsigned_to_nat(57343u);
x_43 = lean_nat_dec_lt(x_42, x_39);
if (x_43 == 0)
{
lean_dec(x_39);
lean_free_object(x_14);
x_3 = x_16;
goto block_6;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_unsigned_to_nat(1114112u);
x_45 = lean_nat_dec_lt(x_39, x_44);
lean_dec(x_39);
if (x_45 == 0)
{
lean_free_object(x_14);
x_3 = x_16;
goto block_6;
}
else
{
lean_object* x_46; 
x_46 = lean_box_uint32(x_38);
lean_ctor_set(x_14, 1, x_46);
return x_14;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_39);
x_47 = lean_box_uint32(x_38);
lean_ctor_set(x_14, 1, x_47);
return x_14;
}
}
else
{
lean_object* x_48; 
x_48 = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_48);
return x_14;
}
}
else
{
lean_object* x_49; lean_object* x_50; uint16_t x_51; uint16_t x_52; uint16_t x_53; uint16_t x_54; uint16_t x_55; uint16_t x_56; uint16_t x_57; uint16_t x_58; uint16_t x_59; uint16_t x_60; uint8_t x_61; 
x_49 = lean_ctor_get(x_14, 0);
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_14);
x_51 = 8;
x_52 = lean_unbox(x_10);
lean_dec(x_10);
x_53 = lean_uint16_shift_left(x_52, x_51);
x_54 = 4;
x_55 = lean_unbox(x_13);
lean_dec(x_13);
x_56 = lean_uint16_shift_left(x_55, x_54);
x_57 = lean_uint16_lor(x_53, x_56);
x_58 = lean_unbox(x_50);
lean_dec(x_50);
x_59 = lean_uint16_lor(x_57, x_58);
x_60 = 3072;
x_61 = lean_uint16_dec_lt(x_59, x_60);
if (x_61 == 0)
{
uint32_t x_62; uint32_t x_63; uint32_t x_64; uint32_t x_65; uint32_t x_66; uint32_t x_67; uint32_t x_68; uint32_t x_69; uint32_t x_70; uint32_t x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_62 = lean_uint16_to_uint32(x_1);
x_63 = 1023;
x_64 = lean_uint32_land(x_62, x_63);
x_65 = 10;
x_66 = lean_uint32_shift_left(x_64, x_65);
x_67 = lean_uint16_to_uint32(x_59);
x_68 = lean_uint32_land(x_67, x_63);
x_69 = lean_uint32_lor(x_66, x_68);
x_70 = 65536;
x_71 = lean_uint32_add(x_69, x_70);
x_72 = lean_uint32_to_nat(x_71);
x_73 = lean_unsigned_to_nat(55296u);
x_74 = lean_nat_dec_lt(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_unsigned_to_nat(57343u);
x_76 = lean_nat_dec_lt(x_75, x_72);
if (x_76 == 0)
{
lean_dec(x_72);
x_3 = x_49;
goto block_6;
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_unsigned_to_nat(1114112u);
x_78 = lean_nat_dec_lt(x_72, x_77);
lean_dec(x_72);
if (x_78 == 0)
{
x_3 = x_49;
goto block_6;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_box_uint32(x_71);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_49);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_72);
x_81 = lean_box_uint32(x_71);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_49);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_49);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_13);
lean_dec(x_10);
x_85 = !lean_is_exclusive(x_14);
if (x_85 == 0)
{
return x_14;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_14, 0);
x_87 = lean_ctor_get(x_14, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_14);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_10);
x_89 = !lean_is_exclusive(x_11);
if (x_89 == 0)
{
return x_11;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_11, 0);
x_91 = lean_ctor_get(x_11, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_11);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_8);
if (x_93 == 0)
{
return x_8;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_8, 0);
x_95 = lean_ctor_get(x_8, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_8);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
block_105:
{
if (x_100 == 0)
{
x_7 = x_98;
goto block_97;
}
else
{
uint32_t x_101; uint8_t x_102; 
x_101 = 68;
x_102 = lean_uint32_dec_eq(x_99, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_98);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
else
{
x_7 = x_98;
goto block_97;
}
}
}
block_120:
{
uint8_t x_112; 
x_112 = lean_nat_dec_lt(x_109, x_108);
lean_dec(x_108);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_109);
lean_dec(x_106);
x_113 = l_Lean_Json_Parser_hexChar___closed__0;
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
else
{
uint32_t x_115; lean_object* x_116; lean_object* x_117; uint32_t x_118; uint8_t x_119; 
lean_dec(x_110);
x_115 = lean_string_utf8_get_fast(x_106, x_109);
x_116 = lean_string_utf8_next_fast(x_106, x_109);
lean_dec(x_109);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_106);
lean_ctor_set(x_117, 1, x_116);
x_118 = 100;
x_119 = lean_uint32_dec_eq(x_115, x_118);
if (x_119 == 0)
{
x_98 = x_117;
x_99 = x_115;
x_100 = x_112;
goto block_105;
}
else
{
x_98 = x_117;
x_99 = x_115;
x_100 = x_111;
goto block_105;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Json_Parser_finishSurrogatePair(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___closed__0() {
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
x_1 = 65533;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 9;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__3() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 13;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__4() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__5() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 12;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__6() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 8;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__7() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__8() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 34;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__9() {
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
x_6 = l_Lean_Json_Parser_hexChar___closed__0;
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
x_31 = l_Lean_Json_Parser_escapedChar___closed__0;
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
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = l_Lean_Json_Parser_hexChar(x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint16_t x_55; uint16_t x_56; uint16_t x_57; uint16_t x_58; uint16_t x_59; uint16_t x_60; uint16_t x_61; uint16_t x_62; uint16_t x_63; uint16_t x_64; uint16_t x_65; uint16_t x_66; uint16_t x_67; uint16_t x_68; uint8_t x_69; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_55 = 12;
x_56 = lean_unbox(x_35);
lean_dec(x_35);
x_57 = lean_uint16_shift_left(x_56, x_55);
x_58 = 8;
x_59 = lean_unbox(x_38);
lean_dec(x_38);
x_60 = lean_uint16_shift_left(x_59, x_58);
x_61 = lean_uint16_lor(x_57, x_60);
x_62 = 4;
x_63 = lean_unbox(x_42);
lean_dec(x_42);
x_64 = lean_uint16_shift_left(x_63, x_62);
x_65 = lean_uint16_lor(x_61, x_64);
x_66 = lean_unbox(x_45);
lean_dec(x_45);
x_67 = lean_uint16_lor(x_65, x_66);
x_68 = 55296;
x_69 = lean_uint16_dec_lt(x_67, x_68);
if (x_69 == 0)
{
uint16_t x_70; uint8_t x_71; 
x_70 = 57344;
x_71 = lean_uint16_dec_lt(x_67, x_70);
if (x_71 == 0)
{
uint32_t x_72; lean_object* x_73; 
lean_dec(x_46);
x_72 = lean_uint16_to_uint32(x_67);
x_73 = lean_box_uint32(x_72);
lean_ctor_set(x_39, 1, x_73);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
uint16_t x_74; uint8_t x_75; 
x_74 = 56320;
x_75 = lean_uint16_dec_lt(x_67, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_46);
x_76 = l_Lean_Json_Parser_escapedChar___boxed__const__1;
lean_ctor_set(x_39, 1, x_76);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_77; 
lean_free_object(x_39);
lean_inc(x_44);
x_77 = l_Lean_Json_Parser_finishSurrogatePair(x_67, x_44);
if (lean_obj_tag(x_77) == 0)
{
if (lean_obj_tag(x_77) == 0)
{
lean_dec(x_46);
lean_dec(x_44);
return x_77;
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_47 = x_77;
x_48 = x_78;
goto block_54;
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_77);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_77, 0);
lean_dec(x_80);
lean_inc(x_44);
lean_ctor_set(x_77, 0, x_44);
lean_inc(x_44);
x_47 = x_77;
x_48 = x_44;
goto block_54;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec(x_77);
lean_inc(x_44);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_44);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_44);
x_47 = x_82;
x_48 = x_44;
goto block_54;
}
}
}
}
}
else
{
uint32_t x_83; lean_object* x_84; 
lean_dec(x_46);
x_83 = lean_uint16_to_uint32(x_67);
x_84 = lean_box_uint32(x_83);
lean_ctor_set(x_39, 1, x_84);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
block_54:
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_dec(x_44);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
x_51 = lean_nat_dec_eq(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_dec(x_48);
lean_dec(x_46);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_47);
x_52 = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (lean_is_scalar(x_46)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_46;
}
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_85; 
lean_free_object(x_39);
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_35);
x_85 = !lean_is_exclusive(x_43);
if (x_85 == 0)
{
return x_43;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_43, 0);
x_87 = lean_ctor_get(x_43, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_43);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_39, 0);
x_90 = lean_ctor_get(x_39, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_39);
x_91 = l_Lean_Json_Parser_hexChar(x_89);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint16_t x_103; uint16_t x_104; uint16_t x_105; uint16_t x_106; uint16_t x_107; uint16_t x_108; uint16_t x_109; uint16_t x_110; uint16_t x_111; uint16_t x_112; uint16_t x_113; uint16_t x_114; uint16_t x_115; uint16_t x_116; uint8_t x_117; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_103 = 12;
x_104 = lean_unbox(x_35);
lean_dec(x_35);
x_105 = lean_uint16_shift_left(x_104, x_103);
x_106 = 8;
x_107 = lean_unbox(x_38);
lean_dec(x_38);
x_108 = lean_uint16_shift_left(x_107, x_106);
x_109 = lean_uint16_lor(x_105, x_108);
x_110 = 4;
x_111 = lean_unbox(x_90);
lean_dec(x_90);
x_112 = lean_uint16_shift_left(x_111, x_110);
x_113 = lean_uint16_lor(x_109, x_112);
x_114 = lean_unbox(x_93);
lean_dec(x_93);
x_115 = lean_uint16_lor(x_113, x_114);
x_116 = 55296;
x_117 = lean_uint16_dec_lt(x_115, x_116);
if (x_117 == 0)
{
uint16_t x_118; uint8_t x_119; 
x_118 = 57344;
x_119 = lean_uint16_dec_lt(x_115, x_118);
if (x_119 == 0)
{
uint32_t x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_94);
x_120 = lean_uint16_to_uint32(x_115);
x_121 = lean_box_uint32(x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_92);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
else
{
uint16_t x_123; uint8_t x_124; 
x_123 = 56320;
x_124 = lean_uint16_dec_lt(x_115, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_94);
x_125 = l_Lean_Json_Parser_escapedChar___boxed__const__1;
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_92);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
else
{
lean_object* x_127; 
lean_inc(x_92);
x_127 = l_Lean_Json_Parser_finishSurrogatePair(x_115, x_92);
if (lean_obj_tag(x_127) == 0)
{
if (lean_obj_tag(x_127) == 0)
{
lean_dec(x_94);
lean_dec(x_92);
return x_127;
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_95 = x_127;
x_96 = x_128;
goto block_102;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
lean_inc(x_92);
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_92);
lean_ctor_set(x_131, 1, x_129);
lean_inc(x_92);
x_95 = x_131;
x_96 = x_92;
goto block_102;
}
}
}
}
else
{
uint32_t x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_94);
x_132 = lean_uint16_to_uint32(x_115);
x_133 = lean_box_uint32(x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_92);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
block_102:
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
lean_dec(x_92);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
x_99 = lean_nat_dec_eq(x_97, x_98);
lean_dec(x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_dec(x_96);
lean_dec(x_94);
return x_95;
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_95);
x_100 = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (lean_is_scalar(x_94)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_94;
}
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_90);
lean_dec(x_38);
lean_dec(x_35);
x_135 = lean_ctor_get(x_91, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_91, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_137 = x_91;
} else {
 lean_dec_ref(x_91);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_38);
lean_dec(x_35);
x_139 = !lean_is_exclusive(x_39);
if (x_139 == 0)
{
return x_39;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_39, 0);
x_141 = lean_ctor_get(x_39, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_39);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_35);
x_143 = !lean_is_exclusive(x_36);
if (x_143 == 0)
{
return x_36;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_36, 0);
x_145 = lean_ctor_get(x_36, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_36);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_33);
if (x_147 == 0)
{
return x_33;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_33, 0);
x_149 = lean_ctor_get(x_33, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_33);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = l_Lean_Json_Parser_escapedChar___boxed__const__2;
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_1);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = l_Lean_Json_Parser_escapedChar___boxed__const__3;
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_1);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = l_Lean_Json_Parser_escapedChar___boxed__const__4;
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_1);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = l_Lean_Json_Parser_escapedChar___boxed__const__5;
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_1);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = l_Lean_Json_Parser_escapedChar___boxed__const__6;
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_1);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = l_Lean_Json_Parser_escapedChar___boxed__const__7;
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_1);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Lean_Json_Parser_escapedChar___boxed__const__8;
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_1);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Lean_Json_Parser_escapedChar___boxed__const__9;
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_1);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
uint32_t x_167; lean_object* x_168; lean_object* x_169; uint32_t x_170; uint8_t x_171; 
lean_dec(x_1);
x_167 = lean_string_utf8_get_fast(x_2, x_3);
x_168 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_2);
lean_ctor_set(x_169, 1, x_168);
x_170 = 92;
x_171 = lean_uint32_dec_eq(x_167, x_170);
if (x_171 == 0)
{
uint32_t x_172; uint8_t x_173; 
x_172 = 34;
x_173 = lean_uint32_dec_eq(x_167, x_172);
if (x_173 == 0)
{
uint32_t x_174; uint8_t x_175; 
x_174 = 47;
x_175 = lean_uint32_dec_eq(x_167, x_174);
if (x_175 == 0)
{
uint32_t x_176; uint8_t x_177; 
x_176 = 98;
x_177 = lean_uint32_dec_eq(x_167, x_176);
if (x_177 == 0)
{
uint32_t x_178; uint8_t x_179; 
x_178 = 102;
x_179 = lean_uint32_dec_eq(x_167, x_178);
if (x_179 == 0)
{
uint32_t x_180; uint8_t x_181; 
x_180 = 110;
x_181 = lean_uint32_dec_eq(x_167, x_180);
if (x_181 == 0)
{
uint32_t x_182; uint8_t x_183; 
x_182 = 114;
x_183 = lean_uint32_dec_eq(x_167, x_182);
if (x_183 == 0)
{
uint32_t x_184; uint8_t x_185; 
x_184 = 116;
x_185 = lean_uint32_dec_eq(x_167, x_184);
if (x_185 == 0)
{
uint32_t x_186; uint8_t x_187; 
x_186 = 117;
x_187 = lean_uint32_dec_eq(x_167, x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = l_Lean_Json_Parser_escapedChar___closed__0;
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_169);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
else
{
lean_object* x_190; 
x_190 = l_Lean_Json_Parser_hexChar(x_169);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l_Lean_Json_Parser_hexChar(x_191);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l_Lean_Json_Parser_hexChar(x_194);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
x_200 = l_Lean_Json_Parser_hexChar(x_197);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint16_t x_212; uint16_t x_213; uint16_t x_214; uint16_t x_215; uint16_t x_216; uint16_t x_217; uint16_t x_218; uint16_t x_219; uint16_t x_220; uint16_t x_221; uint16_t x_222; uint16_t x_223; uint16_t x_224; uint16_t x_225; uint8_t x_226; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_203 = x_200;
} else {
 lean_dec_ref(x_200);
 x_203 = lean_box(0);
}
x_212 = 12;
x_213 = lean_unbox(x_192);
lean_dec(x_192);
x_214 = lean_uint16_shift_left(x_213, x_212);
x_215 = 8;
x_216 = lean_unbox(x_195);
lean_dec(x_195);
x_217 = lean_uint16_shift_left(x_216, x_215);
x_218 = lean_uint16_lor(x_214, x_217);
x_219 = 4;
x_220 = lean_unbox(x_198);
lean_dec(x_198);
x_221 = lean_uint16_shift_left(x_220, x_219);
x_222 = lean_uint16_lor(x_218, x_221);
x_223 = lean_unbox(x_202);
lean_dec(x_202);
x_224 = lean_uint16_lor(x_222, x_223);
x_225 = 55296;
x_226 = lean_uint16_dec_lt(x_224, x_225);
if (x_226 == 0)
{
uint16_t x_227; uint8_t x_228; 
x_227 = 57344;
x_228 = lean_uint16_dec_lt(x_224, x_227);
if (x_228 == 0)
{
uint32_t x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_203);
x_229 = lean_uint16_to_uint32(x_224);
x_230 = lean_box_uint32(x_229);
if (lean_is_scalar(x_199)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_199;
}
lean_ctor_set(x_231, 0, x_201);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
else
{
uint16_t x_232; uint8_t x_233; 
x_232 = 56320;
x_233 = lean_uint16_dec_lt(x_224, x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_203);
x_234 = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (lean_is_scalar(x_199)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_199;
}
lean_ctor_set(x_235, 0, x_201);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
else
{
lean_object* x_236; 
lean_dec(x_199);
lean_inc(x_201);
x_236 = l_Lean_Json_Parser_finishSurrogatePair(x_224, x_201);
if (lean_obj_tag(x_236) == 0)
{
if (lean_obj_tag(x_236) == 0)
{
lean_dec(x_203);
lean_dec(x_201);
return x_236;
}
else
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_204 = x_236;
x_205 = x_237;
goto block_211;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_239 = x_236;
} else {
 lean_dec_ref(x_236);
 x_239 = lean_box(0);
}
lean_inc(x_201);
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_201);
lean_ctor_set(x_240, 1, x_238);
lean_inc(x_201);
x_204 = x_240;
x_205 = x_201;
goto block_211;
}
}
}
}
else
{
uint32_t x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_203);
x_241 = lean_uint16_to_uint32(x_224);
x_242 = lean_box_uint32(x_241);
if (lean_is_scalar(x_199)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_199;
}
lean_ctor_set(x_243, 0, x_201);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
block_211:
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
lean_dec(x_201);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
x_208 = lean_nat_dec_eq(x_206, x_207);
lean_dec(x_207);
lean_dec(x_206);
if (x_208 == 0)
{
lean_dec(x_205);
lean_dec(x_203);
return x_204;
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_204);
x_209 = l_Lean_Json_Parser_escapedChar___boxed__const__1;
if (lean_is_scalar(x_203)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_203;
}
lean_ctor_set(x_210, 0, x_205);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_195);
lean_dec(x_192);
x_244 = lean_ctor_get(x_200, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_200, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_246 = x_200;
} else {
 lean_dec_ref(x_200);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_195);
lean_dec(x_192);
x_248 = lean_ctor_get(x_196, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_196, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_250 = x_196;
} else {
 lean_dec_ref(x_196);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_192);
x_252 = lean_ctor_get(x_193, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_193, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_254 = x_193;
} else {
 lean_dec_ref(x_193);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = lean_ctor_get(x_190, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_190, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_258 = x_190;
} else {
 lean_dec_ref(x_190);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = l_Lean_Json_Parser_escapedChar___boxed__const__2;
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_169);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; 
x_262 = l_Lean_Json_Parser_escapedChar___boxed__const__3;
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_169);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; 
x_264 = l_Lean_Json_Parser_escapedChar___boxed__const__4;
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_169);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
else
{
lean_object* x_266; lean_object* x_267; 
x_266 = l_Lean_Json_Parser_escapedChar___boxed__const__5;
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_169);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; 
x_268 = l_Lean_Json_Parser_escapedChar___boxed__const__6;
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_169);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; 
x_270 = l_Lean_Json_Parser_escapedChar___boxed__const__7;
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_169);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; 
x_272 = l_Lean_Json_Parser_escapedChar___boxed__const__8;
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_169);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
else
{
lean_object* x_274; lean_object* x_275; 
x_274 = l_Lean_Json_Parser_escapedChar___boxed__const__9;
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_169);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_strCore___closed__0() {
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
x_7 = l_Lean_Json_Parser_hexChar___closed__0;
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
if (x_6 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = l_Lean_Json_Parser_hexChar___closed__0;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint32_t x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_2, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 0);
lean_dec(x_16);
x_17 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_17);
x_24 = 92;
x_25 = lean_uint32_dec_eq(x_9, x_24);
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = 32;
x_27 = lean_uint32_dec_le(x_26, x_9);
if (x_27 == 0)
{
x_18 = x_27;
goto block_23;
}
else
{
uint32_t x_28; uint8_t x_29; 
x_28 = 1114111;
x_29 = lean_uint32_dec_le(x_9, x_28);
x_18 = x_29;
goto block_23;
}
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Json_Parser_escapedChar(x_2);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint32_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unbox_uint32(x_32);
lean_dec(x_32);
x_34 = lean_string_push(x_1, x_33);
x_1 = x_34;
x_2 = x_31;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
block_23:
{
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = l_Lean_Json_Parser_strCore___closed__0;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_string_push(x_1, x_9);
x_1 = x_21;
goto _start;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint32_t x_48; uint8_t x_49; 
lean_dec(x_2);
x_40 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_3);
lean_ctor_set(x_41, 1, x_40);
x_48 = 92;
x_49 = lean_uint32_dec_eq(x_9, x_48);
if (x_49 == 0)
{
uint32_t x_50; uint8_t x_51; 
x_50 = 32;
x_51 = lean_uint32_dec_le(x_50, x_9);
if (x_51 == 0)
{
x_42 = x_51;
goto block_47;
}
else
{
uint32_t x_52; uint8_t x_53; 
x_52 = 1114111;
x_53 = lean_uint32_dec_le(x_9, x_52);
x_42 = x_53;
goto block_47;
}
}
else
{
lean_object* x_54; 
x_54 = l_Lean_Json_Parser_escapedChar(x_41);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; uint32_t x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unbox_uint32(x_56);
lean_dec(x_56);
x_58 = lean_string_push(x_1, x_57);
x_1 = x_58;
x_2 = x_55;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_1);
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_62 = x_54;
} else {
 lean_dec_ref(x_54);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
block_47:
{
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_43 = l_Lean_Json_Parser_strCore___closed__0;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; 
x_45 = lean_string_push(x_1, x_9);
x_1 = x_45;
x_2 = x_41;
goto _start;
}
}
}
}
}
else
{
if (x_6 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = l_Lean_Json_Parser_hexChar___closed__0;
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_2);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_2, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_2, 0);
lean_dec(x_68);
x_69 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_69);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_2);
lean_ctor_set(x_70, 1, x_1);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_2);
x_71 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_3);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_1);
return x_73;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_str(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
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
if (x_6 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = l_Lean_Json_Parser_hexChar___closed__0;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; uint8_t x_35; 
x_10 = lean_string_utf8_get_fast(x_3, x_4);
x_11 = 48;
x_35 = lean_uint32_dec_le(x_11, x_10);
if (x_35 == 0)
{
x_12 = x_35;
goto block_34;
}
else
{
uint32_t x_36; uint8_t x_37; 
x_36 = 57;
x_37 = lean_uint32_dec_le(x_10, x_36);
x_12 = x_37;
goto block_34;
}
block_34:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
return x_13;
}
else
{
if (x_6 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = l_Lean_Json_Parser_hexChar___closed__0;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint32_t x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_2, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_2, 0);
lean_dec(x_18);
x_19 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_19);
x_20 = lean_unsigned_to_nat(10u);
x_21 = lean_nat_mul(x_20, x_1);
lean_dec(x_1);
x_22 = lean_uint32_sub(x_10, x_11);
x_23 = lean_uint32_to_nat(x_22);
x_24 = lean_nat_add(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
x_1 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_26 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_unsigned_to_nat(10u);
x_29 = lean_nat_mul(x_28, x_1);
lean_dec(x_1);
x_30 = lean_uint32_sub(x_10, x_11);
x_31 = lean_uint32_to_nat(x_30);
x_32 = lean_nat_add(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
x_1 = x_32;
x_2 = x_27;
goto _start;
}
}
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
if (x_7 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_Json_Parser_hexChar___closed__0;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
uint32_t x_12; uint32_t x_13; uint8_t x_14; uint8_t x_42; 
x_12 = lean_string_utf8_get_fast(x_4, x_5);
x_13 = 48;
x_42 = lean_uint32_dec_le(x_13, x_12);
if (x_42 == 0)
{
x_14 = x_42;
goto block_41;
}
else
{
uint32_t x_43; uint8_t x_44; 
x_43 = 57;
x_44 = lean_uint32_dec_le(x_12, x_43);
x_14 = x_44;
goto block_41;
}
block_41:
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
if (x_7 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Json_Parser_hexChar___closed__0;
x_18 = lean_alloc_ctor(1, 2, 0);
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
x_25 = lean_uint32_sub(x_12, x_13);
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
x_35 = lean_uint32_sub(x_12, x_13);
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
}
}
static lean_object* _init_l_Lean_Json_Parser_lookahead___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected ", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_Json_Parser_hexChar___closed__0;
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
x_14 = l_Lean_Json_Parser_lookahead___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_byte_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_9 = l_Lean_Json_Parser_hexChar___closed__0;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint32_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_string_utf8_get_fast(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_12 = lean_box_uint32(x_11);
x_13 = lean_apply_1(x_3, x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Json_Parser_lookahead___redArg___closed__0;
x_16 = lean_string_append(x_15, x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Json_Parser_lookahead___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Json_Parser_lookahead(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Json_Parser_natNonZero___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected 1-9", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNonZero(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
x_12 = l_Lean_Json_Parser_hexChar___closed__0;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint32_t x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_string_utf8_get_fast(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_15 = 49;
x_16 = lean_uint32_dec_le(x_15, x_14);
if (x_16 == 0)
{
x_2 = x_16;
goto block_7;
}
else
{
uint32_t x_17; uint8_t x_18; 
x_17 = 57;
x_18 = lean_uint32_dec_le(x_14, x_17);
x_2 = x_18;
goto block_7;
}
}
block_7:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_Parser_natNonZero___closed__0;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Json_Parser_natCore(x_5, x_1);
return x_6;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_natNumDigits___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected digit", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNumDigits(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
x_12 = l_Lean_Json_Parser_hexChar___closed__0;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint32_t x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_string_utf8_get_fast(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_15 = 48;
x_16 = lean_uint32_dec_le(x_15, x_14);
if (x_16 == 0)
{
x_2 = x_16;
goto block_7;
}
else
{
uint32_t x_17; uint8_t x_18; 
x_17 = 57;
x_18 = lean_uint32_dec_le(x_14, x_17);
x_2 = x_18;
goto block_7;
}
}
block_7:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_Parser_natNumDigits___closed__0;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Json_Parser_natCoreNumDigits(x_5, x_5, x_1);
return x_6;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_natMaybeZero___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected 0-9", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
x_12 = l_Lean_Json_Parser_hexChar___closed__0;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint32_t x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_string_utf8_get_fast(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_15 = 48;
x_16 = lean_uint32_dec_le(x_15, x_14);
if (x_16 == 0)
{
x_2 = x_16;
goto block_7;
}
else
{
uint32_t x_17; uint8_t x_18; 
x_17 = 57;
x_18 = lean_uint32_dec_le(x_14, x_17);
x_2 = x_18;
goto block_7;
}
}
block_7:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_Parser_natMaybeZero___closed__0;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Json_Parser_natCore(x_5, x_1);
return x_6;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_numSign___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_Parser_numSign___closed__0;
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
x_6 = l_Lean_Json_Parser_hexChar___closed__0;
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
x_11 = l_Lean_Json_Parser_numSign___closed__0;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
if (x_5 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = l_Lean_Json_Parser_hexChar___closed__0;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_18 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_18);
x_19 = l_Lean_Json_Parser_numSign___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_21 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Json_Parser_numSign___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_nat(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
x_12 = l_Lean_Json_Parser_hexChar___closed__0;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint32_t x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_string_utf8_get_fast(x_8, x_9);
x_15 = 48;
x_16 = lean_uint32_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Json_Parser_hexChar___closed__0;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
uint32_t x_19; uint8_t x_20; 
x_19 = 49;
x_20 = lean_uint32_dec_le(x_19, x_14);
if (x_20 == 0)
{
x_2 = x_20;
goto block_7;
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 57;
x_22 = lean_uint32_dec_le(x_14, x_21);
x_2 = x_22;
goto block_7;
}
}
}
else
{
if (x_11 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_8);
x_23 = l_Lean_Json_Parser_hexChar___closed__0;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_1, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_1, 0);
lean_dec(x_27);
x_28 = lean_string_utf8_next_fast(x_8, x_9);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_28);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_31 = lean_string_utf8_next_fast(x_8, x_9);
lean_dec(x_9);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
block_7:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_Parser_natNonZero___closed__0;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Json_Parser_natCore(x_5, x_1);
return x_6;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_numWithDecimals___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_Platform_numBits;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_pow(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_Parser_numWithDecimals___closed__1() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_136 = lean_ctor_get(x_1, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_1, 1);
lean_inc(x_137);
x_138 = lean_string_utf8_byte_size(x_136);
x_139 = lean_nat_dec_lt(x_137, x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_137);
lean_dec(x_136);
x_140 = l_Lean_Json_Parser_hexChar___closed__0;
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_1);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
else
{
uint32_t x_142; uint32_t x_143; uint8_t x_144; 
x_142 = lean_string_utf8_get_fast(x_136, x_137);
x_143 = 45;
x_144 = lean_uint32_dec_eq(x_142, x_143);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = l_Lean_Json_Parser_numSign___closed__0;
x_113 = x_1;
x_114 = x_136;
x_115 = x_137;
x_116 = x_145;
goto block_135;
}
else
{
if (x_139 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_137);
lean_dec(x_136);
x_146 = l_Lean_Json_Parser_hexChar___closed__0;
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_1);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
else
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_1);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_1, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_1, 0);
lean_dec(x_150);
x_151 = lean_string_utf8_next_fast(x_136, x_137);
lean_dec(x_137);
lean_inc(x_151);
lean_inc(x_136);
lean_ctor_set(x_1, 1, x_151);
x_152 = l_Lean_Json_Parser_numSign___closed__1;
x_113 = x_1;
x_114 = x_136;
x_115 = x_151;
x_116 = x_152;
goto block_135;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_1);
x_153 = lean_string_utf8_next_fast(x_136, x_137);
lean_dec(x_137);
lean_inc(x_153);
lean_inc(x_136);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_136);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_Json_Parser_numSign___closed__1;
x_113 = x_154;
x_114 = x_136;
x_115 = x_153;
x_116 = x_155;
goto block_135;
}
}
}
}
block_63:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = l_Lean_Json_Parser_natNumDigits___closed__0;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Json_Parser_natCoreNumDigits(x_8, x_8, x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Json_Parser_numWithDecimals___closed__0;
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_nat_to_int(x_4);
x_18 = lean_unsigned_to_nat(10u);
x_19 = lean_nat_pow(x_18, x_14);
x_20 = lean_nat_to_int(x_19);
x_21 = lean_int_mul(x_17, x_20);
lean_dec(x_20);
lean_dec(x_17);
x_22 = lean_nat_to_int(x_13);
x_23 = lean_int_add(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
x_24 = lean_int_mul(x_3, x_23);
lean_dec(x_23);
lean_dec(x_3);
lean_ctor_set(x_11, 0, x_24);
return x_9;
}
else
{
lean_object* x_25; 
lean_free_object(x_11);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
x_25 = l_Lean_Json_Parser_numWithDecimals___closed__1;
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_25);
return x_9;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = l_Lean_Json_Parser_numWithDecimals___closed__0;
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_nat_to_int(x_4);
x_31 = lean_unsigned_to_nat(10u);
x_32 = lean_nat_pow(x_31, x_27);
x_33 = lean_nat_to_int(x_32);
x_34 = lean_int_mul(x_30, x_33);
lean_dec(x_33);
lean_dec(x_30);
x_35 = lean_nat_to_int(x_26);
x_36 = lean_int_add(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
x_37 = lean_int_mul(x_3, x_36);
lean_dec(x_36);
lean_dec(x_3);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_27);
lean_ctor_set(x_9, 1, x_38);
return x_9;
}
else
{
lean_object* x_39; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
x_39 = l_Lean_Json_Parser_numWithDecimals___closed__1;
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_39);
return x_9;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_ctor_get(x_9, 1);
x_41 = lean_ctor_get(x_9, 0);
lean_inc(x_40);
lean_inc(x_41);
lean_dec(x_9);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_44 = x_40;
} else {
 lean_dec_ref(x_40);
 x_44 = lean_box(0);
}
x_45 = l_Lean_Json_Parser_numWithDecimals___closed__0;
x_46 = lean_nat_dec_lt(x_45, x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_nat_to_int(x_4);
x_48 = lean_unsigned_to_nat(10u);
x_49 = lean_nat_pow(x_48, x_43);
x_50 = lean_nat_to_int(x_49);
x_51 = lean_int_mul(x_47, x_50);
lean_dec(x_50);
lean_dec(x_47);
x_52 = lean_nat_to_int(x_42);
x_53 = lean_int_add(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
x_54 = lean_int_mul(x_3, x_53);
lean_dec(x_53);
lean_dec(x_3);
if (lean_is_scalar(x_44)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_44;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_43);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_41);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_4);
lean_dec(x_3);
x_57 = l_Lean_Json_Parser_numWithDecimals___closed__1;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_41);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_4);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_9);
if (x_59 == 0)
{
return x_9;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_9, 0);
x_61 = lean_ctor_get(x_9, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_9);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
block_96:
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_string_utf8_byte_size(x_66);
x_70 = lean_nat_dec_lt(x_67, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_66);
x_71 = lean_nat_to_int(x_68);
x_72 = lean_int_mul(x_64, x_71);
lean_dec(x_71);
lean_dec(x_64);
x_73 = l_Lean_JsonNumber_fromInt(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
else
{
if (x_70 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
x_75 = l_Lean_Json_Parser_hexChar___closed__0;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
else
{
uint32_t x_77; uint32_t x_78; uint8_t x_79; 
x_77 = lean_string_utf8_get_fast(x_66, x_67);
x_78 = 46;
x_79 = lean_uint32_dec_eq(x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_66);
x_80 = lean_nat_to_int(x_68);
x_81 = lean_int_mul(x_64, x_80);
lean_dec(x_80);
lean_dec(x_64);
x_82 = l_Lean_JsonNumber_fromInt(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_65);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
else
{
if (x_70 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
x_84 = l_Lean_Json_Parser_hexChar___closed__0;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_65);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_65);
x_86 = lean_string_utf8_next_fast(x_66, x_67);
lean_dec(x_67);
lean_inc(x_86);
lean_inc(x_66);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_66);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_nat_dec_lt(x_86, x_69);
lean_dec(x_69);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_86);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_64);
x_89 = l_Lean_Json_Parser_hexChar___closed__0;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
else
{
uint32_t x_91; uint32_t x_92; uint8_t x_93; 
x_91 = lean_string_utf8_get_fast(x_66, x_86);
lean_dec(x_86);
lean_dec(x_66);
x_92 = 48;
x_93 = lean_uint32_dec_le(x_92, x_91);
if (x_93 == 0)
{
x_2 = x_87;
x_3 = x_64;
x_4 = x_68;
x_5 = x_93;
goto block_63;
}
else
{
uint32_t x_94; uint8_t x_95; 
x_94 = 57;
x_95 = lean_uint32_dec_le(x_91, x_94);
x_2 = x_87;
x_3 = x_64;
x_4 = x_68;
x_5 = x_95;
goto block_63;
}
}
}
}
}
}
}
block_112:
{
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_98);
x_100 = l_Lean_Json_Parser_natNonZero___closed__0;
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_unsigned_to_nat(0u);
x_103 = l_Lean_Json_Parser_natCore(x_102, x_97);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
x_64 = x_98;
x_65 = x_104;
x_66 = x_106;
x_67 = x_107;
x_68 = x_105;
goto block_96;
}
else
{
uint8_t x_108; 
lean_dec(x_98);
x_108 = !lean_is_exclusive(x_103);
if (x_108 == 0)
{
return x_103;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_103, 0);
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_103);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
block_135:
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_string_utf8_byte_size(x_114);
x_118 = lean_nat_dec_lt(x_115, x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
x_119 = l_Lean_Json_Parser_hexChar___closed__0;
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
else
{
uint32_t x_121; uint32_t x_122; uint8_t x_123; 
x_121 = lean_string_utf8_get_fast(x_114, x_115);
x_122 = 48;
x_123 = lean_uint32_dec_eq(x_121, x_122);
if (x_123 == 0)
{
lean_dec(x_115);
lean_dec(x_114);
if (x_118 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_116);
x_124 = l_Lean_Json_Parser_hexChar___closed__0;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_113);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
else
{
uint32_t x_126; uint8_t x_127; 
x_126 = 49;
x_127 = lean_uint32_dec_le(x_126, x_121);
if (x_127 == 0)
{
x_97 = x_113;
x_98 = x_116;
x_99 = x_127;
goto block_112;
}
else
{
uint32_t x_128; uint8_t x_129; 
x_128 = 57;
x_129 = lean_uint32_dec_le(x_121, x_128);
x_97 = x_113;
x_98 = x_116;
x_99 = x_129;
goto block_112;
}
}
}
else
{
if (x_118 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
x_130 = l_Lean_Json_Parser_hexChar___closed__0;
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_113);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_113);
x_132 = lean_string_utf8_next_fast(x_114, x_115);
lean_dec(x_115);
lean_inc(x_132);
lean_inc(x_114);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_114);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_unsigned_to_nat(0u);
x_64 = x_116;
x_65 = x_133;
x_66 = x_114;
x_67 = x_132;
x_68 = x_134;
goto block_96;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_exponent___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exp too large", 13, 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_41; uint8_t x_42; lean_object* x_59; lean_object* x_60; lean_object* x_120; uint8_t x_121; 
x_59 = lean_ctor_get(x_2, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_2, 1);
lean_inc(x_60);
x_120 = lean_string_utf8_byte_size(x_59);
x_121 = lean_nat_dec_lt(x_60, x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_60);
lean_dec(x_59);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_2);
lean_ctor_set(x_122, 1, x_1);
return x_122;
}
else
{
if (x_121 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_1);
x_123 = l_Lean_Json_Parser_hexChar___closed__0;
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_2);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
else
{
uint32_t x_125; uint32_t x_126; uint8_t x_127; 
x_125 = lean_string_utf8_get_fast(x_59, x_60);
x_126 = 101;
x_127 = lean_uint32_dec_eq(x_125, x_126);
if (x_127 == 0)
{
uint32_t x_128; uint8_t x_129; 
x_128 = 69;
x_129 = lean_uint32_dec_eq(x_125, x_128);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_60);
lean_dec(x_59);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_2);
lean_ctor_set(x_130, 1, x_1);
return x_130;
}
else
{
goto block_119;
}
}
else
{
goto block_119;
}
}
}
block_27:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Lean_Json_Parser_natMaybeZero___closed__0;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Json_Parser_natCore(x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = l_Lean_Json_Parser_numWithDecimals___closed__0;
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_JsonNumber_shiftl(x_1, x_10);
lean_dec(x_10);
lean_ctor_set(x_8, 1, x_13);
return x_8;
}
else
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_1);
x_14 = l_Lean_Json_Parser_exponent___closed__0;
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_14);
return x_8;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = l_Lean_Json_Parser_numWithDecimals___closed__0;
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_JsonNumber_shiftl(x_1, x_16);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_1);
x_21 = l_Lean_Json_Parser_exponent___closed__0;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
block_40:
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_string_utf8_byte_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_1);
x_33 = l_Lean_Json_Parser_hexChar___closed__0;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
else
{
uint32_t x_35; uint32_t x_36; uint8_t x_37; 
x_35 = lean_string_utf8_get_fast(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
x_36 = 48;
x_37 = lean_uint32_dec_le(x_36, x_35);
if (x_37 == 0)
{
x_3 = x_28;
x_4 = x_37;
goto block_27;
}
else
{
uint32_t x_38; uint8_t x_39; 
x_38 = 57;
x_39 = lean_uint32_dec_le(x_35, x_38);
x_3 = x_28;
x_4 = x_39;
goto block_27;
}
}
}
block_58:
{
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_43 = l_Lean_Json_Parser_natMaybeZero___closed__0;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Lean_Json_Parser_natCore(x_45, x_41);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 1);
x_49 = l_Lean_JsonNumber_shiftr(x_1, x_48);
lean_dec(x_48);
lean_ctor_set(x_46, 1, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = l_Lean_JsonNumber_shiftr(x_1, x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_46);
if (x_54 == 0)
{
return x_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_46, 0);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
block_119:
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_string_utf8_byte_size(x_59);
x_62 = lean_nat_dec_lt(x_60, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_1);
x_63 = l_Lean_Json_Parser_hexChar___closed__0;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_2);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_2, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_2, 0);
lean_dec(x_67);
x_68 = lean_string_utf8_next_fast(x_59, x_60);
lean_dec(x_60);
lean_inc(x_68);
lean_inc(x_59);
lean_ctor_set(x_2, 1, x_68);
x_69 = lean_nat_dec_lt(x_68, x_61);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_68);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_1);
x_70 = l_Lean_Json_Parser_hexChar___closed__0;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_2);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
else
{
uint32_t x_72; uint32_t x_73; uint8_t x_74; 
x_72 = lean_string_utf8_get_fast(x_59, x_68);
x_73 = 45;
x_74 = lean_uint32_dec_eq(x_72, x_73);
if (x_74 == 0)
{
uint32_t x_75; uint8_t x_76; 
lean_dec(x_61);
x_75 = 43;
x_76 = lean_uint32_dec_eq(x_72, x_75);
if (x_76 == 0)
{
x_28 = x_2;
x_29 = x_59;
x_30 = x_68;
goto block_40;
}
else
{
if (x_69 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_68);
lean_dec(x_59);
lean_dec(x_1);
x_77 = l_Lean_Json_Parser_hexChar___closed__0;
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_2);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_2);
x_79 = lean_string_utf8_next_fast(x_59, x_68);
lean_dec(x_68);
lean_inc(x_79);
lean_inc(x_59);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_59);
lean_ctor_set(x_80, 1, x_79);
x_28 = x_80;
x_29 = x_59;
x_30 = x_79;
goto block_40;
}
}
}
else
{
if (x_69 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_68);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_1);
x_81 = l_Lean_Json_Parser_hexChar___closed__0;
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_2);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_2);
x_83 = lean_string_utf8_next_fast(x_59, x_68);
lean_dec(x_68);
lean_inc(x_83);
lean_inc(x_59);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_59);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_nat_dec_lt(x_83, x_61);
lean_dec(x_61);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_83);
lean_dec(x_59);
lean_dec(x_1);
x_86 = l_Lean_Json_Parser_hexChar___closed__0;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
else
{
uint32_t x_88; uint32_t x_89; uint8_t x_90; 
x_88 = lean_string_utf8_get_fast(x_59, x_83);
lean_dec(x_83);
lean_dec(x_59);
x_89 = 48;
x_90 = lean_uint32_dec_le(x_89, x_88);
if (x_90 == 0)
{
x_41 = x_84;
x_42 = x_90;
goto block_58;
}
else
{
uint32_t x_91; uint8_t x_92; 
x_91 = 57;
x_92 = lean_uint32_dec_le(x_88, x_91);
x_41 = x_84;
x_42 = x_92;
goto block_58;
}
}
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_2);
x_93 = lean_string_utf8_next_fast(x_59, x_60);
lean_dec(x_60);
lean_inc(x_93);
lean_inc(x_59);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_59);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_nat_dec_lt(x_93, x_61);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_93);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_1);
x_96 = l_Lean_Json_Parser_hexChar___closed__0;
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
else
{
uint32_t x_98; uint32_t x_99; uint8_t x_100; 
x_98 = lean_string_utf8_get_fast(x_59, x_93);
x_99 = 45;
x_100 = lean_uint32_dec_eq(x_98, x_99);
if (x_100 == 0)
{
uint32_t x_101; uint8_t x_102; 
lean_dec(x_61);
x_101 = 43;
x_102 = lean_uint32_dec_eq(x_98, x_101);
if (x_102 == 0)
{
x_28 = x_94;
x_29 = x_59;
x_30 = x_93;
goto block_40;
}
else
{
if (x_95 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_93);
lean_dec(x_59);
lean_dec(x_1);
x_103 = l_Lean_Json_Parser_hexChar___closed__0;
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_94);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_94);
x_105 = lean_string_utf8_next_fast(x_59, x_93);
lean_dec(x_93);
lean_inc(x_105);
lean_inc(x_59);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_59);
lean_ctor_set(x_106, 1, x_105);
x_28 = x_106;
x_29 = x_59;
x_30 = x_105;
goto block_40;
}
}
}
else
{
if (x_95 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_93);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_1);
x_107 = l_Lean_Json_Parser_hexChar___closed__0;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_94);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_94);
x_109 = lean_string_utf8_next_fast(x_59, x_93);
lean_dec(x_93);
lean_inc(x_109);
lean_inc(x_59);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_59);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_nat_dec_lt(x_109, x_61);
lean_dec(x_61);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_109);
lean_dec(x_59);
lean_dec(x_1);
x_112 = l_Lean_Json_Parser_hexChar___closed__0;
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
else
{
uint32_t x_114; uint32_t x_115; uint8_t x_116; 
x_114 = lean_string_utf8_get_fast(x_59, x_109);
lean_dec(x_109);
lean_dec(x_59);
x_115 = 48;
x_116 = lean_uint32_dec_le(x_115, x_114);
if (x_116 == 0)
{
x_41 = x_110;
x_42 = x_116;
goto block_58;
}
else
{
uint32_t x_117; uint8_t x_118; 
x_117 = 57;
x_118 = lean_uint32_dec_le(x_114, x_117);
x_41 = x_110;
x_42 = x_118;
goto block_58;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_num(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_247 = lean_ctor_get(x_1, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_1, 1);
lean_inc(x_248);
x_249 = lean_string_utf8_byte_size(x_247);
x_250 = lean_nat_dec_lt(x_248, x_249);
lean_dec(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_248);
lean_dec(x_247);
x_251 = l_Lean_Json_Parser_hexChar___closed__0;
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_1);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
else
{
uint32_t x_253; uint32_t x_254; uint8_t x_255; 
x_253 = lean_string_utf8_get_fast(x_247, x_248);
x_254 = 45;
x_255 = lean_uint32_dec_eq(x_253, x_254);
if (x_255 == 0)
{
lean_object* x_256; 
x_256 = l_Lean_Json_Parser_numSign___closed__0;
x_224 = x_1;
x_225 = x_247;
x_226 = x_248;
x_227 = x_256;
goto block_246;
}
else
{
if (x_250 == 0)
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_248);
lean_dec(x_247);
x_257 = l_Lean_Json_Parser_hexChar___closed__0;
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_1);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
else
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_1);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_260 = lean_ctor_get(x_1, 1);
lean_dec(x_260);
x_261 = lean_ctor_get(x_1, 0);
lean_dec(x_261);
x_262 = lean_string_utf8_next_fast(x_247, x_248);
lean_dec(x_248);
lean_inc(x_262);
lean_inc(x_247);
lean_ctor_set(x_1, 1, x_262);
x_263 = l_Lean_Json_Parser_numSign___closed__1;
x_224 = x_1;
x_225 = x_247;
x_226 = x_262;
x_227 = x_263;
goto block_246;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_1);
x_264 = lean_string_utf8_next_fast(x_247, x_248);
lean_dec(x_248);
lean_inc(x_264);
lean_inc(x_247);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_247);
lean_ctor_set(x_265, 1, x_264);
x_266 = l_Lean_Json_Parser_numSign___closed__1;
x_224 = x_265;
x_225 = x_247;
x_226 = x_264;
x_227 = x_266;
goto block_246;
}
}
}
}
block_27:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = l_Lean_Json_Parser_natMaybeZero___closed__0;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Json_Parser_natCore(x_7, x_2);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = l_Lean_Json_Parser_numWithDecimals___closed__0;
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_JsonNumber_shiftl(x_3, x_10);
lean_dec(x_10);
lean_ctor_set(x_8, 1, x_13);
return x_8;
}
else
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_3);
x_14 = l_Lean_Json_Parser_exponent___closed__0;
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_14);
return x_8;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = l_Lean_Json_Parser_numWithDecimals___closed__0;
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_JsonNumber_shiftl(x_3, x_16);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_3);
x_21 = l_Lean_Json_Parser_exponent___closed__0;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
block_41:
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_string_utf8_byte_size(x_30);
x_33 = lean_nat_dec_lt(x_31, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
x_34 = l_Lean_Json_Parser_hexChar___closed__0;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
else
{
uint32_t x_36; uint32_t x_37; uint8_t x_38; 
x_36 = lean_string_utf8_get_fast(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_37 = 48;
x_38 = lean_uint32_dec_le(x_37, x_36);
if (x_38 == 0)
{
x_2 = x_29;
x_3 = x_28;
x_4 = x_38;
goto block_27;
}
else
{
uint32_t x_39; uint8_t x_40; 
x_39 = 57;
x_40 = lean_uint32_dec_le(x_36, x_39);
x_2 = x_29;
x_3 = x_28;
x_4 = x_40;
goto block_27;
}
}
}
block_60:
{
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
x_45 = l_Lean_Json_Parser_natMaybeZero___closed__0;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_Json_Parser_natCore(x_47, x_43);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 1);
x_51 = l_Lean_JsonNumber_shiftr(x_42, x_50);
lean_dec(x_50);
lean_ctor_set(x_48, 1, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = l_Lean_JsonNumber_shiftr(x_42, x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_42);
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
return x_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
block_95:
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_string_utf8_byte_size(x_63);
x_66 = lean_nat_dec_lt(x_62, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
x_67 = l_Lean_Json_Parser_hexChar___closed__0;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_61);
x_69 = lean_string_utf8_next_fast(x_63, x_62);
lean_dec(x_62);
lean_inc(x_69);
lean_inc(x_63);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_nat_dec_lt(x_69, x_65);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_69);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
x_72 = l_Lean_Json_Parser_hexChar___closed__0;
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
else
{
uint32_t x_74; uint32_t x_75; uint8_t x_76; 
x_74 = lean_string_utf8_get_fast(x_63, x_69);
x_75 = 45;
x_76 = lean_uint32_dec_eq(x_74, x_75);
if (x_76 == 0)
{
uint32_t x_77; uint8_t x_78; 
lean_dec(x_65);
x_77 = 43;
x_78 = lean_uint32_dec_eq(x_74, x_77);
if (x_78 == 0)
{
x_28 = x_64;
x_29 = x_70;
x_30 = x_63;
x_31 = x_69;
goto block_41;
}
else
{
if (x_71 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_63);
x_79 = l_Lean_Json_Parser_hexChar___closed__0;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_70);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_70);
x_81 = lean_string_utf8_next_fast(x_63, x_69);
lean_dec(x_69);
lean_inc(x_81);
lean_inc(x_63);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_63);
lean_ctor_set(x_82, 1, x_81);
x_28 = x_64;
x_29 = x_82;
x_30 = x_63;
x_31 = x_81;
goto block_41;
}
}
}
else
{
if (x_71 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_69);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
x_83 = l_Lean_Json_Parser_hexChar___closed__0;
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_70);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_70);
x_85 = lean_string_utf8_next_fast(x_63, x_69);
lean_dec(x_69);
lean_inc(x_85);
lean_inc(x_63);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_63);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_nat_dec_lt(x_85, x_65);
lean_dec(x_65);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_63);
x_88 = l_Lean_Json_Parser_hexChar___closed__0;
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
else
{
uint32_t x_90; uint32_t x_91; uint8_t x_92; 
x_90 = lean_string_utf8_get_fast(x_63, x_85);
lean_dec(x_85);
lean_dec(x_63);
x_91 = 48;
x_92 = lean_uint32_dec_le(x_91, x_90);
if (x_92 == 0)
{
x_42 = x_64;
x_43 = x_86;
x_44 = x_92;
goto block_60;
}
else
{
uint32_t x_93; uint8_t x_94; 
x_93 = 57;
x_94 = lean_uint32_dec_le(x_90, x_93);
x_42 = x_64;
x_43 = x_86;
x_44 = x_94;
goto block_60;
}
}
}
}
}
}
}
block_110:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
x_101 = lean_string_utf8_byte_size(x_99);
x_102 = lean_nat_dec_lt(x_100, x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
return x_96;
}
else
{
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_96);
x_103 = l_Lean_Json_Parser_hexChar___closed__0;
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
else
{
uint32_t x_105; uint32_t x_106; uint8_t x_107; 
x_105 = lean_string_utf8_get_fast(x_99, x_100);
x_106 = 101;
x_107 = lean_uint32_dec_eq(x_105, x_106);
if (x_107 == 0)
{
uint32_t x_108; uint8_t x_109; 
x_108 = 69;
x_109 = lean_uint32_dec_eq(x_105, x_108);
if (x_109 == 0)
{
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
return x_96;
}
else
{
lean_dec(x_96);
x_61 = x_97;
x_62 = x_100;
x_63 = x_99;
x_64 = x_98;
goto block_95;
}
}
else
{
lean_dec(x_96);
x_61 = x_97;
x_62 = x_100;
x_63 = x_99;
x_64 = x_98;
goto block_95;
}
}
}
}
block_174:
{
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_112);
lean_dec(x_111);
x_115 = l_Lean_Json_Parser_natNumDigits___closed__0;
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_unsigned_to_nat(0u);
x_118 = l_Lean_Json_Parser_natCoreNumDigits(x_117, x_117, x_113);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_118, 1);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_122 = lean_ctor_get(x_118, 0);
x_123 = lean_ctor_get(x_120, 0);
x_124 = lean_ctor_get(x_120, 1);
x_125 = l_Lean_Json_Parser_numWithDecimals___closed__0;
x_126 = lean_nat_dec_lt(x_125, x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_127 = lean_nat_to_int(x_111);
x_128 = lean_unsigned_to_nat(10u);
x_129 = lean_nat_pow(x_128, x_124);
x_130 = lean_nat_to_int(x_129);
x_131 = lean_int_mul(x_127, x_130);
lean_dec(x_130);
lean_dec(x_127);
x_132 = lean_nat_to_int(x_123);
x_133 = lean_int_add(x_131, x_132);
lean_dec(x_132);
lean_dec(x_131);
x_134 = lean_int_mul(x_112, x_133);
lean_dec(x_133);
lean_dec(x_112);
lean_ctor_set(x_120, 0, x_134);
lean_inc(x_120);
lean_inc(x_122);
x_96 = x_118;
x_97 = x_122;
x_98 = x_120;
goto block_110;
}
else
{
lean_object* x_135; 
lean_free_object(x_120);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_112);
lean_dec(x_111);
x_135 = l_Lean_Json_Parser_numWithDecimals___closed__1;
lean_ctor_set_tag(x_118, 1);
lean_ctor_set(x_118, 1, x_135);
return x_118;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_118, 0);
x_137 = lean_ctor_get(x_120, 0);
x_138 = lean_ctor_get(x_120, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_120);
x_139 = l_Lean_Json_Parser_numWithDecimals___closed__0;
x_140 = lean_nat_dec_lt(x_139, x_138);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_141 = lean_nat_to_int(x_111);
x_142 = lean_unsigned_to_nat(10u);
x_143 = lean_nat_pow(x_142, x_138);
x_144 = lean_nat_to_int(x_143);
x_145 = lean_int_mul(x_141, x_144);
lean_dec(x_144);
lean_dec(x_141);
x_146 = lean_nat_to_int(x_137);
x_147 = lean_int_add(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
x_148 = lean_int_mul(x_112, x_147);
lean_dec(x_147);
lean_dec(x_112);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_138);
lean_inc(x_149);
lean_inc(x_136);
lean_ctor_set(x_118, 1, x_149);
x_96 = x_118;
x_97 = x_136;
x_98 = x_149;
goto block_110;
}
else
{
lean_object* x_150; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_112);
lean_dec(x_111);
x_150 = l_Lean_Json_Parser_numWithDecimals___closed__1;
lean_ctor_set_tag(x_118, 1);
lean_ctor_set(x_118, 1, x_150);
return x_118;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_151 = lean_ctor_get(x_118, 1);
x_152 = lean_ctor_get(x_118, 0);
lean_inc(x_151);
lean_inc(x_152);
lean_dec(x_118);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_155 = x_151;
} else {
 lean_dec_ref(x_151);
 x_155 = lean_box(0);
}
x_156 = l_Lean_Json_Parser_numWithDecimals___closed__0;
x_157 = lean_nat_dec_lt(x_156, x_154);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_158 = lean_nat_to_int(x_111);
x_159 = lean_unsigned_to_nat(10u);
x_160 = lean_nat_pow(x_159, x_154);
x_161 = lean_nat_to_int(x_160);
x_162 = lean_int_mul(x_158, x_161);
lean_dec(x_161);
lean_dec(x_158);
x_163 = lean_nat_to_int(x_153);
x_164 = lean_int_add(x_162, x_163);
lean_dec(x_163);
lean_dec(x_162);
x_165 = lean_int_mul(x_112, x_164);
lean_dec(x_164);
lean_dec(x_112);
if (lean_is_scalar(x_155)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_155;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_154);
lean_inc(x_166);
lean_inc(x_152);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_152);
lean_ctor_set(x_167, 1, x_166);
x_96 = x_167;
x_97 = x_152;
x_98 = x_166;
goto block_110;
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_112);
lean_dec(x_111);
x_168 = l_Lean_Json_Parser_numWithDecimals___closed__1;
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_152);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_112);
lean_dec(x_111);
x_170 = !lean_is_exclusive(x_118);
if (x_170 == 0)
{
return x_118;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_118, 0);
x_172 = lean_ctor_get(x_118, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_118);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
}
block_207:
{
lean_object* x_180; uint8_t x_181; 
x_180 = lean_string_utf8_byte_size(x_177);
x_181 = lean_nat_dec_lt(x_178, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_177);
x_182 = lean_nat_to_int(x_179);
x_183 = lean_int_mul(x_175, x_182);
lean_dec(x_182);
lean_dec(x_175);
x_184 = l_Lean_JsonNumber_fromInt(x_183);
lean_inc(x_184);
lean_inc(x_176);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_176);
lean_ctor_set(x_185, 1, x_184);
x_96 = x_185;
x_97 = x_176;
x_98 = x_184;
goto block_110;
}
else
{
if (x_181 == 0)
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_175);
x_186 = l_Lean_Json_Parser_hexChar___closed__0;
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_176);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
else
{
uint32_t x_188; uint32_t x_189; uint8_t x_190; 
x_188 = lean_string_utf8_get_fast(x_177, x_178);
x_189 = 46;
x_190 = lean_uint32_dec_eq(x_188, x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_177);
x_191 = lean_nat_to_int(x_179);
x_192 = lean_int_mul(x_175, x_191);
lean_dec(x_191);
lean_dec(x_175);
x_193 = l_Lean_JsonNumber_fromInt(x_192);
lean_inc(x_193);
lean_inc(x_176);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_176);
lean_ctor_set(x_194, 1, x_193);
x_96 = x_194;
x_97 = x_176;
x_98 = x_193;
goto block_110;
}
else
{
if (x_181 == 0)
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_175);
x_195 = l_Lean_Json_Parser_hexChar___closed__0;
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_176);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_176);
x_197 = lean_string_utf8_next_fast(x_177, x_178);
lean_dec(x_178);
lean_inc(x_197);
lean_inc(x_177);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_177);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_nat_dec_lt(x_197, x_180);
lean_dec(x_180);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_197);
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_175);
x_200 = l_Lean_Json_Parser_hexChar___closed__0;
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
else
{
uint32_t x_202; uint32_t x_203; uint8_t x_204; 
x_202 = lean_string_utf8_get_fast(x_177, x_197);
lean_dec(x_197);
lean_dec(x_177);
x_203 = 48;
x_204 = lean_uint32_dec_le(x_203, x_202);
if (x_204 == 0)
{
x_111 = x_179;
x_112 = x_175;
x_113 = x_198;
x_114 = x_204;
goto block_174;
}
else
{
uint32_t x_205; uint8_t x_206; 
x_205 = 57;
x_206 = lean_uint32_dec_le(x_202, x_205);
x_111 = x_179;
x_112 = x_175;
x_113 = x_198;
x_114 = x_206;
goto block_174;
}
}
}
}
}
}
}
block_223:
{
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_209);
x_211 = l_Lean_Json_Parser_natNonZero___closed__0;
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_208);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_unsigned_to_nat(0u);
x_214 = l_Lean_Json_Parser_natCore(x_213, x_208);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
x_175 = x_209;
x_176 = x_215;
x_177 = x_217;
x_178 = x_218;
x_179 = x_216;
goto block_207;
}
else
{
uint8_t x_219; 
lean_dec(x_209);
x_219 = !lean_is_exclusive(x_214);
if (x_219 == 0)
{
return x_214;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_214, 0);
x_221 = lean_ctor_get(x_214, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_214);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
}
block_246:
{
lean_object* x_228; uint8_t x_229; 
x_228 = lean_string_utf8_byte_size(x_225);
x_229 = lean_nat_dec_lt(x_226, x_228);
lean_dec(x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
x_230 = l_Lean_Json_Parser_hexChar___closed__0;
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_224);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
else
{
uint32_t x_232; uint32_t x_233; uint8_t x_234; 
x_232 = lean_string_utf8_get_fast(x_225, x_226);
x_233 = 48;
x_234 = lean_uint32_dec_eq(x_232, x_233);
if (x_234 == 0)
{
lean_dec(x_226);
lean_dec(x_225);
if (x_229 == 0)
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_227);
x_235 = l_Lean_Json_Parser_hexChar___closed__0;
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_224);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
else
{
uint32_t x_237; uint8_t x_238; 
x_237 = 49;
x_238 = lean_uint32_dec_le(x_237, x_232);
if (x_238 == 0)
{
x_208 = x_224;
x_209 = x_227;
x_210 = x_238;
goto block_223;
}
else
{
uint32_t x_239; uint8_t x_240; 
x_239 = 57;
x_240 = lean_uint32_dec_le(x_232, x_239);
x_208 = x_224;
x_209 = x_227;
x_210 = x_240;
goto block_223;
}
}
}
else
{
if (x_229 == 0)
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
x_241 = l_Lean_Json_Parser_hexChar___closed__0;
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_224);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_224);
x_243 = lean_string_utf8_next_fast(x_225, x_226);
lean_dec(x_226);
lean_inc(x_243);
lean_inc(x_225);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_225);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_unsigned_to_nat(0u);
x_175 = x_227;
x_176 = x_244;
x_177 = x_225;
x_178 = x_243;
x_179 = x_245;
goto block_207;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_arrayCore___closed__0() {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_string_utf8_byte_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = l_Lean_Json_Parser_hexChar___closed__0;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_5, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
x_15 = lean_array_push(x_1, x_6);
x_16 = lean_string_utf8_get_fast(x_7, x_8);
x_17 = lean_string_utf8_next_fast(x_7, x_8);
lean_dec(x_8);
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
lean_dec(x_15);
x_22 = l_Lean_Json_Parser_arrayCore___closed__0;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_22);
return x_3;
}
else
{
lean_object* x_23; 
lean_free_object(x_3);
x_23 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_5);
x_1 = x_15;
x_2 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; 
x_25 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_5);
lean_ctor_set(x_3, 1, x_15);
lean_ctor_set(x_3, 0, x_25);
return x_3;
}
}
else
{
lean_object* x_26; uint32_t x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; uint8_t x_31; 
lean_dec(x_5);
x_26 = lean_array_push(x_1, x_6);
x_27 = lean_string_utf8_get_fast(x_7, x_8);
x_28 = lean_string_utf8_next_fast(x_7, x_8);
lean_dec(x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_28);
x_30 = 93;
x_31 = lean_uint32_dec_eq(x_27, x_30);
if (x_31 == 0)
{
uint32_t x_32; uint8_t x_33; 
x_32 = 44;
x_33 = lean_uint32_dec_eq(x_27, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_26);
x_34 = l_Lean_Json_Parser_arrayCore___closed__0;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_34);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
else
{
lean_object* x_35; 
lean_free_object(x_3);
x_35 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_29);
x_1 = x_26;
x_2 = x_35;
goto _start;
}
}
else
{
lean_object* x_37; 
x_37 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_29);
lean_ctor_set(x_3, 1, x_26);
lean_ctor_set(x_3, 0, x_37);
return x_3;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_3, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_3);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
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
lean_dec(x_1);
x_44 = l_Lean_Json_Parser_hexChar___closed__0;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint32_t x_48; lean_object* x_49; lean_object* x_50; uint32_t x_51; uint8_t x_52; 
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
x_47 = lean_array_push(x_1, x_39);
x_48 = lean_string_utf8_get_fast(x_40, x_41);
x_49 = lean_string_utf8_next_fast(x_40, x_41);
lean_dec(x_41);
if (lean_is_scalar(x_46)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_46;
}
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
x_51 = 93;
x_52 = lean_uint32_dec_eq(x_48, x_51);
if (x_52 == 0)
{
uint32_t x_53; uint8_t x_54; 
x_53 = 44;
x_54 = lean_uint32_dec_eq(x_48, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_47);
x_55 = l_Lean_Json_Parser_arrayCore___closed__0;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
else
{
lean_object* x_57; 
x_57 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_50);
x_1 = x_47;
x_2 = x_57;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_50);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_47);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_3);
if (x_61 == 0)
{
return x_3;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_3, 0);
x_63 = lean_ctor_get(x_3, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_3);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected input", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_Parser_anyCore___closed__6;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_string_utf8_byte_size(x_21);
x_24 = lean_nat_dec_lt(x_22, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_21);
x_25 = l_Lean_Json_Parser_hexChar___closed__0;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
uint32_t x_27; uint32_t x_28; uint8_t x_29; 
x_27 = lean_string_utf8_get_fast(x_21, x_22);
x_28 = 91;
x_29 = lean_uint32_dec_eq(x_27, x_28);
if (x_29 == 0)
{
uint32_t x_30; uint8_t x_31; 
x_30 = 123;
x_31 = lean_uint32_dec_eq(x_27, x_30);
if (x_31 == 0)
{
uint32_t x_32; uint8_t x_33; 
x_32 = 34;
x_33 = lean_uint32_dec_eq(x_27, x_32);
if (x_33 == 0)
{
uint32_t x_34; uint8_t x_35; 
lean_dec(x_22);
lean_dec(x_21);
x_34 = 102;
x_35 = lean_uint32_dec_eq(x_27, x_34);
if (x_35 == 0)
{
uint32_t x_36; uint8_t x_37; 
x_36 = 116;
x_37 = lean_uint32_dec_eq(x_27, x_36);
if (x_37 == 0)
{
uint32_t x_38; uint8_t x_39; 
x_38 = 110;
x_39 = lean_uint32_dec_eq(x_27, x_38);
if (x_39 == 0)
{
uint32_t x_40; uint8_t x_41; 
x_40 = 45;
x_41 = lean_uint32_dec_eq(x_27, x_40);
if (x_41 == 0)
{
uint32_t x_42; uint8_t x_43; 
x_42 = 48;
x_43 = lean_uint32_dec_le(x_42, x_27);
if (x_43 == 0)
{
x_2 = x_43;
goto block_20;
}
else
{
uint32_t x_44; uint8_t x_45; 
x_44 = 57;
x_45 = lean_uint32_dec_le(x_27, x_44);
x_2 = x_45;
goto block_20;
}
}
else
{
x_2 = x_24;
goto block_20;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_Json_Parser_anyCore___closed__1;
x_47 = l_Std_Internal_Parsec_String_pstring(x_46, x_1);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_dec(x_50);
x_51 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_49);
x_52 = lean_box(0);
lean_ctor_set(x_47, 1, x_52);
lean_ctor_set(x_47, 0, x_51);
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
lean_dec(x_47);
x_54 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_53);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_47);
if (x_57 == 0)
{
return x_47;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_47, 0);
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_47);
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
x_67 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_67, 0, x_24);
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
x_70 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_70, 0, x_24);
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
x_82 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_82, 0, x_33);
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
x_85 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_85, 0, x_33);
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
if (x_24 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_22);
lean_dec(x_21);
x_91 = l_Lean_Json_Parser_hexChar___closed__0;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
else
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_1);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_1, 1);
lean_dec(x_94);
x_95 = lean_ctor_get(x_1, 0);
lean_dec(x_95);
x_96 = lean_string_utf8_next_fast(x_21, x_22);
lean_dec(x_22);
lean_ctor_set(x_1, 1, x_96);
x_97 = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
x_98 = l_Lean_Json_Parser_strCore(x_97, x_1);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_ctor_get(x_98, 1);
x_102 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_100);
x_103 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_98, 1, x_103);
lean_ctor_set(x_98, 0, x_102);
return x_98;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_98, 0);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_98);
x_106 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_104);
x_107 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_107, 0, x_105);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
else
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_98);
if (x_109 == 0)
{
return x_98;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_98, 0);
x_111 = lean_ctor_get(x_98, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_98);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_1);
x_113 = lean_string_utf8_next_fast(x_21, x_22);
lean_dec(x_22);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_21);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
x_116 = l_Lean_Json_Parser_strCore(x_115, x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_117);
x_121 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_121, 0, x_118);
if (lean_is_scalar(x_119)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_119;
}
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_116, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_116, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_125 = x_116;
} else {
 lean_dec_ref(x_116);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
}
}
else
{
if (x_24 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_22);
lean_dec(x_21);
x_127 = l_Lean_Json_Parser_hexChar___closed__0;
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_1);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_1);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_130 = lean_ctor_get(x_1, 1);
lean_dec(x_130);
x_131 = lean_ctor_get(x_1, 0);
lean_dec(x_131);
x_132 = lean_string_utf8_next_fast(x_21, x_22);
lean_dec(x_22);
lean_ctor_set(x_1, 1, x_132);
x_133 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_1);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
x_136 = lean_string_utf8_byte_size(x_134);
x_137 = lean_nat_dec_lt(x_135, x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_135);
lean_dec(x_134);
x_138 = l_Lean_Json_Parser_hexChar___closed__0;
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
else
{
uint32_t x_140; uint32_t x_141; uint8_t x_142; 
x_140 = lean_string_utf8_get_fast(x_134, x_135);
x_141 = 125;
x_142 = lean_uint32_dec_eq(x_140, x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_135);
lean_dec(x_134);
x_143 = lean_box(0);
x_144 = l_Lean_Json_Parser_objectCore(x_143, x_133);
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_144, 1);
x_147 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_144, 1, x_147);
return x_144;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_144, 0);
x_149 = lean_ctor_get(x_144, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_144);
x_150 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
else
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_144);
if (x_152 == 0)
{
return x_144;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_144, 0);
x_154 = lean_ctor_get(x_144, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_144);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
if (x_137 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_135);
lean_dec(x_134);
x_156 = l_Lean_Json_Parser_hexChar___closed__0;
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_133);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
else
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_133);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_133, 1);
lean_dec(x_159);
x_160 = lean_ctor_get(x_133, 0);
lean_dec(x_160);
x_161 = lean_string_utf8_next_fast(x_134, x_135);
lean_dec(x_135);
lean_ctor_set(x_133, 1, x_161);
x_162 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_133);
x_163 = l_Lean_Json_Parser_anyCore___closed__4;
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_133);
x_165 = lean_string_utf8_next_fast(x_134, x_135);
lean_dec(x_135);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_134);
lean_ctor_set(x_166, 1, x_165);
x_167 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_166);
x_168 = l_Lean_Json_Parser_anyCore___closed__4;
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
lean_dec(x_1);
x_170 = lean_string_utf8_next_fast(x_21, x_22);
lean_dec(x_22);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_21);
lean_ctor_set(x_171, 1, x_170);
x_172 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
x_175 = lean_string_utf8_byte_size(x_173);
x_176 = lean_nat_dec_lt(x_174, x_175);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_174);
lean_dec(x_173);
x_177 = l_Lean_Json_Parser_hexChar___closed__0;
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
else
{
uint32_t x_179; uint32_t x_180; uint8_t x_181; 
x_179 = lean_string_utf8_get_fast(x_173, x_174);
x_180 = 125;
x_181 = lean_uint32_dec_eq(x_179, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_174);
lean_dec(x_173);
x_182 = lean_box(0);
x_183 = l_Lean_Json_Parser_objectCore(x_182, x_172);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_187, 0, x_185);
if (lean_is_scalar(x_186)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_186;
}
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_183, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_183, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_191 = x_183;
} else {
 lean_dec_ref(x_183);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
else
{
if (x_176 == 0)
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_174);
lean_dec(x_173);
x_193 = l_Lean_Json_Parser_hexChar___closed__0;
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_172);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_195 = x_172;
} else {
 lean_dec_ref(x_172);
 x_195 = lean_box(0);
}
x_196 = lean_string_utf8_next_fast(x_173, x_174);
lean_dec(x_174);
if (lean_is_scalar(x_195)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_195;
}
lean_ctor_set(x_197, 0, x_173);
lean_ctor_set(x_197, 1, x_196);
x_198 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_197);
x_199 = l_Lean_Json_Parser_anyCore___closed__4;
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
}
}
}
}
else
{
if (x_24 == 0)
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_22);
lean_dec(x_21);
x_201 = l_Lean_Json_Parser_hexChar___closed__0;
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_1);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
else
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_1);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_204 = lean_ctor_get(x_1, 1);
lean_dec(x_204);
x_205 = lean_ctor_get(x_1, 0);
lean_dec(x_205);
x_206 = lean_string_utf8_next_fast(x_21, x_22);
lean_dec(x_22);
lean_ctor_set(x_1, 1, x_206);
x_207 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_1);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
x_210 = lean_string_utf8_byte_size(x_208);
x_211 = lean_nat_dec_lt(x_209, x_210);
lean_dec(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_209);
lean_dec(x_208);
x_212 = l_Lean_Json_Parser_hexChar___closed__0;
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_207);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
else
{
uint32_t x_214; uint32_t x_215; uint8_t x_216; 
x_214 = lean_string_utf8_get_fast(x_208, x_209);
x_215 = 93;
x_216 = lean_uint32_dec_eq(x_214, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_209);
lean_dec(x_208);
x_217 = l_Lean_Json_Parser_anyCore___closed__5;
x_218 = l_Lean_Json_Parser_arrayCore(x_217, x_207);
if (lean_obj_tag(x_218) == 0)
{
uint8_t x_219; 
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_218, 1);
x_221 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_218, 1, x_221);
return x_218;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_ctor_get(x_218, 0);
x_223 = lean_ctor_get(x_218, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_218);
x_224 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_224, 0, x_223);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
else
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_218);
if (x_226 == 0)
{
return x_218;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_218, 0);
x_228 = lean_ctor_get(x_218, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_218);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
else
{
if (x_211 == 0)
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_209);
lean_dec(x_208);
x_230 = l_Lean_Json_Parser_hexChar___closed__0;
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_207);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
else
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_207);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_233 = lean_ctor_get(x_207, 1);
lean_dec(x_233);
x_234 = lean_ctor_get(x_207, 0);
lean_dec(x_234);
x_235 = lean_string_utf8_next_fast(x_208, x_209);
lean_dec(x_209);
lean_ctor_set(x_207, 1, x_235);
x_236 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_207);
x_237 = l_Lean_Json_Parser_anyCore___closed__7;
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_207);
x_239 = lean_string_utf8_next_fast(x_208, x_209);
lean_dec(x_209);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_208);
lean_ctor_set(x_240, 1, x_239);
x_241 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_240);
x_242 = l_Lean_Json_Parser_anyCore___closed__7;
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
lean_dec(x_1);
x_244 = lean_string_utf8_next_fast(x_21, x_22);
lean_dec(x_22);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_21);
lean_ctor_set(x_245, 1, x_244);
x_246 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_245);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
x_249 = lean_string_utf8_byte_size(x_247);
x_250 = lean_nat_dec_lt(x_248, x_249);
lean_dec(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_248);
lean_dec(x_247);
x_251 = l_Lean_Json_Parser_hexChar___closed__0;
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_246);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
else
{
uint32_t x_253; uint32_t x_254; uint8_t x_255; 
x_253 = lean_string_utf8_get_fast(x_247, x_248);
x_254 = 93;
x_255 = lean_uint32_dec_eq(x_253, x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_248);
lean_dec(x_247);
x_256 = l_Lean_Json_Parser_anyCore___closed__5;
x_257 = l_Lean_Json_Parser_arrayCore(x_256, x_246);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_260 = x_257;
} else {
 lean_dec_ref(x_257);
 x_260 = lean_box(0);
}
x_261 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_261, 0, x_259);
if (lean_is_scalar(x_260)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_260;
}
lean_ctor_set(x_262, 0, x_258);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_263 = lean_ctor_get(x_257, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_257, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_265 = x_257;
} else {
 lean_dec_ref(x_257);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
else
{
if (x_250 == 0)
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_248);
lean_dec(x_247);
x_267 = l_Lean_Json_Parser_hexChar___closed__0;
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_246);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_269 = x_246;
} else {
 lean_dec_ref(x_246);
 x_269 = lean_box(0);
}
x_270 = lean_string_utf8_next_fast(x_247, x_248);
lean_dec(x_248);
if (lean_is_scalar(x_269)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_269;
}
lean_ctor_set(x_271, 0, x_247);
lean_ctor_set(x_271, 1, x_270);
x_272 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_271);
x_273 = l_Lean_Json_Parser_anyCore___closed__7;
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
}
}
}
}
block_20:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_Parser_anyCore___closed__0;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Json_Parser_num(x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_7);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_5, 1, x_10);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_11);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_objectCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected \"", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_objectCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected :", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_objectCore___closed__2() {
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
x_7 = l_Lean_Json_Parser_hexChar___closed__0;
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
x_12 = l_Lean_Json_Parser_objectCore___closed__0;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
if (x_6 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = l_Lean_Json_Parser_hexChar___closed__0;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_2, 0);
lean_dec(x_18);
x_19 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_19);
x_20 = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
x_21 = l_Lean_Json_Parser_strCore(x_20, x_2);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = lean_string_utf8_byte_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_1);
x_30 = l_Lean_Json_Parser_hexChar___closed__0;
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_30);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
uint32_t x_31; uint32_t x_32; uint8_t x_33; 
x_31 = lean_string_utf8_get_fast(x_26, x_27);
x_32 = 58;
x_33 = lean_uint32_dec_eq(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_1);
x_34 = l_Lean_Json_Parser_objectCore___closed__1;
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_34);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
if (x_29 == 0)
{
lean_object* x_35; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_1);
x_35 = l_Lean_Json_Parser_hexChar___closed__0;
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_35);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
uint8_t x_36; 
lean_free_object(x_21);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_25, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_25, 0);
lean_dec(x_38);
x_39 = lean_string_utf8_next_fast(x_26, x_27);
lean_dec(x_27);
lean_ctor_set(x_25, 1, x_39);
x_40 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_25);
x_41 = l_Lean_Json_Parser_anyCore(x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_string_utf8_byte_size(x_45);
x_48 = lean_nat_dec_lt(x_46, x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_24);
lean_dec(x_1);
x_49 = l_Lean_Json_Parser_hexChar___closed__0;
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 1, x_49);
return x_41;
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint32_t x_53; lean_object* x_54; uint32_t x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_43, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_43, 0);
lean_dec(x_52);
x_53 = lean_string_utf8_get_fast(x_45, x_46);
x_54 = lean_string_utf8_next_fast(x_45, x_46);
lean_dec(x_46);
lean_ctor_set(x_43, 1, x_54);
x_55 = 125;
x_56 = lean_uint32_dec_eq(x_53, x_55);
if (x_56 == 0)
{
uint32_t x_57; uint8_t x_58; 
x_57 = 44;
x_58 = lean_uint32_dec_eq(x_53, x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_44);
lean_dec(x_24);
lean_dec(x_1);
x_59 = l_Lean_Json_Parser_objectCore___closed__2;
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 1, x_59);
return x_41;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_41);
x_60 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_43);
x_61 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_24, x_44);
x_1 = x_61;
x_2 = x_60;
goto _start;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_43);
x_64 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_24, x_44);
lean_ctor_set(x_41, 1, x_64);
lean_ctor_set(x_41, 0, x_63);
return x_41;
}
}
else
{
uint32_t x_65; lean_object* x_66; lean_object* x_67; uint32_t x_68; uint8_t x_69; 
lean_dec(x_43);
x_65 = lean_string_utf8_get_fast(x_45, x_46);
x_66 = lean_string_utf8_next_fast(x_45, x_46);
lean_dec(x_46);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_45);
lean_ctor_set(x_67, 1, x_66);
x_68 = 125;
x_69 = lean_uint32_dec_eq(x_65, x_68);
if (x_69 == 0)
{
uint32_t x_70; uint8_t x_71; 
x_70 = 44;
x_71 = lean_uint32_dec_eq(x_65, x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_44);
lean_dec(x_24);
lean_dec(x_1);
x_72 = l_Lean_Json_Parser_objectCore___closed__2;
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 1, x_72);
lean_ctor_set(x_41, 0, x_67);
return x_41;
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_free_object(x_41);
x_73 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_67);
x_74 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_24, x_44);
x_1 = x_74;
x_2 = x_73;
goto _start;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_67);
x_77 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_24, x_44);
lean_ctor_set(x_41, 1, x_77);
lean_ctor_set(x_41, 0, x_76);
return x_41;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_78 = lean_ctor_get(x_41, 0);
x_79 = lean_ctor_get(x_41, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_41);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
x_82 = lean_string_utf8_byte_size(x_80);
x_83 = lean_nat_dec_lt(x_81, x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_24);
lean_dec(x_1);
x_84 = l_Lean_Json_Parser_hexChar___closed__0;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
else
{
lean_object* x_86; uint32_t x_87; lean_object* x_88; lean_object* x_89; uint32_t x_90; uint8_t x_91; 
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_86 = x_78;
} else {
 lean_dec_ref(x_78);
 x_86 = lean_box(0);
}
x_87 = lean_string_utf8_get_fast(x_80, x_81);
x_88 = lean_string_utf8_next_fast(x_80, x_81);
lean_dec(x_81);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_80);
lean_ctor_set(x_89, 1, x_88);
x_90 = 125;
x_91 = lean_uint32_dec_eq(x_87, x_90);
if (x_91 == 0)
{
uint32_t x_92; uint8_t x_93; 
x_92 = 44;
x_93 = lean_uint32_dec_eq(x_87, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_79);
lean_dec(x_24);
lean_dec(x_1);
x_94 = l_Lean_Json_Parser_objectCore___closed__2;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_89);
x_97 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_24, x_79);
x_1 = x_97;
x_2 = x_96;
goto _start;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_89);
x_100 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_24, x_79);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_24);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_41);
if (x_102 == 0)
{
return x_41;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_41, 0);
x_104 = lean_ctor_get(x_41, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_41);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_25);
x_106 = lean_string_utf8_next_fast(x_26, x_27);
lean_dec(x_27);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_26);
lean_ctor_set(x_107, 1, x_106);
x_108 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_107);
x_109 = l_Lean_Json_Parser_anyCore(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
x_115 = lean_string_utf8_byte_size(x_113);
x_116 = lean_nat_dec_lt(x_114, x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_24);
lean_dec(x_1);
x_117 = l_Lean_Json_Parser_hexChar___closed__0;
if (lean_is_scalar(x_112)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_112;
 lean_ctor_set_tag(x_118, 1);
}
lean_ctor_set(x_118, 0, x_110);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
else
{
lean_object* x_119; uint32_t x_120; lean_object* x_121; lean_object* x_122; uint32_t x_123; uint8_t x_124; 
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_119 = x_110;
} else {
 lean_dec_ref(x_110);
 x_119 = lean_box(0);
}
x_120 = lean_string_utf8_get_fast(x_113, x_114);
x_121 = lean_string_utf8_next_fast(x_113, x_114);
lean_dec(x_114);
if (lean_is_scalar(x_119)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_119;
}
lean_ctor_set(x_122, 0, x_113);
lean_ctor_set(x_122, 1, x_121);
x_123 = 125;
x_124 = lean_uint32_dec_eq(x_120, x_123);
if (x_124 == 0)
{
uint32_t x_125; uint8_t x_126; 
x_125 = 44;
x_126 = lean_uint32_dec_eq(x_120, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_111);
lean_dec(x_24);
lean_dec(x_1);
x_127 = l_Lean_Json_Parser_objectCore___closed__2;
if (lean_is_scalar(x_112)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_112;
 lean_ctor_set_tag(x_128, 1);
}
lean_ctor_set(x_128, 0, x_122);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_112);
x_129 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_122);
x_130 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_24, x_111);
x_1 = x_130;
x_2 = x_129;
goto _start;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_122);
x_133 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_24, x_111);
if (lean_is_scalar(x_112)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_112;
}
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_24);
lean_dec(x_1);
x_135 = lean_ctor_get(x_109, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_109, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_137 = x_109;
} else {
 lean_dec_ref(x_109);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_139 = lean_ctor_get(x_21, 0);
x_140 = lean_ctor_get(x_21, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_21);
x_141 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_139);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
x_144 = lean_string_utf8_byte_size(x_142);
x_145 = lean_nat_dec_lt(x_143, x_144);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_1);
x_146 = l_Lean_Json_Parser_hexChar___closed__0;
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_141);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
else
{
uint32_t x_148; uint32_t x_149; uint8_t x_150; 
x_148 = lean_string_utf8_get_fast(x_142, x_143);
x_149 = 58;
x_150 = lean_uint32_dec_eq(x_148, x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_1);
x_151 = l_Lean_Json_Parser_objectCore___closed__1;
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_141);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
else
{
if (x_145 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_1);
x_153 = l_Lean_Json_Parser_hexChar___closed__0;
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_141);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_155 = x_141;
} else {
 lean_dec_ref(x_141);
 x_155 = lean_box(0);
}
x_156 = lean_string_utf8_next_fast(x_142, x_143);
lean_dec(x_143);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_142);
lean_ctor_set(x_157, 1, x_156);
x_158 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_157);
x_159 = l_Lean_Json_Parser_anyCore(x_158);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_162 = x_159;
} else {
 lean_dec_ref(x_159);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_160, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
x_165 = lean_string_utf8_byte_size(x_163);
x_166 = lean_nat_dec_lt(x_164, x_165);
lean_dec(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_161);
lean_dec(x_140);
lean_dec(x_1);
x_167 = l_Lean_Json_Parser_hexChar___closed__0;
if (lean_is_scalar(x_162)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_162;
 lean_ctor_set_tag(x_168, 1);
}
lean_ctor_set(x_168, 0, x_160);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
else
{
lean_object* x_169; uint32_t x_170; lean_object* x_171; lean_object* x_172; uint32_t x_173; uint8_t x_174; 
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_169 = x_160;
} else {
 lean_dec_ref(x_160);
 x_169 = lean_box(0);
}
x_170 = lean_string_utf8_get_fast(x_163, x_164);
x_171 = lean_string_utf8_next_fast(x_163, x_164);
lean_dec(x_164);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_163);
lean_ctor_set(x_172, 1, x_171);
x_173 = 125;
x_174 = lean_uint32_dec_eq(x_170, x_173);
if (x_174 == 0)
{
uint32_t x_175; uint8_t x_176; 
x_175 = 44;
x_176 = lean_uint32_dec_eq(x_170, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_161);
lean_dec(x_140);
lean_dec(x_1);
x_177 = l_Lean_Json_Parser_objectCore___closed__2;
if (lean_is_scalar(x_162)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_162;
 lean_ctor_set_tag(x_178, 1);
}
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_162);
x_179 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_172);
x_180 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_140, x_161);
x_1 = x_180;
x_2 = x_179;
goto _start;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_172);
x_183 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_140, x_161);
if (lean_is_scalar(x_162)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_162;
}
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_140);
lean_dec(x_1);
x_185 = lean_ctor_get(x_159, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_159, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_187 = x_159;
} else {
 lean_dec_ref(x_159);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
}
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_21);
if (x_189 == 0)
{
return x_21;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_21, 0);
x_191 = lean_ctor_get(x_21, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_21);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_2);
x_193 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_3);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lean_Json_Parser_finishSurrogatePair___closed__0;
x_196 = l_Lean_Json_Parser_strCore(x_195, x_194);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
x_200 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_197);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
x_203 = lean_string_utf8_byte_size(x_201);
x_204 = lean_nat_dec_lt(x_202, x_203);
lean_dec(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_198);
lean_dec(x_1);
x_205 = l_Lean_Json_Parser_hexChar___closed__0;
if (lean_is_scalar(x_199)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_199;
 lean_ctor_set_tag(x_206, 1);
}
lean_ctor_set(x_206, 0, x_200);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
else
{
uint32_t x_207; uint32_t x_208; uint8_t x_209; 
x_207 = lean_string_utf8_get_fast(x_201, x_202);
x_208 = 58;
x_209 = lean_uint32_dec_eq(x_207, x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_198);
lean_dec(x_1);
x_210 = l_Lean_Json_Parser_objectCore___closed__1;
if (lean_is_scalar(x_199)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_199;
 lean_ctor_set_tag(x_211, 1);
}
lean_ctor_set(x_211, 0, x_200);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
else
{
if (x_204 == 0)
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_198);
lean_dec(x_1);
x_212 = l_Lean_Json_Parser_hexChar___closed__0;
if (lean_is_scalar(x_199)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_199;
 lean_ctor_set_tag(x_213, 1);
}
lean_ctor_set(x_213, 0, x_200);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_199);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_214 = x_200;
} else {
 lean_dec_ref(x_200);
 x_214 = lean_box(0);
}
x_215 = lean_string_utf8_next_fast(x_201, x_202);
lean_dec(x_202);
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_214;
}
lean_ctor_set(x_216, 0, x_201);
lean_ctor_set(x_216, 1, x_215);
x_217 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_216);
x_218 = l_Lean_Json_Parser_anyCore(x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_221 = x_218;
} else {
 lean_dec_ref(x_218);
 x_221 = lean_box(0);
}
x_222 = lean_ctor_get(x_219, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_219, 1);
lean_inc(x_223);
x_224 = lean_string_utf8_byte_size(x_222);
x_225 = lean_nat_dec_lt(x_223, x_224);
lean_dec(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; 
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_198);
lean_dec(x_1);
x_226 = l_Lean_Json_Parser_hexChar___closed__0;
if (lean_is_scalar(x_221)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_221;
 lean_ctor_set_tag(x_227, 1);
}
lean_ctor_set(x_227, 0, x_219);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
else
{
lean_object* x_228; uint32_t x_229; lean_object* x_230; lean_object* x_231; uint32_t x_232; uint8_t x_233; 
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_228 = x_219;
} else {
 lean_dec_ref(x_219);
 x_228 = lean_box(0);
}
x_229 = lean_string_utf8_get_fast(x_222, x_223);
x_230 = lean_string_utf8_next_fast(x_222, x_223);
lean_dec(x_223);
if (lean_is_scalar(x_228)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_228;
}
lean_ctor_set(x_231, 0, x_222);
lean_ctor_set(x_231, 1, x_230);
x_232 = 125;
x_233 = lean_uint32_dec_eq(x_229, x_232);
if (x_233 == 0)
{
uint32_t x_234; uint8_t x_235; 
x_234 = 44;
x_235 = lean_uint32_dec_eq(x_229, x_234);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_220);
lean_dec(x_198);
lean_dec(x_1);
x_236 = l_Lean_Json_Parser_objectCore___closed__2;
if (lean_is_scalar(x_221)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_221;
 lean_ctor_set_tag(x_237, 1);
}
lean_ctor_set(x_237, 0, x_231);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_221);
x_238 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_231);
x_239 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_198, x_220);
x_1 = x_239;
x_2 = x_238;
goto _start;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_231);
x_242 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_198, x_220);
if (lean_is_scalar(x_221)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_221;
}
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_198);
lean_dec(x_1);
x_244 = lean_ctor_get(x_218, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_218, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_246 = x_218;
} else {
 lean_dec_ref(x_218);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_1);
x_248 = lean_ctor_get(x_196, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_196, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_250 = x_196;
} else {
 lean_dec_ref(x_196);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_any___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected end of input", 21, 21);
return x_1;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_byte_size(x_5);
lean_dec(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
x_12 = l_Lean_Json_Parser_any___closed__0;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = l_Lean_Json_Parser_any___closed__0;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
x_3 = l_Std_Internal_Parsec_String_Parser_run___redArg(x_2, x_1);
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
l_Lean_Json_Parser_hexChar___closed__0 = _init_l_Lean_Json_Parser_hexChar___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_hexChar___closed__0);
l_Lean_Json_Parser_hexChar___closed__1 = _init_l_Lean_Json_Parser_hexChar___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_hexChar___closed__1);
l_Lean_Json_Parser_finishSurrogatePair___closed__0 = _init_l_Lean_Json_Parser_finishSurrogatePair___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_finishSurrogatePair___closed__0);
l_Lean_Json_Parser_escapedChar___closed__0 = _init_l_Lean_Json_Parser_escapedChar___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___closed__0);
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
l_Lean_Json_Parser_escapedChar___boxed__const__9 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__9();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__9);
l_Lean_Json_Parser_strCore___closed__0 = _init_l_Lean_Json_Parser_strCore___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_strCore___closed__0);
l_Lean_Json_Parser_lookahead___redArg___closed__0 = _init_l_Lean_Json_Parser_lookahead___redArg___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_lookahead___redArg___closed__0);
l_Lean_Json_Parser_natNonZero___closed__0 = _init_l_Lean_Json_Parser_natNonZero___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_natNonZero___closed__0);
l_Lean_Json_Parser_natNumDigits___closed__0 = _init_l_Lean_Json_Parser_natNumDigits___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_natNumDigits___closed__0);
l_Lean_Json_Parser_natMaybeZero___closed__0 = _init_l_Lean_Json_Parser_natMaybeZero___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_natMaybeZero___closed__0);
l_Lean_Json_Parser_numSign___closed__0 = _init_l_Lean_Json_Parser_numSign___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_numSign___closed__0);
l_Lean_Json_Parser_numSign___closed__1 = _init_l_Lean_Json_Parser_numSign___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_numSign___closed__1);
l_Lean_Json_Parser_numWithDecimals___closed__0 = _init_l_Lean_Json_Parser_numWithDecimals___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_numWithDecimals___closed__0);
l_Lean_Json_Parser_numWithDecimals___closed__1 = _init_l_Lean_Json_Parser_numWithDecimals___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_numWithDecimals___closed__1);
l_Lean_Json_Parser_exponent___closed__0 = _init_l_Lean_Json_Parser_exponent___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_exponent___closed__0);
l_Lean_Json_Parser_arrayCore___closed__0 = _init_l_Lean_Json_Parser_arrayCore___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_arrayCore___closed__0);
l_Lean_Json_Parser_anyCore___closed__0 = _init_l_Lean_Json_Parser_anyCore___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___closed__0);
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
l_Lean_Json_Parser_objectCore___closed__0 = _init_l_Lean_Json_Parser_objectCore___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_objectCore___closed__0);
l_Lean_Json_Parser_objectCore___closed__1 = _init_l_Lean_Json_Parser_objectCore___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_objectCore___closed__1);
l_Lean_Json_Parser_objectCore___closed__2 = _init_l_Lean_Json_Parser_objectCore___closed__2();
lean_mark_persistent(l_Lean_Json_Parser_objectCore___closed__2);
l_Lean_Json_Parser_any___closed__0 = _init_l_Lean_Json_Parser_any___closed__0();
lean_mark_persistent(l_Lean_Json_Parser_any___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

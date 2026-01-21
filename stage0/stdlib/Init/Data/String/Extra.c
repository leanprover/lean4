// Lean compiler output
// Module: Init.Data.String.Extra
// Imports: import all Init.Data.ByteArray.Basic public import Init.Data.String.Basic import all Init.Data.String.Basic public import Init.Data.String.Substring public import Init.Data.String.Modify import Init.Data.String.Search
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___boxed(lean_object*, lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_removeLeadingSpaces(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_crlfToLf_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT uint8_t l_String_validateUTF8(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_crlfToLf(lean_object*);
LEAN_EXPORT lean_object* l_String_crlfToLf___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_next_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_validateUTF8___boxed(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_crlfToLf_go(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_byte_array_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_byte_array_fget(x_1, x_2);
x_7 = 128;
x_8 = lean_uint8_land(x_6, x_7);
x_9 = 0;
x_10 = lean_uint8_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_11 = 224;
x_12 = lean_uint8_land(x_6, x_11);
x_13 = 192;
x_14 = lean_uint8_dec_eq(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; 
x_15 = 240;
x_16 = lean_uint8_land(x_6, x_15);
x_17 = lean_uint8_dec_eq(x_16, x_11);
if (x_17 == 0)
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_18 = 248;
x_19 = lean_uint8_land(x_6, x_18);
x_20 = lean_uint8_dec_eq(x_19, x_15);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(3u);
x_23 = lean_nat_add(x_2, x_22);
x_24 = lean_nat_dec_lt(x_23, x_3);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
x_25 = lean_box(0);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_2, x_26);
x_28 = lean_byte_array_fget(x_1, x_27);
lean_dec(x_27);
x_29 = lean_uint8_land(x_28, x_13);
x_30 = lean_uint8_dec_eq(x_29, x_7);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_23);
x_31 = lean_box(0);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; 
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_add(x_2, x_32);
x_34 = lean_byte_array_fget(x_1, x_33);
lean_dec(x_33);
x_35 = lean_uint8_land(x_34, x_13);
x_36 = lean_uint8_dec_eq(x_35, x_7);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_23);
x_37 = lean_box(0);
return x_37;
}
else
{
uint8_t x_38; uint8_t x_39; uint8_t x_40; 
x_38 = lean_byte_array_fget(x_1, x_23);
lean_dec(x_23);
x_39 = lean_uint8_land(x_38, x_13);
x_40 = lean_uint8_dec_eq(x_39, x_7);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_box(0);
return x_41;
}
else
{
uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint32_t x_48; uint32_t x_49; uint32_t x_50; uint32_t x_51; uint32_t x_52; uint32_t x_53; uint32_t x_54; uint32_t x_55; uint32_t x_56; uint32_t x_57; uint32_t x_58; uint32_t x_59; uint32_t x_60; uint32_t x_61; uint8_t x_62; 
x_42 = 7;
x_43 = lean_uint8_land(x_6, x_42);
x_44 = 63;
x_45 = lean_uint8_land(x_28, x_44);
x_46 = lean_uint8_land(x_34, x_44);
x_47 = lean_uint8_land(x_38, x_44);
x_48 = lean_uint8_to_uint32(x_43);
x_49 = 18;
x_50 = lean_uint32_shift_left(x_48, x_49);
x_51 = lean_uint8_to_uint32(x_45);
x_52 = 12;
x_53 = lean_uint32_shift_left(x_51, x_52);
x_54 = lean_uint32_lor(x_50, x_53);
x_55 = lean_uint8_to_uint32(x_46);
x_56 = 6;
x_57 = lean_uint32_shift_left(x_55, x_56);
x_58 = lean_uint32_lor(x_54, x_57);
x_59 = lean_uint8_to_uint32(x_47);
x_60 = lean_uint32_lor(x_58, x_59);
x_61 = 65536;
x_62 = lean_uint32_dec_lt(x_60, x_61);
if (x_62 == 0)
{
uint32_t x_63; uint8_t x_64; 
x_63 = 1114111;
x_64 = lean_uint32_dec_lt(x_63, x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_box_uint32(x_60);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
else
{
lean_object* x_67; 
x_67 = lean_box(0);
return x_67;
}
}
else
{
lean_object* x_68; 
x_68 = lean_box(0);
return x_68;
}
}
}
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_unsigned_to_nat(2u);
x_70 = lean_nat_add(x_2, x_69);
x_71 = lean_nat_dec_lt(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_70);
x_72 = lean_box(0);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; 
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_2, x_73);
x_75 = lean_byte_array_fget(x_1, x_74);
lean_dec(x_74);
x_76 = lean_uint8_land(x_75, x_13);
x_77 = lean_uint8_dec_eq(x_76, x_7);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_70);
x_78 = lean_box(0);
return x_78;
}
else
{
uint8_t x_79; uint8_t x_80; uint8_t x_81; 
x_79 = lean_byte_array_fget(x_1, x_70);
lean_dec(x_70);
x_80 = lean_uint8_land(x_79, x_13);
x_81 = lean_uint8_dec_eq(x_80, x_7);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_box(0);
return x_82;
}
else
{
uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint32_t x_88; uint32_t x_89; uint32_t x_90; uint32_t x_91; uint32_t x_92; uint32_t x_93; uint32_t x_94; uint32_t x_95; uint32_t x_96; uint32_t x_97; uint8_t x_98; 
x_83 = 15;
x_84 = lean_uint8_land(x_6, x_83);
x_85 = 63;
x_86 = lean_uint8_land(x_75, x_85);
x_87 = lean_uint8_land(x_79, x_85);
x_88 = lean_uint8_to_uint32(x_84);
x_89 = 12;
x_90 = lean_uint32_shift_left(x_88, x_89);
x_91 = lean_uint8_to_uint32(x_86);
x_92 = 6;
x_93 = lean_uint32_shift_left(x_91, x_92);
x_94 = lean_uint32_lor(x_90, x_93);
x_95 = lean_uint8_to_uint32(x_87);
x_96 = lean_uint32_lor(x_94, x_95);
x_97 = 2048;
x_98 = lean_uint32_dec_lt(x_96, x_97);
if (x_98 == 0)
{
uint32_t x_99; uint8_t x_100; 
x_99 = 55296;
x_100 = lean_uint32_dec_le(x_99, x_96);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_box_uint32(x_96);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
else
{
uint32_t x_103; uint8_t x_104; 
x_103 = 57343;
x_104 = lean_uint32_dec_le(x_96, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_box_uint32(x_96);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
else
{
lean_object* x_107; 
x_107 = lean_box(0);
return x_107;
}
}
}
else
{
lean_object* x_108; 
x_108 = lean_box(0);
return x_108;
}
}
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_unsigned_to_nat(1u);
x_110 = lean_nat_add(x_2, x_109);
x_111 = lean_nat_dec_lt(x_110, x_3);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_110);
x_112 = lean_box(0);
return x_112;
}
else
{
uint8_t x_113; uint8_t x_114; uint8_t x_115; 
x_113 = lean_byte_array_fget(x_1, x_110);
lean_dec(x_110);
x_114 = lean_uint8_land(x_113, x_13);
x_115 = lean_uint8_dec_eq(x_114, x_7);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_box(0);
return x_116;
}
else
{
uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint32_t x_121; uint32_t x_122; uint32_t x_123; uint32_t x_124; uint32_t x_125; uint32_t x_126; uint8_t x_127; 
x_117 = 31;
x_118 = lean_uint8_land(x_6, x_117);
x_119 = 63;
x_120 = lean_uint8_land(x_113, x_119);
x_121 = lean_uint8_to_uint32(x_118);
x_122 = 6;
x_123 = lean_uint32_shift_left(x_121, x_122);
x_124 = lean_uint8_to_uint32(x_120);
x_125 = lean_uint32_lor(x_123, x_124);
x_126 = 128;
x_127 = lean_uint32_dec_lt(x_125, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_box_uint32(x_125);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
else
{
lean_object* x_130; 
x_130 = lean_box(0);
return x_130;
}
}
}
}
}
else
{
uint32_t x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_uint8_to_uint32(x_6);
x_132 = lean_box_uint32(x_131);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
}
}
}
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_utf8DecodeChar_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_validateUTF8(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_string_validate_utf8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_validateUTF8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_validateUTF8(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; uint32_t x_22; uint8_t x_23; 
x_7 = lean_string_utf8_get_fast(x_1, x_2);
x_22 = 32;
x_23 = lean_uint32_dec_eq(x_7, x_22);
if (x_23 == 0)
{
uint32_t x_24; uint8_t x_25; 
x_24 = 9;
x_25 = lean_uint32_dec_eq(x_7, x_24);
x_8 = x_25;
goto block_21;
}
else
{
x_8 = x_23;
goto block_21;
}
block_21:
{
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 10;
x_10 = lean_uint32_dec_eq(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_12 = lean_nat_dec_le(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(x_1, x_11, x_4);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(x_1, x_11, x_3);
lean_dec(x_3);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_16 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(x_1, x_15, x_4);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_2 = x_17;
x_3 = x_19;
goto _start;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get_fast(x_1, x_2);
x_7 = 10;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(x_1, x_11, x_12, x_3);
return x_13;
}
}
else
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_nat_sub(x_7, x_6);
x_9 = lean_nat_dec_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = lean_string_utf8_get_fast(x_2, x_4);
x_11 = 10;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_string_utf8_next_fast(x_2, x_4);
lean_dec(x_4);
{
lean_object* _tmp_3 = x_13;
lean_object* _tmp_4 = x_3;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
else
{
lean_dec(x_4);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = lean_box(0);
x_6 = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(x_4, x_1, x_5, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_String_Slice_Pos_next_x3f(x_4, x_7);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_string_length(x_1);
x_11 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(x_1, x_9, x_2, x_10);
lean_dec_ref(x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(x_1, x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 1)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(x_1, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_string_utf8_byte_size(x_3);
x_10 = lean_nat_dec_eq(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint32_t x_18; uint32_t x_19; uint8_t x_20; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
lean_dec(x_2);
x_18 = lean_string_utf8_get_fast(x_3, x_4);
x_19 = 32;
x_20 = lean_uint32_dec_eq(x_18, x_19);
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 9;
x_22 = lean_uint32_dec_eq(x_18, x_21);
x_13 = x_22;
goto block_17;
}
else
{
x_13 = x_20;
goto block_17;
}
block_17:
{
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(x_1, x_3, x_4, x_5);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_2 = x_12;
x_4 = x_15;
goto _start;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get_fast(x_2, x_3);
x_8 = 10;
x_9 = lean_uint32_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_11 = lean_string_push(x_4, x_7);
x_3 = x_10;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_14 = lean_string_push(x_4, x_8);
lean_inc(x_1);
x_15 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(x_1, x_1, x_2, x_13, x_14);
return x_15;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0;
lean_inc(x_1);
x_5 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(x_1, x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_removeLeadingSpaces(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
lean_inc_ref(x_1);
x_2 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(x_2, x_1);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_crlfToLf_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_4);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; uint8_t x_20; 
x_6 = lean_string_utf8_get_fast(x_1, x_4);
x_7 = lean_string_utf8_next_fast(x_1, x_4);
x_20 = lean_string_utf8_at_end(x_1, x_7);
if (x_20 == 0)
{
goto block_19;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
x_4 = x_7;
goto _start;
}
else
{
goto block_19;
}
}
block_19:
{
uint32_t x_8; uint8_t x_9; 
x_8 = 13;
x_9 = lean_uint32_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_dec(x_4);
x_4 = x_7;
goto _start;
}
else
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get(x_1, x_7);
x_12 = 10;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_4);
x_4 = x_7;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_utf8_extract(x_1, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_string_append(x_2, x_15);
lean_dec_ref(x_15);
x_17 = lean_string_utf8_next_fast(x_1, x_7);
x_2 = x_16;
x_3 = x_7;
x_4 = x_17;
goto _start;
}
}
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_3, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_string_utf8_extract(x_1, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_string_append(x_2, x_24);
lean_dec_ref(x_24);
return x_25;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_crlfToLf_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Extra_0__String_crlfToLf_go(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_crlfToLf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Init_Data_String_Extra_0__String_crlfToLf_go(x_1, x_2, x_3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_crlfToLf___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_crlfToLf(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Substring(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Extra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0 = _init_l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0();
lean_mark_persistent(l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

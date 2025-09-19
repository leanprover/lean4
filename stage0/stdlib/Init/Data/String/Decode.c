// Lean compiler output
// Module: Init.Data.String.Decode
// Imports: Init.Data.List.Lemmas Init.Data.List.Lemmas Init.Data.UInt.Bitwise Init.Data.Char.Lemmas Init.Data.ByteArray.Basic Init.Data.ByteArray.Lemmas
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
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(uint8_t, uint8_t);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(uint8_t, uint8_t, uint8_t);
uint32_t lean_uint8_to_uint32(uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(lean_object*, uint8_t, lean_object*, lean_object*);
uint32_t lean_uint32_shift_right(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg(lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_parseFirstByte___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8EncodeCharFast(uint32_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(uint8_t);
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(lean_object*, uint8_t, lean_object*, lean_object*);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_toCtorIdx(uint8_t);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8EncodeCharFast___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8EncodeCharFast(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 127;
x_3 = lean_uint32_dec_le(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 2047;
x_5 = lean_uint32_dec_le(x_1, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 65535;
x_7 = lean_uint32_dec_le(x_1, x_6);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint32_t x_15; uint32_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint32_t x_22; uint32_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_8 = 18;
x_9 = lean_uint32_shift_right(x_1, x_8);
x_10 = lean_uint32_to_uint8(x_9);
x_11 = 7;
x_12 = lean_uint8_land(x_10, x_11);
x_13 = 240;
x_14 = lean_uint8_lor(x_12, x_13);
x_15 = 12;
x_16 = lean_uint32_shift_right(x_1, x_15);
x_17 = lean_uint32_to_uint8(x_16);
x_18 = 63;
x_19 = lean_uint8_land(x_17, x_18);
x_20 = 128;
x_21 = lean_uint8_lor(x_19, x_20);
x_22 = 6;
x_23 = lean_uint32_shift_right(x_1, x_22);
x_24 = lean_uint32_to_uint8(x_23);
x_25 = lean_uint8_land(x_24, x_18);
x_26 = lean_uint8_lor(x_25, x_20);
x_27 = lean_uint32_to_uint8(x_1);
x_28 = lean_uint8_land(x_27, x_18);
x_29 = lean_uint8_lor(x_28, x_20);
x_30 = lean_box(0);
x_31 = lean_box(x_29);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_box(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_box(x_21);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_box(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
else
{
uint32_t x_39; uint32_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint32_t x_46; uint32_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_39 = 12;
x_40 = lean_uint32_shift_right(x_1, x_39);
x_41 = lean_uint32_to_uint8(x_40);
x_42 = 15;
x_43 = lean_uint8_land(x_41, x_42);
x_44 = 224;
x_45 = lean_uint8_lor(x_43, x_44);
x_46 = 6;
x_47 = lean_uint32_shift_right(x_1, x_46);
x_48 = lean_uint32_to_uint8(x_47);
x_49 = 63;
x_50 = lean_uint8_land(x_48, x_49);
x_51 = 128;
x_52 = lean_uint8_lor(x_50, x_51);
x_53 = lean_uint32_to_uint8(x_1);
x_54 = lean_uint8_land(x_53, x_49);
x_55 = lean_uint8_lor(x_54, x_51);
x_56 = lean_box(0);
x_57 = lean_box(x_55);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_box(x_52);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_box(x_45);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
uint32_t x_63; uint32_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_63 = 6;
x_64 = lean_uint32_shift_right(x_1, x_63);
x_65 = lean_uint32_to_uint8(x_64);
x_66 = 31;
x_67 = lean_uint8_land(x_65, x_66);
x_68 = 192;
x_69 = lean_uint8_lor(x_67, x_68);
x_70 = lean_uint32_to_uint8(x_1);
x_71 = 63;
x_72 = lean_uint8_land(x_70, x_71);
x_73 = 128;
x_74 = lean_uint8_lor(x_72, x_73);
x_75 = lean_box(0);
x_76 = lean_box(x_74);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_box(x_69);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_uint32_to_uint8(x_1);
x_81 = lean_box(0);
x_82 = lean_box(x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
LEAN_EXPORT lean_object* l_String_utf8EncodeCharFast___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_String_utf8EncodeCharFast(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_ByteArray_utf8DecodeChar_x3f_FirstByte_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_2 = 128;
x_3 = lean_uint8_land(x_1, x_2);
x_4 = 0;
x_5 = lean_uint8_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_6 = 224;
x_7 = lean_uint8_land(x_1, x_6);
x_8 = 192;
x_9 = lean_uint8_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_10 = 240;
x_11 = lean_uint8_land(x_1, x_10);
x_12 = lean_uint8_dec_eq(x_11, x_6);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_13 = 248;
x_14 = lean_uint8_land(x_1, x_13);
x_15 = lean_uint8_dec_eq(x_14, x_10);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = 4;
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = 3;
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = 2;
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_parseFirstByte___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_2 = 192;
x_3 = lean_uint8_land(x_1, x_2);
x_4 = 128;
x_5 = lean_uint8_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(uint8_t x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_uint8_to_uint32(x_1);
x_3 = lean_box_uint32(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(uint8_t x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_uint8_to_uint32(x_1);
x_4 = lean_box_uint32(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint32_t x_7; uint32_t x_8; uint32_t x_9; uint32_t x_10; uint32_t x_11; 
x_3 = 31;
x_4 = lean_uint8_land(x_1, x_3);
x_5 = 63;
x_6 = lean_uint8_land(x_2, x_5);
x_7 = lean_uint8_to_uint32(x_4);
x_8 = 6;
x_9 = lean_uint32_shift_left(x_7, x_8);
x_10 = lean_uint8_to_uint32(x_6);
x_11 = lean_uint32_lor(x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_3 = 192;
x_4 = lean_uint8_land(x_2, x_3);
x_5 = 128;
x_6 = lean_uint8_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint32_t x_12; uint32_t x_13; uint32_t x_14; uint32_t x_15; uint32_t x_16; uint32_t x_17; uint8_t x_18; 
x_8 = 31;
x_9 = lean_uint8_land(x_1, x_8);
x_10 = 63;
x_11 = lean_uint8_land(x_2, x_10);
x_12 = lean_uint8_to_uint32(x_9);
x_13 = 6;
x_14 = lean_uint32_shift_left(x_12, x_13);
x_15 = lean_uint8_to_uint32(x_11);
x_16 = lean_uint32_lor(x_14, x_15);
x_17 = 128;
x_18 = lean_uint32_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box_uint32(x_16);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_box(0);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(uint8_t x_1, uint8_t x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint32_t x_9; uint32_t x_10; uint32_t x_11; uint32_t x_12; uint32_t x_13; uint32_t x_14; uint32_t x_15; uint32_t x_16; uint32_t x_17; 
x_4 = 15;
x_5 = lean_uint8_land(x_1, x_4);
x_6 = 63;
x_7 = lean_uint8_land(x_2, x_6);
x_8 = lean_uint8_land(x_3, x_6);
x_9 = lean_uint8_to_uint32(x_5);
x_10 = 12;
x_11 = lean_uint32_shift_left(x_9, x_10);
x_12 = lean_uint8_to_uint32(x_7);
x_13 = 6;
x_14 = lean_uint32_shift_left(x_12, x_13);
x_15 = lean_uint32_lor(x_11, x_14);
x_16 = lean_uint8_to_uint32(x_8);
x_17 = lean_uint32_lor(x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; uint32_t x_7; lean_object* x_8; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(x_4, x_5, x_6);
x_8 = lean_box_uint32(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(uint8_t x_1, uint8_t x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_4 = 192;
x_5 = lean_uint8_land(x_2, x_4);
x_6 = 128;
x_7 = lean_uint8_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; uint8_t x_10; 
x_9 = lean_uint8_land(x_3, x_4);
x_10 = lean_uint8_dec_eq(x_9, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint32_t x_17; uint32_t x_18; uint32_t x_19; uint32_t x_20; uint32_t x_21; uint32_t x_22; uint32_t x_23; uint32_t x_24; uint32_t x_25; uint32_t x_26; uint8_t x_27; 
x_12 = 15;
x_13 = lean_uint8_land(x_1, x_12);
x_14 = 63;
x_15 = lean_uint8_land(x_2, x_14);
x_16 = lean_uint8_land(x_3, x_14);
x_17 = lean_uint8_to_uint32(x_13);
x_18 = 12;
x_19 = lean_uint32_shift_left(x_17, x_18);
x_20 = lean_uint8_to_uint32(x_15);
x_21 = 6;
x_22 = lean_uint32_shift_left(x_20, x_21);
x_23 = lean_uint32_lor(x_19, x_22);
x_24 = lean_uint8_to_uint32(x_16);
x_25 = lean_uint32_lor(x_23, x_24);
x_26 = 2048;
x_27 = lean_uint32_dec_lt(x_25, x_26);
if (x_27 == 0)
{
uint32_t x_28; uint8_t x_29; 
x_28 = 55296;
x_29 = lean_uint32_dec_le(x_28, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box_uint32(x_25);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
uint32_t x_32; uint8_t x_33; 
x_32 = 57343;
x_33 = lean_uint32_dec_le(x_25, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box_uint32(x_25);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = lean_box(0);
return x_36;
}
}
}
else
{
lean_object* x_37; 
x_37 = lean_box(0);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(uint8_t x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint32_t x_11; uint32_t x_12; uint32_t x_13; uint32_t x_14; uint32_t x_15; uint32_t x_16; uint32_t x_17; uint32_t x_18; uint32_t x_19; uint32_t x_20; uint32_t x_21; uint32_t x_22; uint32_t x_23; 
x_5 = 7;
x_6 = lean_uint8_land(x_1, x_5);
x_7 = 63;
x_8 = lean_uint8_land(x_2, x_7);
x_9 = lean_uint8_land(x_3, x_7);
x_10 = lean_uint8_land(x_4, x_7);
x_11 = lean_uint8_to_uint32(x_6);
x_12 = 18;
x_13 = lean_uint32_shift_left(x_11, x_12);
x_14 = lean_uint8_to_uint32(x_8);
x_15 = 12;
x_16 = lean_uint32_shift_left(x_14, x_15);
x_17 = lean_uint32_lor(x_13, x_16);
x_18 = lean_uint8_to_uint32(x_9);
x_19 = 6;
x_20 = lean_uint32_shift_left(x_18, x_19);
x_21 = lean_uint32_lor(x_17, x_20);
x_22 = lean_uint8_to_uint32(x_10);
x_23 = lean_uint32_lor(x_21, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint32_t x_9; lean_object* x_10; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = lean_unbox(x_4);
x_9 = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(x_5, x_6, x_7, x_8);
x_10 = lean_box_uint32(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(uint8_t x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_5 = 192;
x_6 = lean_uint8_land(x_2, x_5);
x_7 = 128;
x_8 = lean_uint8_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; uint8_t x_11; 
x_10 = lean_uint8_land(x_3, x_5);
x_11 = lean_uint8_dec_eq(x_10, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; uint8_t x_14; 
x_13 = lean_uint8_land(x_4, x_5);
x_14 = lean_uint8_dec_eq(x_13, x_7);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
else
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint32_t x_22; uint32_t x_23; uint32_t x_24; uint32_t x_25; uint32_t x_26; uint32_t x_27; uint32_t x_28; uint32_t x_29; uint32_t x_30; uint32_t x_31; uint32_t x_32; uint32_t x_33; uint32_t x_34; uint32_t x_35; uint8_t x_36; 
x_16 = 7;
x_17 = lean_uint8_land(x_1, x_16);
x_18 = 63;
x_19 = lean_uint8_land(x_2, x_18);
x_20 = lean_uint8_land(x_3, x_18);
x_21 = lean_uint8_land(x_4, x_18);
x_22 = lean_uint8_to_uint32(x_17);
x_23 = 18;
x_24 = lean_uint32_shift_left(x_22, x_23);
x_25 = lean_uint8_to_uint32(x_19);
x_26 = 12;
x_27 = lean_uint32_shift_left(x_25, x_26);
x_28 = lean_uint32_lor(x_24, x_27);
x_29 = lean_uint8_to_uint32(x_20);
x_30 = 6;
x_31 = lean_uint32_shift_left(x_29, x_30);
x_32 = lean_uint32_lor(x_28, x_31);
x_33 = lean_uint8_to_uint32(x_21);
x_34 = lean_uint32_lor(x_32, x_33);
x_35 = 65536;
x_36 = lean_uint32_dec_lt(x_34, x_35);
if (x_36 == 0)
{
uint32_t x_37; uint8_t x_38; 
x_37 = 1114111;
x_38 = lean_uint32_dec_lt(x_37, x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box_uint32(x_34);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = lean_box(0);
return x_41;
}
}
else
{
lean_object* x_42; 
x_42 = lean_box(0);
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = lean_unbox(x_4);
x_9 = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_byte_array_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
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
lean_dec(x_3);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(3u);
x_23 = lean_nat_add(x_2, x_22);
x_24 = lean_nat_dec_lt(x_23, x_3);
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
x_131 = lean_uint8_to_uint32(x_6);
x_132 = lean_box_uint32(x_131);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ByteArray_utf8DecodeChar_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_apply_1(x_2, lean_box(0));
return x_7;
}
case 1:
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, lean_box(0));
return x_8;
}
case 2:
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_apply_1(x_4, lean_box(0));
return x_9;
}
case 3:
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_apply_1(x_5, lean_box(0));
return x_10;
}
default: 
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_apply_1(x_6, lean_box(0));
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_byte_array_fget(x_1, x_2);
x_4 = 128;
x_5 = lean_uint8_land(x_3, x_4);
x_6 = 0;
x_7 = lean_uint8_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_8 = 224;
x_9 = lean_uint8_land(x_3, x_8);
x_10 = 192;
x_11 = lean_uint8_dec_eq(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_12 = 240;
x_13 = lean_uint8_land(x_3, x_12);
x_14 = lean_uint8_dec_eq(x_13, x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint32_t x_30; uint32_t x_31; uint32_t x_32; uint32_t x_33; uint32_t x_34; uint32_t x_35; uint32_t x_36; uint32_t x_37; uint32_t x_38; uint32_t x_39; uint32_t x_40; uint32_t x_41; uint32_t x_42; 
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_add(x_2, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
x_19 = lean_byte_array_fget(x_1, x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = lean_byte_array_fget(x_1, x_21);
lean_dec(x_21);
x_23 = lean_byte_array_fget(x_1, x_16);
lean_dec(x_16);
x_24 = 7;
x_25 = lean_uint8_land(x_3, x_24);
x_26 = 63;
x_27 = lean_uint8_land(x_19, x_26);
x_28 = lean_uint8_land(x_22, x_26);
x_29 = lean_uint8_land(x_23, x_26);
x_30 = lean_uint8_to_uint32(x_25);
x_31 = 18;
x_32 = lean_uint32_shift_left(x_30, x_31);
x_33 = lean_uint8_to_uint32(x_27);
x_34 = 12;
x_35 = lean_uint32_shift_left(x_33, x_34);
x_36 = lean_uint32_lor(x_32, x_35);
x_37 = lean_uint8_to_uint32(x_28);
x_38 = 6;
x_39 = lean_uint32_shift_left(x_37, x_38);
x_40 = lean_uint32_lor(x_36, x_39);
x_41 = lean_uint8_to_uint32(x_29);
x_42 = lean_uint32_lor(x_40, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint32_t x_54; uint32_t x_55; uint32_t x_56; uint32_t x_57; uint32_t x_58; uint32_t x_59; uint32_t x_60; uint32_t x_61; uint32_t x_62; uint32_t x_63; uint8_t x_64; 
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_add(x_2, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_2, x_45);
x_47 = lean_byte_array_fget(x_1, x_46);
lean_dec(x_46);
x_48 = lean_byte_array_fget(x_1, x_44);
lean_dec(x_44);
x_49 = 15;
x_50 = lean_uint8_land(x_3, x_49);
x_51 = 63;
x_52 = lean_uint8_land(x_47, x_51);
x_53 = lean_uint8_land(x_48, x_51);
x_54 = lean_uint8_to_uint32(x_50);
x_55 = 12;
x_56 = lean_uint32_shift_left(x_54, x_55);
x_57 = lean_uint8_to_uint32(x_52);
x_58 = 6;
x_59 = lean_uint32_shift_left(x_57, x_58);
x_60 = lean_uint32_lor(x_56, x_59);
x_61 = lean_uint8_to_uint32(x_53);
x_62 = lean_uint32_lor(x_60, x_61);
x_63 = 55296;
x_64 = lean_uint32_dec_le(x_63, x_62);
if (x_64 == 0)
{
return x_62;
}
else
{
return x_62;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint32_t x_72; uint32_t x_73; uint32_t x_74; uint32_t x_75; uint32_t x_76; 
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_2, x_65);
x_67 = lean_byte_array_fget(x_1, x_66);
lean_dec(x_66);
x_68 = 31;
x_69 = lean_uint8_land(x_3, x_68);
x_70 = 63;
x_71 = lean_uint8_land(x_67, x_70);
x_72 = lean_uint8_to_uint32(x_69);
x_73 = 6;
x_74 = lean_uint32_shift_left(x_72, x_73);
x_75 = lean_uint8_to_uint32(x_71);
x_76 = lean_uint32_lor(x_74, x_75);
return x_76;
}
}
else
{
uint32_t x_77; 
x_77 = lean_uint8_to_uint32(x_3);
return x_77;
}
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; 
x_4 = l_ByteArray_utf8DecodeChar___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_ByteArray_utf8DecodeChar___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = l_ByteArray_utf8DecodeChar(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_UInt_Bitwise(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Char_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Decode(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Bitwise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

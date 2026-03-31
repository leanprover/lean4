// Lean compiler output
// Module: Init.Data.String.Decode
// Imports: import Init.Data.Char.Lemmas public import Init.Data.ByteArray.Basic import Init.Data.ByteArray.Lemmas public import Init.Data.UInt.Basic import Init.Data.BitVec.Bootstrap import Init.Data.BitVec.Lemmas import Init.Data.Nat.Linear import Init.Data.Nat.MinMax import Init.Data.Option.Lemmas import Init.Data.UInt.Bitwise import Init.Data.UInt.Lemmas import Init.Omega
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
uint8_t lean_uint8_land(uint8_t, uint8_t);
uint32_t lean_uint8_to_uint32(uint8_t);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_shift_right(uint32_t, uint32_t);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_String_utf8EncodeCharFast(uint32_t);
LEAN_EXPORT lean_object* l_String_utf8EncodeCharFast___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_parseFirstByte___boxed(lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2081(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2081___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2082(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2082___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2083(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2083___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2084(uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2084___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8At(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8At___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt8_instDecidableIsUTF8FirstByte___aux__1(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_instDecidableIsUTF8FirstByte___aux__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt8_instDecidableIsUTF8FirstByte(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_instDecidableIsUTF8FirstByte___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8EncodeCharFast(uint32_t v_c_1_){
_start:
{
uint32_t v___x_2_; uint8_t v___x_3_; 
v___x_2_ = 127;
v___x_3_ = lean_uint32_dec_le(v_c_1_, v___x_2_);
if (v___x_3_ == 0)
{
uint32_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = 2047;
v___x_5_ = lean_uint32_dec_le(v_c_1_, v___x_4_);
if (v___x_5_ == 0)
{
uint32_t v___x_6_; uint8_t v___x_7_; 
v___x_6_ = 65535;
v___x_7_ = lean_uint32_dec_le(v_c_1_, v___x_6_);
if (v___x_7_ == 0)
{
uint32_t v___x_8_; uint32_t v___x_9_; uint8_t v___x_10_; uint8_t v___x_11_; uint8_t v___x_12_; uint8_t v___x_13_; uint8_t v___x_14_; uint32_t v___x_15_; uint32_t v___x_16_; uint8_t v___x_17_; uint8_t v___x_18_; uint8_t v___x_19_; uint8_t v___x_20_; uint8_t v___x_21_; uint32_t v___x_22_; uint32_t v___x_23_; uint8_t v___x_24_; uint8_t v___x_25_; uint8_t v___x_26_; uint8_t v___x_27_; uint8_t v___x_28_; uint8_t v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_8_ = 18;
v___x_9_ = lean_uint32_shift_right(v_c_1_, v___x_8_);
v___x_10_ = lean_uint32_to_uint8(v___x_9_);
v___x_11_ = 7;
v___x_12_ = lean_uint8_land(v___x_10_, v___x_11_);
v___x_13_ = 240;
v___x_14_ = lean_uint8_lor(v___x_12_, v___x_13_);
v___x_15_ = 12;
v___x_16_ = lean_uint32_shift_right(v_c_1_, v___x_15_);
v___x_17_ = lean_uint32_to_uint8(v___x_16_);
v___x_18_ = 63;
v___x_19_ = lean_uint8_land(v___x_17_, v___x_18_);
v___x_20_ = 128;
v___x_21_ = lean_uint8_lor(v___x_19_, v___x_20_);
v___x_22_ = 6;
v___x_23_ = lean_uint32_shift_right(v_c_1_, v___x_22_);
v___x_24_ = lean_uint32_to_uint8(v___x_23_);
v___x_25_ = lean_uint8_land(v___x_24_, v___x_18_);
v___x_26_ = lean_uint8_lor(v___x_25_, v___x_20_);
v___x_27_ = lean_uint32_to_uint8(v_c_1_);
v___x_28_ = lean_uint8_land(v___x_27_, v___x_18_);
v___x_29_ = lean_uint8_lor(v___x_28_, v___x_20_);
v___x_30_ = lean_box(0);
v___x_31_ = lean_box(v___x_29_);
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v___x_30_);
v___x_33_ = lean_box(v___x_26_);
v___x_34_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v___x_32_);
v___x_35_ = lean_box(v___x_21_);
v___x_36_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_34_);
v___x_37_ = lean_box(v___x_14_);
v___x_38_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
return v___x_38_;
}
else
{
uint32_t v___x_39_; uint32_t v___x_40_; uint8_t v___x_41_; uint8_t v___x_42_; uint8_t v___x_43_; uint8_t v___x_44_; uint8_t v___x_45_; uint32_t v___x_46_; uint32_t v___x_47_; uint8_t v___x_48_; uint8_t v___x_49_; uint8_t v___x_50_; uint8_t v___x_51_; uint8_t v___x_52_; uint8_t v___x_53_; uint8_t v___x_54_; uint8_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_39_ = 12;
v___x_40_ = lean_uint32_shift_right(v_c_1_, v___x_39_);
v___x_41_ = lean_uint32_to_uint8(v___x_40_);
v___x_42_ = 15;
v___x_43_ = lean_uint8_land(v___x_41_, v___x_42_);
v___x_44_ = 224;
v___x_45_ = lean_uint8_lor(v___x_43_, v___x_44_);
v___x_46_ = 6;
v___x_47_ = lean_uint32_shift_right(v_c_1_, v___x_46_);
v___x_48_ = lean_uint32_to_uint8(v___x_47_);
v___x_49_ = 63;
v___x_50_ = lean_uint8_land(v___x_48_, v___x_49_);
v___x_51_ = 128;
v___x_52_ = lean_uint8_lor(v___x_50_, v___x_51_);
v___x_53_ = lean_uint32_to_uint8(v_c_1_);
v___x_54_ = lean_uint8_land(v___x_53_, v___x_49_);
v___x_55_ = lean_uint8_lor(v___x_54_, v___x_51_);
v___x_56_ = lean_box(0);
v___x_57_ = lean_box(v___x_55_);
v___x_58_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v___x_56_);
v___x_59_ = lean_box(v___x_52_);
v___x_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
v___x_61_ = lean_box(v___x_45_);
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
return v___x_62_;
}
}
else
{
uint32_t v___x_63_; uint32_t v___x_64_; uint8_t v___x_65_; uint8_t v___x_66_; uint8_t v___x_67_; uint8_t v___x_68_; uint8_t v___x_69_; uint8_t v___x_70_; uint8_t v___x_71_; uint8_t v___x_72_; uint8_t v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_63_ = 6;
v___x_64_ = lean_uint32_shift_right(v_c_1_, v___x_63_);
v___x_65_ = lean_uint32_to_uint8(v___x_64_);
v___x_66_ = 31;
v___x_67_ = lean_uint8_land(v___x_65_, v___x_66_);
v___x_68_ = 192;
v___x_69_ = lean_uint8_lor(v___x_67_, v___x_68_);
v___x_70_ = lean_uint32_to_uint8(v_c_1_);
v___x_71_ = 63;
v___x_72_ = lean_uint8_land(v___x_70_, v___x_71_);
v___x_73_ = 128;
v___x_74_ = lean_uint8_lor(v___x_72_, v___x_73_);
v___x_75_ = lean_box(0);
v___x_76_ = lean_box(v___x_74_);
v___x_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_75_);
v___x_78_ = lean_box(v___x_69_);
v___x_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
return v___x_79_;
}
}
else
{
uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_80_ = lean_uint32_to_uint8(v_c_1_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_box(v___x_80_);
v___x_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_81_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_String_utf8EncodeCharFast___boxed(lean_object* v_c_84_){
_start:
{
uint32_t v_c_boxed_85_; lean_object* v_res_86_; 
v_c_boxed_85_ = lean_unbox_uint32(v_c_84_);
lean_dec(v_c_84_);
v_res_86_ = l_String_utf8EncodeCharFast(v_c_boxed_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx(uint8_t v_x_87_){
_start:
{
switch(v_x_87_)
{
case 0:
{
lean_object* v___x_88_; 
v___x_88_ = lean_unsigned_to_nat(0u);
return v___x_88_;
}
case 1:
{
lean_object* v___x_89_; 
v___x_89_ = lean_unsigned_to_nat(1u);
return v___x_89_;
}
case 2:
{
lean_object* v___x_90_; 
v___x_90_ = lean_unsigned_to_nat(2u);
return v___x_90_;
}
case 3:
{
lean_object* v___x_91_; 
v___x_91_ = lean_unsigned_to_nat(3u);
return v___x_91_;
}
default: 
{
lean_object* v___x_92_; 
v___x_92_ = lean_unsigned_to_nat(4u);
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___boxed(lean_object* v_x_93_){
_start:
{
uint8_t v_x_boxed_94_; lean_object* v_res_95_; 
v_x_boxed_94_ = lean_unbox(v_x_93_);
v_res_95_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx(v_x_boxed_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_toCtorIdx(uint8_t v_x_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx(v_x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_toCtorIdx___boxed(lean_object* v_x_98_){
_start:
{
uint8_t v_x_4__boxed_99_; lean_object* v_res_100_; 
v_x_4__boxed_99_ = lean_unbox(v_x_98_);
v_res_100_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_toCtorIdx(v_x_4__boxed_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg(lean_object* v_k_101_){
_start:
{
lean_inc(v_k_101_);
return v_k_101_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg___boxed(lean_object* v_k_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg(v_k_102_);
lean_dec(v_k_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim(lean_object* v_motive_104_, lean_object* v_ctorIdx_105_, uint8_t v_t_106_, lean_object* v_h_107_, lean_object* v_k_108_){
_start:
{
lean_inc(v_k_108_);
return v_k_108_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___boxed(lean_object* v_motive_109_, lean_object* v_ctorIdx_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_k_113_){
_start:
{
uint8_t v_t_boxed_114_; lean_object* v_res_115_; 
v_t_boxed_114_ = lean_unbox(v_t_111_);
v_res_115_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim(v_motive_109_, v_ctorIdx_110_, v_t_boxed_114_, v_h_112_, v_k_113_);
lean_dec(v_k_113_);
lean_dec(v_ctorIdx_110_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg(lean_object* v_invalid_116_){
_start:
{
lean_inc(v_invalid_116_);
return v_invalid_116_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg___boxed(lean_object* v_invalid_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg(v_invalid_117_);
lean_dec(v_invalid_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(lean_object* v_motive_119_, uint8_t v_t_120_, lean_object* v_h_121_, lean_object* v_invalid_122_){
_start:
{
lean_inc(v_invalid_122_);
return v_invalid_122_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___boxed(lean_object* v_motive_123_, lean_object* v_t_124_, lean_object* v_h_125_, lean_object* v_invalid_126_){
_start:
{
uint8_t v_t_boxed_127_; lean_object* v_res_128_; 
v_t_boxed_127_ = lean_unbox(v_t_124_);
v_res_128_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(v_motive_123_, v_t_boxed_127_, v_h_125_, v_invalid_126_);
lean_dec(v_invalid_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg(lean_object* v_done_129_){
_start:
{
lean_inc(v_done_129_);
return v_done_129_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg___boxed(lean_object* v_done_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg(v_done_130_);
lean_dec(v_done_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(lean_object* v_motive_132_, uint8_t v_t_133_, lean_object* v_h_134_, lean_object* v_done_135_){
_start:
{
lean_inc(v_done_135_);
return v_done_135_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___boxed(lean_object* v_motive_136_, lean_object* v_t_137_, lean_object* v_h_138_, lean_object* v_done_139_){
_start:
{
uint8_t v_t_boxed_140_; lean_object* v_res_141_; 
v_t_boxed_140_ = lean_unbox(v_t_137_);
v_res_141_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(v_motive_136_, v_t_boxed_140_, v_h_138_, v_done_139_);
lean_dec(v_done_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg(lean_object* v_oneMore_142_){
_start:
{
lean_inc(v_oneMore_142_);
return v_oneMore_142_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg___boxed(lean_object* v_oneMore_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg(v_oneMore_143_);
lean_dec(v_oneMore_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(lean_object* v_motive_145_, uint8_t v_t_146_, lean_object* v_h_147_, lean_object* v_oneMore_148_){
_start:
{
lean_inc(v_oneMore_148_);
return v_oneMore_148_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___boxed(lean_object* v_motive_149_, lean_object* v_t_150_, lean_object* v_h_151_, lean_object* v_oneMore_152_){
_start:
{
uint8_t v_t_boxed_153_; lean_object* v_res_154_; 
v_t_boxed_153_ = lean_unbox(v_t_150_);
v_res_154_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(v_motive_149_, v_t_boxed_153_, v_h_151_, v_oneMore_152_);
lean_dec(v_oneMore_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg(lean_object* v_twoMore_155_){
_start:
{
lean_inc(v_twoMore_155_);
return v_twoMore_155_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg___boxed(lean_object* v_twoMore_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg(v_twoMore_156_);
lean_dec(v_twoMore_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(lean_object* v_motive_158_, uint8_t v_t_159_, lean_object* v_h_160_, lean_object* v_twoMore_161_){
_start:
{
lean_inc(v_twoMore_161_);
return v_twoMore_161_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___boxed(lean_object* v_motive_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_twoMore_165_){
_start:
{
uint8_t v_t_boxed_166_; lean_object* v_res_167_; 
v_t_boxed_166_ = lean_unbox(v_t_163_);
v_res_167_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(v_motive_162_, v_t_boxed_166_, v_h_164_, v_twoMore_165_);
lean_dec(v_twoMore_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg(lean_object* v_threeMore_168_){
_start:
{
lean_inc(v_threeMore_168_);
return v_threeMore_168_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg___boxed(lean_object* v_threeMore_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg(v_threeMore_169_);
lean_dec(v_threeMore_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim(lean_object* v_motive_171_, uint8_t v_t_172_, lean_object* v_h_173_, lean_object* v_threeMore_174_){
_start:
{
lean_inc(v_threeMore_174_);
return v_threeMore_174_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___boxed(lean_object* v_motive_175_, lean_object* v_t_176_, lean_object* v_h_177_, lean_object* v_threeMore_178_){
_start:
{
uint8_t v_t_boxed_179_; lean_object* v_res_180_; 
v_t_boxed_179_ = lean_unbox(v_t_176_);
v_res_180_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim(v_motive_175_, v_t_boxed_179_, v_h_177_, v_threeMore_178_);
lean_dec(v_threeMore_178_);
return v_res_180_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(uint8_t v_b_181_){
_start:
{
uint8_t v___x_182_; uint8_t v___x_183_; uint8_t v___x_184_; uint8_t v___x_185_; 
v___x_182_ = 128;
v___x_183_ = lean_uint8_land(v_b_181_, v___x_182_);
v___x_184_ = 0;
v___x_185_ = lean_uint8_dec_eq(v___x_183_, v___x_184_);
if (v___x_185_ == 0)
{
uint8_t v___x_186_; uint8_t v___x_187_; uint8_t v___x_188_; uint8_t v___x_189_; 
v___x_186_ = 224;
v___x_187_ = lean_uint8_land(v_b_181_, v___x_186_);
v___x_188_ = 192;
v___x_189_ = lean_uint8_dec_eq(v___x_187_, v___x_188_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; uint8_t v___x_191_; uint8_t v___x_192_; 
v___x_190_ = 240;
v___x_191_ = lean_uint8_land(v_b_181_, v___x_190_);
v___x_192_ = lean_uint8_dec_eq(v___x_191_, v___x_186_);
if (v___x_192_ == 0)
{
uint8_t v___x_193_; uint8_t v___x_194_; uint8_t v___x_195_; 
v___x_193_ = 248;
v___x_194_ = lean_uint8_land(v_b_181_, v___x_193_);
v___x_195_ = lean_uint8_dec_eq(v___x_194_, v___x_190_);
if (v___x_195_ == 0)
{
uint8_t v___x_196_; 
v___x_196_ = 0;
return v___x_196_;
}
else
{
uint8_t v___x_197_; 
v___x_197_ = 4;
return v___x_197_;
}
}
else
{
uint8_t v___x_198_; 
v___x_198_ = 3;
return v___x_198_;
}
}
else
{
uint8_t v___x_199_; 
v___x_199_ = 2;
return v___x_199_;
}
}
else
{
uint8_t v___x_200_; 
v___x_200_ = 1;
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_parseFirstByte___boxed(lean_object* v_b_201_){
_start:
{
uint8_t v_b_boxed_202_; uint8_t v_res_203_; lean_object* v_r_204_; 
v_b_boxed_202_ = lean_unbox(v_b_201_);
v_res_203_ = l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(v_b_boxed_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(uint8_t v_b_205_){
_start:
{
uint8_t v___x_206_; uint8_t v___x_207_; uint8_t v___x_208_; uint8_t v___x_209_; 
v___x_206_ = 192;
v___x_207_ = lean_uint8_land(v_b_205_, v___x_206_);
v___x_208_ = 128;
v___x_209_ = lean_uint8_dec_eq(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
uint8_t v___x_210_; 
v___x_210_ = 1;
return v___x_210_;
}
else
{
uint8_t v___x_211_; 
v___x_211_ = 0;
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte___boxed(lean_object* v_b_212_){
_start:
{
uint8_t v_b_boxed_213_; uint8_t v_res_214_; lean_object* v_r_215_; 
v_b_boxed_213_ = lean_unbox(v_b_212_);
v_res_214_ = l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(v_b_boxed_213_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(uint8_t v_w_216_){
_start:
{
uint32_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = lean_uint8_to_uint32(v_w_216_);
v___x_218_ = lean_box_uint32(v___x_217_);
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg___boxed(lean_object* v_w_220_){
_start:
{
uint8_t v_w_boxed_221_; lean_object* v_res_222_; 
v_w_boxed_221_ = lean_unbox(v_w_220_);
v_res_222_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(v_w_boxed_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(uint8_t v_w_223_, lean_object* v_h_224_){
_start:
{
uint32_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_uint8_to_uint32(v_w_223_);
v___x_226_ = lean_box_uint32(v___x_225_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___boxed(lean_object* v_w_228_, lean_object* v_h_229_){
_start:
{
uint8_t v_w_boxed_230_; lean_object* v_res_231_; 
v_w_boxed_230_ = lean_unbox(v_w_228_);
v_res_231_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(v_w_boxed_230_, v_h_229_);
return v_res_231_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2081(uint8_t v_w_232_, uint8_t v___w_233_, lean_object* v___h_234_){
_start:
{
uint8_t v___x_235_; 
v___x_235_ = 1;
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2081___boxed(lean_object* v_w_236_, lean_object* v___w_237_, lean_object* v___h_238_){
_start:
{
uint8_t v_w_boxed_239_; uint8_t v___w_boxed_240_; uint8_t v_res_241_; lean_object* v_r_242_; 
v_w_boxed_239_ = lean_unbox(v_w_236_);
v___w_boxed_240_ = lean_unbox(v___w_237_);
v_res_241_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2081(v_w_boxed_239_, v___w_boxed_240_, v___h_238_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(uint8_t v_w_243_, uint8_t v_x_244_){
_start:
{
uint8_t v___x_245_; uint8_t v_b_u2080_246_; uint8_t v___x_247_; uint8_t v_b_u2081_248_; uint32_t v___x_249_; uint32_t v___x_250_; uint32_t v___x_251_; uint32_t v___x_252_; uint32_t v___x_253_; 
v___x_245_ = 31;
v_b_u2080_246_ = lean_uint8_land(v_w_243_, v___x_245_);
v___x_247_ = 63;
v_b_u2081_248_ = lean_uint8_land(v_x_244_, v___x_247_);
v___x_249_ = lean_uint8_to_uint32(v_b_u2080_246_);
v___x_250_ = 6;
v___x_251_ = lean_uint32_shift_left(v___x_249_, v___x_250_);
v___x_252_ = lean_uint8_to_uint32(v_b_u2081_248_);
v___x_253_ = lean_uint32_lor(v___x_251_, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked___boxed(lean_object* v_w_254_, lean_object* v_x_255_){
_start:
{
uint8_t v_w_boxed_256_; uint8_t v_x_boxed_257_; uint32_t v_res_258_; lean_object* v_r_259_; 
v_w_boxed_256_ = lean_unbox(v_w_254_);
v_x_boxed_257_ = lean_unbox(v_x_255_);
v_res_258_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(v_w_boxed_256_, v_x_boxed_257_);
v_r_259_ = lean_box_uint32(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(uint8_t v_w_260_, uint8_t v_x_261_){
_start:
{
uint8_t v___x_262_; uint8_t v___x_263_; uint8_t v___x_264_; uint8_t v___x_265_; 
v___x_262_ = 192;
v___x_263_ = lean_uint8_land(v_x_261_, v___x_262_);
v___x_264_ = 128;
v___x_265_ = lean_uint8_dec_eq(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
v___x_266_ = lean_box(0);
return v___x_266_;
}
else
{
uint8_t v___x_267_; uint8_t v_b_u2080_268_; uint8_t v___x_269_; uint8_t v_b_u2081_270_; uint32_t v___x_271_; uint32_t v___x_272_; uint32_t v___x_273_; uint32_t v___x_274_; uint32_t v_r_275_; uint32_t v___x_276_; uint8_t v___x_277_; 
v___x_267_ = 31;
v_b_u2080_268_ = lean_uint8_land(v_w_260_, v___x_267_);
v___x_269_ = 63;
v_b_u2081_270_ = lean_uint8_land(v_x_261_, v___x_269_);
v___x_271_ = lean_uint8_to_uint32(v_b_u2080_268_);
v___x_272_ = 6;
v___x_273_ = lean_uint32_shift_left(v___x_271_, v___x_272_);
v___x_274_ = lean_uint8_to_uint32(v_b_u2081_270_);
v_r_275_ = lean_uint32_lor(v___x_273_, v___x_274_);
v___x_276_ = 128;
v___x_277_ = lean_uint32_dec_lt(v_r_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_box_uint32(v_r_275_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; 
v___x_280_ = lean_box(0);
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082___boxed(lean_object* v_w_281_, lean_object* v_x_282_){
_start:
{
uint8_t v_w_boxed_283_; uint8_t v_x_boxed_284_; lean_object* v_res_285_; 
v_w_boxed_283_ = lean_unbox(v_w_281_);
v_x_boxed_284_ = lean_unbox(v_x_282_);
v_res_285_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(v_w_boxed_283_, v_x_boxed_284_);
return v_res_285_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2082(uint8_t v_w_286_, uint8_t v_x_287_){
_start:
{
uint8_t v___x_288_; uint8_t v___x_289_; uint8_t v___x_290_; uint8_t v___x_291_; 
v___x_288_ = 192;
v___x_289_ = lean_uint8_land(v_x_287_, v___x_288_);
v___x_290_ = 128;
v___x_291_ = lean_uint8_dec_eq(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
return v___x_291_;
}
else
{
uint8_t v___x_292_; uint8_t v_b_u2080_293_; uint8_t v___x_294_; uint8_t v_b_u2081_295_; uint32_t v___x_296_; uint32_t v___x_297_; uint32_t v___x_298_; uint32_t v___x_299_; uint32_t v_r_300_; uint32_t v___x_301_; uint8_t v___x_302_; 
v___x_292_ = 31;
v_b_u2080_293_ = lean_uint8_land(v_w_286_, v___x_292_);
v___x_294_ = 63;
v_b_u2081_295_ = lean_uint8_land(v_x_287_, v___x_294_);
v___x_296_ = lean_uint8_to_uint32(v_b_u2080_293_);
v___x_297_ = 6;
v___x_298_ = lean_uint32_shift_left(v___x_296_, v___x_297_);
v___x_299_ = lean_uint8_to_uint32(v_b_u2081_295_);
v_r_300_ = lean_uint32_lor(v___x_298_, v___x_299_);
v___x_301_ = 128;
v___x_302_ = lean_uint32_dec_le(v___x_301_, v_r_300_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2082___boxed(lean_object* v_w_303_, lean_object* v_x_304_){
_start:
{
uint8_t v_w_boxed_305_; uint8_t v_x_boxed_306_; uint8_t v_res_307_; lean_object* v_r_308_; 
v_w_boxed_305_ = lean_unbox(v_w_303_);
v_x_boxed_306_ = lean_unbox(v_x_304_);
v_res_307_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2082(v_w_boxed_305_, v_x_boxed_306_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(uint8_t v_w_309_, uint8_t v_x_310_, uint8_t v_y_311_){
_start:
{
uint8_t v___x_312_; uint8_t v_b_u2080_313_; uint8_t v___x_314_; uint8_t v_b_u2081_315_; uint8_t v_b_u2082_316_; uint32_t v___x_317_; uint32_t v___x_318_; uint32_t v___x_319_; uint32_t v___x_320_; uint32_t v___x_321_; uint32_t v___x_322_; uint32_t v___x_323_; uint32_t v___x_324_; uint32_t v___x_325_; 
v___x_312_ = 15;
v_b_u2080_313_ = lean_uint8_land(v_w_309_, v___x_312_);
v___x_314_ = 63;
v_b_u2081_315_ = lean_uint8_land(v_x_310_, v___x_314_);
v_b_u2082_316_ = lean_uint8_land(v_y_311_, v___x_314_);
v___x_317_ = lean_uint8_to_uint32(v_b_u2080_313_);
v___x_318_ = 12;
v___x_319_ = lean_uint32_shift_left(v___x_317_, v___x_318_);
v___x_320_ = lean_uint8_to_uint32(v_b_u2081_315_);
v___x_321_ = 6;
v___x_322_ = lean_uint32_shift_left(v___x_320_, v___x_321_);
v___x_323_ = lean_uint32_lor(v___x_319_, v___x_322_);
v___x_324_ = lean_uint8_to_uint32(v_b_u2082_316_);
v___x_325_ = lean_uint32_lor(v___x_323_, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked___boxed(lean_object* v_w_326_, lean_object* v_x_327_, lean_object* v_y_328_){
_start:
{
uint8_t v_w_boxed_329_; uint8_t v_x_boxed_330_; uint8_t v_y_boxed_331_; uint32_t v_res_332_; lean_object* v_r_333_; 
v_w_boxed_329_ = lean_unbox(v_w_326_);
v_x_boxed_330_ = lean_unbox(v_x_327_);
v_y_boxed_331_ = lean_unbox(v_y_328_);
v_res_332_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(v_w_boxed_329_, v_x_boxed_330_, v_y_boxed_331_);
v_r_333_ = lean_box_uint32(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(uint8_t v_w_334_, uint8_t v_x_335_, uint8_t v_y_336_){
_start:
{
uint8_t v___x_337_; uint8_t v___x_338_; uint8_t v___x_339_; uint8_t v___x_340_; 
v___x_337_ = 192;
v___x_338_ = lean_uint8_land(v_x_335_, v___x_337_);
v___x_339_ = 128;
v___x_340_ = lean_uint8_dec_eq(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
v___x_341_ = lean_box(0);
return v___x_341_;
}
else
{
uint8_t v___x_342_; uint8_t v___x_343_; 
v___x_342_ = lean_uint8_land(v_y_336_, v___x_337_);
v___x_343_ = lean_uint8_dec_eq(v___x_342_, v___x_339_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
v___x_344_ = lean_box(0);
return v___x_344_;
}
else
{
uint8_t v___x_345_; uint8_t v_b_u2080_346_; uint8_t v___x_347_; uint8_t v_b_u2081_348_; uint8_t v_b_u2082_349_; uint32_t v___x_350_; uint32_t v___x_351_; uint32_t v___x_352_; uint32_t v___x_353_; uint32_t v___x_354_; uint32_t v___x_355_; uint32_t v___x_356_; uint32_t v___x_357_; uint32_t v_r_358_; uint32_t v___x_359_; uint8_t v___x_360_; 
v___x_345_ = 15;
v_b_u2080_346_ = lean_uint8_land(v_w_334_, v___x_345_);
v___x_347_ = 63;
v_b_u2081_348_ = lean_uint8_land(v_x_335_, v___x_347_);
v_b_u2082_349_ = lean_uint8_land(v_y_336_, v___x_347_);
v___x_350_ = lean_uint8_to_uint32(v_b_u2080_346_);
v___x_351_ = 12;
v___x_352_ = lean_uint32_shift_left(v___x_350_, v___x_351_);
v___x_353_ = lean_uint8_to_uint32(v_b_u2081_348_);
v___x_354_ = 6;
v___x_355_ = lean_uint32_shift_left(v___x_353_, v___x_354_);
v___x_356_ = lean_uint32_lor(v___x_352_, v___x_355_);
v___x_357_ = lean_uint8_to_uint32(v_b_u2082_349_);
v_r_358_ = lean_uint32_lor(v___x_356_, v___x_357_);
v___x_359_ = 2048;
v___x_360_ = lean_uint32_dec_lt(v_r_358_, v___x_359_);
if (v___x_360_ == 0)
{
uint32_t v___x_361_; uint8_t v___x_362_; 
v___x_361_ = 55296;
v___x_362_ = lean_uint32_dec_le(v___x_361_, v_r_358_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_box_uint32(v_r_358_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
else
{
uint32_t v___x_365_; uint8_t v___x_366_; 
v___x_365_ = 57343;
v___x_366_ = lean_uint32_dec_le(v_r_358_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_box_uint32(v_r_358_);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; 
v___x_369_ = lean_box(0);
return v___x_369_;
}
}
}
else
{
lean_object* v___x_370_; 
v___x_370_ = lean_box(0);
return v___x_370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083___boxed(lean_object* v_w_371_, lean_object* v_x_372_, lean_object* v_y_373_){
_start:
{
uint8_t v_w_boxed_374_; uint8_t v_x_boxed_375_; uint8_t v_y_boxed_376_; lean_object* v_res_377_; 
v_w_boxed_374_ = lean_unbox(v_w_371_);
v_x_boxed_375_ = lean_unbox(v_x_372_);
v_y_boxed_376_ = lean_unbox(v_y_373_);
v_res_377_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(v_w_boxed_374_, v_x_boxed_375_, v_y_boxed_376_);
return v_res_377_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2083(uint8_t v_w_378_, uint8_t v_x_379_, uint8_t v_y_380_){
_start:
{
uint8_t v___x_381_; uint8_t v___x_382_; uint8_t v___x_383_; uint8_t v___x_384_; 
v___x_381_ = 192;
v___x_382_ = lean_uint8_land(v_x_379_, v___x_381_);
v___x_383_ = 128;
v___x_384_ = lean_uint8_dec_eq(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
return v___x_384_;
}
else
{
uint8_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = lean_uint8_land(v_y_380_, v___x_381_);
v___x_386_ = lean_uint8_dec_eq(v___x_385_, v___x_383_);
if (v___x_386_ == 0)
{
return v___x_386_;
}
else
{
uint8_t v___x_387_; uint8_t v___x_388_; uint8_t v_b_u2080_389_; uint8_t v___x_390_; uint8_t v_b_u2081_391_; uint8_t v_b_u2082_392_; uint32_t v___x_393_; uint32_t v___x_394_; uint32_t v___x_395_; uint32_t v___x_396_; uint32_t v___x_397_; uint32_t v___x_398_; uint32_t v___x_399_; uint32_t v___x_400_; uint32_t v_r_401_; uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_387_ = 0;
v___x_388_ = 15;
v_b_u2080_389_ = lean_uint8_land(v_w_378_, v___x_388_);
v___x_390_ = 63;
v_b_u2081_391_ = lean_uint8_land(v_x_379_, v___x_390_);
v_b_u2082_392_ = lean_uint8_land(v_y_380_, v___x_390_);
v___x_393_ = lean_uint8_to_uint32(v_b_u2080_389_);
v___x_394_ = 12;
v___x_395_ = lean_uint32_shift_left(v___x_393_, v___x_394_);
v___x_396_ = lean_uint8_to_uint32(v_b_u2081_391_);
v___x_397_ = 6;
v___x_398_ = lean_uint32_shift_left(v___x_396_, v___x_397_);
v___x_399_ = lean_uint32_lor(v___x_395_, v___x_398_);
v___x_400_ = lean_uint8_to_uint32(v_b_u2082_392_);
v_r_401_ = lean_uint32_lor(v___x_399_, v___x_400_);
v___x_402_ = 2048;
v___x_403_ = lean_uint32_dec_le(v___x_402_, v_r_401_);
if (v___x_403_ == 0)
{
return v___x_387_;
}
else
{
uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = 55296;
v___x_405_ = lean_uint32_dec_lt(v_r_401_, v___x_404_);
if (v___x_405_ == 0)
{
uint32_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = 57343;
v___x_407_ = lean_uint32_dec_lt(v___x_406_, v_r_401_);
if (v___x_407_ == 0)
{
return v___x_387_;
}
else
{
return v___x_386_;
}
}
else
{
return v___x_386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2083___boxed(lean_object* v_w_408_, lean_object* v_x_409_, lean_object* v_y_410_){
_start:
{
uint8_t v_w_boxed_411_; uint8_t v_x_boxed_412_; uint8_t v_y_boxed_413_; uint8_t v_res_414_; lean_object* v_r_415_; 
v_w_boxed_411_ = lean_unbox(v_w_408_);
v_x_boxed_412_ = lean_unbox(v_x_409_);
v_y_boxed_413_ = lean_unbox(v_y_410_);
v_res_414_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2083(v_w_boxed_411_, v_x_boxed_412_, v_y_boxed_413_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(uint8_t v_w_416_, uint8_t v_x_417_, uint8_t v_y_418_, uint8_t v_z_419_){
_start:
{
uint8_t v___x_420_; uint8_t v_b_u2080_421_; uint8_t v___x_422_; uint8_t v_b_u2081_423_; uint8_t v_b_u2082_424_; uint8_t v_b_u2083_425_; uint32_t v___x_426_; uint32_t v___x_427_; uint32_t v___x_428_; uint32_t v___x_429_; uint32_t v___x_430_; uint32_t v___x_431_; uint32_t v___x_432_; uint32_t v___x_433_; uint32_t v___x_434_; uint32_t v___x_435_; uint32_t v___x_436_; uint32_t v___x_437_; uint32_t v___x_438_; 
v___x_420_ = 7;
v_b_u2080_421_ = lean_uint8_land(v_w_416_, v___x_420_);
v___x_422_ = 63;
v_b_u2081_423_ = lean_uint8_land(v_x_417_, v___x_422_);
v_b_u2082_424_ = lean_uint8_land(v_y_418_, v___x_422_);
v_b_u2083_425_ = lean_uint8_land(v_z_419_, v___x_422_);
v___x_426_ = lean_uint8_to_uint32(v_b_u2080_421_);
v___x_427_ = 18;
v___x_428_ = lean_uint32_shift_left(v___x_426_, v___x_427_);
v___x_429_ = lean_uint8_to_uint32(v_b_u2081_423_);
v___x_430_ = 12;
v___x_431_ = lean_uint32_shift_left(v___x_429_, v___x_430_);
v___x_432_ = lean_uint32_lor(v___x_428_, v___x_431_);
v___x_433_ = lean_uint8_to_uint32(v_b_u2082_424_);
v___x_434_ = 6;
v___x_435_ = lean_uint32_shift_left(v___x_433_, v___x_434_);
v___x_436_ = lean_uint32_lor(v___x_432_, v___x_435_);
v___x_437_ = lean_uint8_to_uint32(v_b_u2083_425_);
v___x_438_ = lean_uint32_lor(v___x_436_, v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked___boxed(lean_object* v_w_439_, lean_object* v_x_440_, lean_object* v_y_441_, lean_object* v_z_442_){
_start:
{
uint8_t v_w_boxed_443_; uint8_t v_x_boxed_444_; uint8_t v_y_boxed_445_; uint8_t v_z_boxed_446_; uint32_t v_res_447_; lean_object* v_r_448_; 
v_w_boxed_443_ = lean_unbox(v_w_439_);
v_x_boxed_444_ = lean_unbox(v_x_440_);
v_y_boxed_445_ = lean_unbox(v_y_441_);
v_z_boxed_446_ = lean_unbox(v_z_442_);
v_res_447_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(v_w_boxed_443_, v_x_boxed_444_, v_y_boxed_445_, v_z_boxed_446_);
v_r_448_ = lean_box_uint32(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(uint8_t v_w_449_, uint8_t v_x_450_, uint8_t v_y_451_, uint8_t v_z_452_){
_start:
{
uint8_t v___x_453_; uint8_t v___x_454_; uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_453_ = 192;
v___x_454_ = lean_uint8_land(v_x_450_, v___x_453_);
v___x_455_ = 128;
v___x_456_ = lean_uint8_dec_eq(v___x_454_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
v___x_457_ = lean_box(0);
return v___x_457_;
}
else
{
uint8_t v___x_458_; uint8_t v___x_459_; 
v___x_458_ = lean_uint8_land(v_y_451_, v___x_453_);
v___x_459_ = lean_uint8_dec_eq(v___x_458_, v___x_455_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
v___x_460_ = lean_box(0);
return v___x_460_;
}
else
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_uint8_land(v_z_452_, v___x_453_);
v___x_462_ = lean_uint8_dec_eq(v___x_461_, v___x_455_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
v___x_463_ = lean_box(0);
return v___x_463_;
}
else
{
uint8_t v___x_464_; uint8_t v_b_u2080_465_; uint8_t v___x_466_; uint8_t v_b_u2081_467_; uint8_t v_b_u2082_468_; uint8_t v_b_u2083_469_; uint32_t v___x_470_; uint32_t v___x_471_; uint32_t v___x_472_; uint32_t v___x_473_; uint32_t v___x_474_; uint32_t v___x_475_; uint32_t v___x_476_; uint32_t v___x_477_; uint32_t v___x_478_; uint32_t v___x_479_; uint32_t v___x_480_; uint32_t v___x_481_; uint32_t v_r_482_; uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_464_ = 7;
v_b_u2080_465_ = lean_uint8_land(v_w_449_, v___x_464_);
v___x_466_ = 63;
v_b_u2081_467_ = lean_uint8_land(v_x_450_, v___x_466_);
v_b_u2082_468_ = lean_uint8_land(v_y_451_, v___x_466_);
v_b_u2083_469_ = lean_uint8_land(v_z_452_, v___x_466_);
v___x_470_ = lean_uint8_to_uint32(v_b_u2080_465_);
v___x_471_ = 18;
v___x_472_ = lean_uint32_shift_left(v___x_470_, v___x_471_);
v___x_473_ = lean_uint8_to_uint32(v_b_u2081_467_);
v___x_474_ = 12;
v___x_475_ = lean_uint32_shift_left(v___x_473_, v___x_474_);
v___x_476_ = lean_uint32_lor(v___x_472_, v___x_475_);
v___x_477_ = lean_uint8_to_uint32(v_b_u2082_468_);
v___x_478_ = 6;
v___x_479_ = lean_uint32_shift_left(v___x_477_, v___x_478_);
v___x_480_ = lean_uint32_lor(v___x_476_, v___x_479_);
v___x_481_ = lean_uint8_to_uint32(v_b_u2083_469_);
v_r_482_ = lean_uint32_lor(v___x_480_, v___x_481_);
v___x_483_ = 65536;
v___x_484_ = lean_uint32_dec_lt(v_r_482_, v___x_483_);
if (v___x_484_ == 0)
{
uint32_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = 1114111;
v___x_486_ = lean_uint32_dec_lt(v___x_485_, v_r_482_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_box_uint32(v_r_482_);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; 
v___x_489_ = lean_box(0);
return v___x_489_;
}
}
else
{
lean_object* v___x_490_; 
v___x_490_ = lean_box(0);
return v___x_490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084___boxed(lean_object* v_w_491_, lean_object* v_x_492_, lean_object* v_y_493_, lean_object* v_z_494_){
_start:
{
uint8_t v_w_boxed_495_; uint8_t v_x_boxed_496_; uint8_t v_y_boxed_497_; uint8_t v_z_boxed_498_; lean_object* v_res_499_; 
v_w_boxed_495_ = lean_unbox(v_w_491_);
v_x_boxed_496_ = lean_unbox(v_x_492_);
v_y_boxed_497_ = lean_unbox(v_y_493_);
v_z_boxed_498_ = lean_unbox(v_z_494_);
v_res_499_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(v_w_boxed_495_, v_x_boxed_496_, v_y_boxed_497_, v_z_boxed_498_);
return v_res_499_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2084(uint8_t v_w_500_, uint8_t v_x_501_, uint8_t v_y_502_, uint8_t v_z_503_){
_start:
{
uint8_t v___x_504_; uint8_t v___x_505_; uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_504_ = 192;
v___x_505_ = lean_uint8_land(v_x_501_, v___x_504_);
v___x_506_ = 128;
v___x_507_ = lean_uint8_dec_eq(v___x_505_, v___x_506_);
if (v___x_507_ == 0)
{
return v___x_507_;
}
else
{
uint8_t v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_uint8_land(v_y_502_, v___x_504_);
v___x_509_ = lean_uint8_dec_eq(v___x_508_, v___x_506_);
if (v___x_509_ == 0)
{
return v___x_509_;
}
else
{
uint8_t v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_uint8_land(v_z_503_, v___x_504_);
v___x_511_ = lean_uint8_dec_eq(v___x_510_, v___x_506_);
if (v___x_511_ == 0)
{
return v___x_511_;
}
else
{
uint8_t v___x_512_; uint8_t v___x_513_; uint8_t v_b_u2080_514_; uint8_t v___x_515_; uint8_t v_b_u2081_516_; uint8_t v_b_u2082_517_; uint8_t v_b_u2083_518_; uint32_t v___x_519_; uint32_t v___x_520_; uint32_t v___x_521_; uint32_t v___x_522_; uint32_t v___x_523_; uint32_t v___x_524_; uint32_t v___x_525_; uint32_t v___x_526_; uint32_t v___x_527_; uint32_t v___x_528_; uint32_t v___x_529_; uint32_t v___x_530_; uint32_t v_r_531_; uint32_t v___x_532_; uint8_t v___x_533_; 
v___x_512_ = 0;
v___x_513_ = 7;
v_b_u2080_514_ = lean_uint8_land(v_w_500_, v___x_513_);
v___x_515_ = 63;
v_b_u2081_516_ = lean_uint8_land(v_x_501_, v___x_515_);
v_b_u2082_517_ = lean_uint8_land(v_y_502_, v___x_515_);
v_b_u2083_518_ = lean_uint8_land(v_z_503_, v___x_515_);
v___x_519_ = lean_uint8_to_uint32(v_b_u2080_514_);
v___x_520_ = 18;
v___x_521_ = lean_uint32_shift_left(v___x_519_, v___x_520_);
v___x_522_ = lean_uint8_to_uint32(v_b_u2081_516_);
v___x_523_ = 12;
v___x_524_ = lean_uint32_shift_left(v___x_522_, v___x_523_);
v___x_525_ = lean_uint32_lor(v___x_521_, v___x_524_);
v___x_526_ = lean_uint8_to_uint32(v_b_u2082_517_);
v___x_527_ = 6;
v___x_528_ = lean_uint32_shift_left(v___x_526_, v___x_527_);
v___x_529_ = lean_uint32_lor(v___x_525_, v___x_528_);
v___x_530_ = lean_uint8_to_uint32(v_b_u2083_518_);
v_r_531_ = lean_uint32_lor(v___x_529_, v___x_530_);
v___x_532_ = 65536;
v___x_533_ = lean_uint32_dec_le(v___x_532_, v_r_531_);
if (v___x_533_ == 0)
{
return v___x_512_;
}
else
{
uint32_t v___x_534_; uint8_t v___x_535_; 
v___x_534_ = 1114111;
v___x_535_ = lean_uint32_dec_le(v_r_531_, v___x_534_);
if (v___x_535_ == 0)
{
return v___x_512_;
}
else
{
return v___x_511_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2084___boxed(lean_object* v_w_536_, lean_object* v_x_537_, lean_object* v_y_538_, lean_object* v_z_539_){
_start:
{
uint8_t v_w_boxed_540_; uint8_t v_x_boxed_541_; uint8_t v_y_boxed_542_; uint8_t v_z_boxed_543_; uint8_t v_res_544_; lean_object* v_r_545_; 
v_w_boxed_540_ = lean_unbox(v_w_536_);
v_x_boxed_541_ = lean_unbox(v_x_537_);
v_y_boxed_542_ = lean_unbox(v_y_538_);
v_z_boxed_543_ = lean_unbox(v_z_539_);
v_res_544_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2084(v_w_boxed_540_, v_x_boxed_541_, v_y_boxed_542_, v_z_boxed_543_);
v_r_545_ = lean_box(v_res_544_);
return v_r_545_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f(lean_object* v_bytes_546_, lean_object* v_i_547_){
_start:
{
lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_byte_array_size(v_bytes_546_);
v___x_549_ = lean_nat_dec_lt(v_i_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
v___x_550_ = lean_box(0);
return v___x_550_;
}
else
{
uint8_t v___x_551_; uint8_t v___x_552_; uint8_t v___x_553_; uint8_t v___x_554_; uint8_t v___x_555_; 
v___x_551_ = lean_byte_array_fget(v_bytes_546_, v_i_547_);
v___x_552_ = 128;
v___x_553_ = lean_uint8_land(v___x_551_, v___x_552_);
v___x_554_ = 0;
v___x_555_ = lean_uint8_dec_eq(v___x_553_, v___x_554_);
if (v___x_555_ == 0)
{
uint8_t v___x_556_; uint8_t v___x_557_; uint8_t v___x_558_; uint8_t v___x_559_; 
v___x_556_ = 224;
v___x_557_ = lean_uint8_land(v___x_551_, v___x_556_);
v___x_558_ = 192;
v___x_559_ = lean_uint8_dec_eq(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
uint8_t v___x_560_; uint8_t v___x_561_; uint8_t v___x_562_; 
v___x_560_ = 240;
v___x_561_ = lean_uint8_land(v___x_551_, v___x_560_);
v___x_562_ = lean_uint8_dec_eq(v___x_561_, v___x_556_);
if (v___x_562_ == 0)
{
uint8_t v___x_563_; uint8_t v___x_564_; uint8_t v___x_565_; 
v___x_563_ = 248;
v___x_564_ = lean_uint8_land(v___x_551_, v___x_563_);
v___x_565_ = lean_uint8_dec_eq(v___x_564_, v___x_560_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
v___x_566_ = lean_box(0);
return v___x_566_;
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_567_ = lean_unsigned_to_nat(3u);
v___x_568_ = lean_nat_add(v_i_547_, v___x_567_);
v___x_569_ = lean_nat_dec_lt(v___x_568_, v___x_548_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
lean_dec(v___x_568_);
v___x_570_ = lean_box(0);
return v___x_570_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; uint8_t v___x_574_; uint8_t v___x_575_; 
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = lean_nat_add(v_i_547_, v___x_571_);
v___x_573_ = lean_byte_array_fget(v_bytes_546_, v___x_572_);
lean_dec(v___x_572_);
v___x_574_ = lean_uint8_land(v___x_573_, v___x_558_);
v___x_575_ = lean_uint8_dec_eq(v___x_574_, v___x_552_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
lean_dec(v___x_568_);
v___x_576_ = lean_box(0);
return v___x_576_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; uint8_t v___x_580_; uint8_t v___x_581_; 
v___x_577_ = lean_unsigned_to_nat(2u);
v___x_578_ = lean_nat_add(v_i_547_, v___x_577_);
v___x_579_ = lean_byte_array_fget(v_bytes_546_, v___x_578_);
lean_dec(v___x_578_);
v___x_580_ = lean_uint8_land(v___x_579_, v___x_558_);
v___x_581_ = lean_uint8_dec_eq(v___x_580_, v___x_552_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec(v___x_568_);
v___x_582_ = lean_box(0);
return v___x_582_;
}
else
{
uint8_t v___x_583_; uint8_t v___x_584_; uint8_t v___x_585_; 
v___x_583_ = lean_byte_array_fget(v_bytes_546_, v___x_568_);
lean_dec(v___x_568_);
v___x_584_ = lean_uint8_land(v___x_583_, v___x_558_);
v___x_585_ = lean_uint8_dec_eq(v___x_584_, v___x_552_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_box(0);
return v___x_586_;
}
else
{
uint8_t v___x_587_; uint8_t v_b_u2080_588_; uint8_t v___x_589_; uint8_t v_b_u2081_590_; uint8_t v_b_u2082_591_; uint8_t v_b_u2083_592_; uint32_t v___x_593_; uint32_t v___x_594_; uint32_t v___x_595_; uint32_t v___x_596_; uint32_t v___x_597_; uint32_t v___x_598_; uint32_t v___x_599_; uint32_t v___x_600_; uint32_t v___x_601_; uint32_t v___x_602_; uint32_t v___x_603_; uint32_t v___x_604_; uint32_t v_r_605_; uint32_t v___x_606_; uint8_t v___x_607_; 
v___x_587_ = 7;
v_b_u2080_588_ = lean_uint8_land(v___x_551_, v___x_587_);
v___x_589_ = 63;
v_b_u2081_590_ = lean_uint8_land(v___x_573_, v___x_589_);
v_b_u2082_591_ = lean_uint8_land(v___x_579_, v___x_589_);
v_b_u2083_592_ = lean_uint8_land(v___x_583_, v___x_589_);
v___x_593_ = lean_uint8_to_uint32(v_b_u2080_588_);
v___x_594_ = 18;
v___x_595_ = lean_uint32_shift_left(v___x_593_, v___x_594_);
v___x_596_ = lean_uint8_to_uint32(v_b_u2081_590_);
v___x_597_ = 12;
v___x_598_ = lean_uint32_shift_left(v___x_596_, v___x_597_);
v___x_599_ = lean_uint32_lor(v___x_595_, v___x_598_);
v___x_600_ = lean_uint8_to_uint32(v_b_u2082_591_);
v___x_601_ = 6;
v___x_602_ = lean_uint32_shift_left(v___x_600_, v___x_601_);
v___x_603_ = lean_uint32_lor(v___x_599_, v___x_602_);
v___x_604_ = lean_uint8_to_uint32(v_b_u2083_592_);
v_r_605_ = lean_uint32_lor(v___x_603_, v___x_604_);
v___x_606_ = 65536;
v___x_607_ = lean_uint32_dec_lt(v_r_605_, v___x_606_);
if (v___x_607_ == 0)
{
uint32_t v___x_608_; uint8_t v___x_609_; 
v___x_608_ = 1114111;
v___x_609_ = lean_uint32_dec_lt(v___x_608_, v_r_605_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_box_uint32(v_r_605_);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
else
{
lean_object* v___x_612_; 
v___x_612_ = lean_box(0);
return v___x_612_;
}
}
else
{
lean_object* v___x_613_; 
v___x_613_ = lean_box(0);
return v___x_613_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_614_ = lean_unsigned_to_nat(2u);
v___x_615_ = lean_nat_add(v_i_547_, v___x_614_);
v___x_616_ = lean_nat_dec_lt(v___x_615_, v___x_548_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
lean_dec(v___x_615_);
v___x_617_ = lean_box(0);
return v___x_617_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; uint8_t v___x_621_; uint8_t v___x_622_; 
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_nat_add(v_i_547_, v___x_618_);
v___x_620_ = lean_byte_array_fget(v_bytes_546_, v___x_619_);
lean_dec(v___x_619_);
v___x_621_ = lean_uint8_land(v___x_620_, v___x_558_);
v___x_622_ = lean_uint8_dec_eq(v___x_621_, v___x_552_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_dec(v___x_615_);
v___x_623_ = lean_box(0);
return v___x_623_;
}
else
{
uint8_t v___x_624_; uint8_t v___x_625_; uint8_t v___x_626_; 
v___x_624_ = lean_byte_array_fget(v_bytes_546_, v___x_615_);
lean_dec(v___x_615_);
v___x_625_ = lean_uint8_land(v___x_624_, v___x_558_);
v___x_626_ = lean_uint8_dec_eq(v___x_625_, v___x_552_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
v___x_627_ = lean_box(0);
return v___x_627_;
}
else
{
uint8_t v___x_628_; uint8_t v_b_u2080_629_; uint8_t v___x_630_; uint8_t v_b_u2081_631_; uint8_t v_b_u2082_632_; uint32_t v___x_633_; uint32_t v___x_634_; uint32_t v___x_635_; uint32_t v___x_636_; uint32_t v___x_637_; uint32_t v___x_638_; uint32_t v___x_639_; uint32_t v___x_640_; uint32_t v_r_641_; uint32_t v___x_642_; uint8_t v___x_643_; 
v___x_628_ = 15;
v_b_u2080_629_ = lean_uint8_land(v___x_551_, v___x_628_);
v___x_630_ = 63;
v_b_u2081_631_ = lean_uint8_land(v___x_620_, v___x_630_);
v_b_u2082_632_ = lean_uint8_land(v___x_624_, v___x_630_);
v___x_633_ = lean_uint8_to_uint32(v_b_u2080_629_);
v___x_634_ = 12;
v___x_635_ = lean_uint32_shift_left(v___x_633_, v___x_634_);
v___x_636_ = lean_uint8_to_uint32(v_b_u2081_631_);
v___x_637_ = 6;
v___x_638_ = lean_uint32_shift_left(v___x_636_, v___x_637_);
v___x_639_ = lean_uint32_lor(v___x_635_, v___x_638_);
v___x_640_ = lean_uint8_to_uint32(v_b_u2082_632_);
v_r_641_ = lean_uint32_lor(v___x_639_, v___x_640_);
v___x_642_ = 2048;
v___x_643_ = lean_uint32_dec_lt(v_r_641_, v___x_642_);
if (v___x_643_ == 0)
{
uint32_t v___x_644_; uint8_t v___x_645_; 
v___x_644_ = 55296;
v___x_645_ = lean_uint32_dec_le(v___x_644_, v_r_641_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_box_uint32(v_r_641_);
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
else
{
uint32_t v___x_648_; uint8_t v___x_649_; 
v___x_648_ = 57343;
v___x_649_ = lean_uint32_dec_le(v_r_641_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_box_uint32(v_r_641_);
v___x_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
else
{
lean_object* v___x_652_; 
v___x_652_ = lean_box(0);
return v___x_652_;
}
}
}
else
{
lean_object* v___x_653_; 
v___x_653_ = lean_box(0);
return v___x_653_;
}
}
}
}
}
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_654_ = lean_unsigned_to_nat(1u);
v___x_655_ = lean_nat_add(v_i_547_, v___x_654_);
v___x_656_ = lean_nat_dec_lt(v___x_655_, v___x_548_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
lean_dec(v___x_655_);
v___x_657_ = lean_box(0);
return v___x_657_;
}
else
{
uint8_t v___x_658_; uint8_t v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_byte_array_fget(v_bytes_546_, v___x_655_);
lean_dec(v___x_655_);
v___x_659_ = lean_uint8_land(v___x_658_, v___x_558_);
v___x_660_ = lean_uint8_dec_eq(v___x_659_, v___x_552_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
v___x_661_ = lean_box(0);
return v___x_661_;
}
else
{
uint8_t v___x_662_; uint8_t v_b_u2080_663_; uint8_t v___x_664_; uint8_t v_b_u2081_665_; uint32_t v___x_666_; uint32_t v___x_667_; uint32_t v___x_668_; uint32_t v___x_669_; uint32_t v_r_670_; uint32_t v___x_671_; uint8_t v___x_672_; 
v___x_662_ = 31;
v_b_u2080_663_ = lean_uint8_land(v___x_551_, v___x_662_);
v___x_664_ = 63;
v_b_u2081_665_ = lean_uint8_land(v___x_658_, v___x_664_);
v___x_666_ = lean_uint8_to_uint32(v_b_u2080_663_);
v___x_667_ = 6;
v___x_668_ = lean_uint32_shift_left(v___x_666_, v___x_667_);
v___x_669_ = lean_uint8_to_uint32(v_b_u2081_665_);
v_r_670_ = lean_uint32_lor(v___x_668_, v___x_669_);
v___x_671_ = 128;
v___x_672_ = lean_uint32_dec_lt(v_r_670_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_box_uint32(v_r_670_);
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
else
{
lean_object* v___x_675_; 
v___x_675_ = lean_box(0);
return v___x_675_;
}
}
}
}
}
else
{
uint32_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = lean_uint8_to_uint32(v___x_551_);
v___x_677_ = lean_box_uint32(v___x_676_);
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f___boxed(lean_object* v_bytes_679_, lean_object* v_i_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_ByteArray_utf8DecodeChar_x3f(v_bytes_679_, v_i_680_);
lean_dec(v_i_680_);
lean_dec_ref(v_bytes_679_);
return v_res_681_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8At(lean_object* v_bytes_682_, lean_object* v_i_683_){
_start:
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_byte_array_size(v_bytes_682_);
v___x_685_ = lean_nat_dec_lt(v_i_683_, v___x_684_);
if (v___x_685_ == 0)
{
return v___x_685_;
}
else
{
uint8_t v___x_686_; uint8_t v___x_687_; uint8_t v___x_688_; uint8_t v___x_689_; uint8_t v___x_690_; 
v___x_686_ = lean_byte_array_fget(v_bytes_682_, v_i_683_);
v___x_687_ = 128;
v___x_688_ = lean_uint8_land(v___x_686_, v___x_687_);
v___x_689_ = 0;
v___x_690_ = lean_uint8_dec_eq(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
uint8_t v___x_691_; uint8_t v___x_692_; uint8_t v___x_693_; uint8_t v___x_694_; 
v___x_691_ = 224;
v___x_692_ = lean_uint8_land(v___x_686_, v___x_691_);
v___x_693_ = 192;
v___x_694_ = lean_uint8_dec_eq(v___x_692_, v___x_693_);
if (v___x_694_ == 0)
{
uint8_t v___x_695_; uint8_t v___x_696_; uint8_t v___x_697_; 
v___x_695_ = 240;
v___x_696_ = lean_uint8_land(v___x_686_, v___x_695_);
v___x_697_ = lean_uint8_dec_eq(v___x_696_, v___x_691_);
if (v___x_697_ == 0)
{
uint8_t v___x_698_; uint8_t v___x_699_; uint8_t v___x_700_; 
v___x_698_ = 248;
v___x_699_ = lean_uint8_land(v___x_686_, v___x_698_);
v___x_700_ = lean_uint8_dec_eq(v___x_699_, v___x_695_);
if (v___x_700_ == 0)
{
return v___x_700_;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_701_ = lean_unsigned_to_nat(3u);
v___x_702_ = lean_nat_add(v_i_683_, v___x_701_);
v___x_703_ = lean_nat_dec_lt(v___x_702_, v___x_684_);
if (v___x_703_ == 0)
{
lean_dec(v___x_702_);
return v___x_697_;
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; uint8_t v___x_707_; uint8_t v___x_708_; 
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_add(v_i_683_, v___x_704_);
v___x_706_ = lean_byte_array_fget(v_bytes_682_, v___x_705_);
lean_dec(v___x_705_);
v___x_707_ = lean_uint8_land(v___x_706_, v___x_693_);
v___x_708_ = lean_uint8_dec_eq(v___x_707_, v___x_687_);
if (v___x_708_ == 0)
{
lean_dec(v___x_702_);
return v___x_708_;
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; uint8_t v___x_712_; uint8_t v___x_713_; 
v___x_709_ = lean_unsigned_to_nat(2u);
v___x_710_ = lean_nat_add(v_i_683_, v___x_709_);
v___x_711_ = lean_byte_array_fget(v_bytes_682_, v___x_710_);
lean_dec(v___x_710_);
v___x_712_ = lean_uint8_land(v___x_711_, v___x_693_);
v___x_713_ = lean_uint8_dec_eq(v___x_712_, v___x_687_);
if (v___x_713_ == 0)
{
lean_dec(v___x_702_);
return v___x_713_;
}
else
{
uint8_t v___x_714_; uint8_t v___x_715_; uint8_t v___x_716_; 
v___x_714_ = lean_byte_array_fget(v_bytes_682_, v___x_702_);
lean_dec(v___x_702_);
v___x_715_ = lean_uint8_land(v___x_714_, v___x_693_);
v___x_716_ = lean_uint8_dec_eq(v___x_715_, v___x_687_);
if (v___x_716_ == 0)
{
return v___x_716_;
}
else
{
uint8_t v___x_717_; uint8_t v_b_u2080_718_; uint8_t v___x_719_; uint8_t v_b_u2081_720_; uint8_t v_b_u2082_721_; uint8_t v_b_u2083_722_; uint32_t v___x_723_; uint32_t v___x_724_; uint32_t v___x_725_; uint32_t v___x_726_; uint32_t v___x_727_; uint32_t v___x_728_; uint32_t v___x_729_; uint32_t v___x_730_; uint32_t v___x_731_; uint32_t v___x_732_; uint32_t v___x_733_; uint32_t v___x_734_; uint32_t v_r_735_; uint32_t v___x_736_; uint8_t v___x_737_; 
v___x_717_ = 7;
v_b_u2080_718_ = lean_uint8_land(v___x_686_, v___x_717_);
v___x_719_ = 63;
v_b_u2081_720_ = lean_uint8_land(v___x_706_, v___x_719_);
v_b_u2082_721_ = lean_uint8_land(v___x_711_, v___x_719_);
v_b_u2083_722_ = lean_uint8_land(v___x_714_, v___x_719_);
v___x_723_ = lean_uint8_to_uint32(v_b_u2080_718_);
v___x_724_ = 18;
v___x_725_ = lean_uint32_shift_left(v___x_723_, v___x_724_);
v___x_726_ = lean_uint8_to_uint32(v_b_u2081_720_);
v___x_727_ = 12;
v___x_728_ = lean_uint32_shift_left(v___x_726_, v___x_727_);
v___x_729_ = lean_uint32_lor(v___x_725_, v___x_728_);
v___x_730_ = lean_uint8_to_uint32(v_b_u2082_721_);
v___x_731_ = 6;
v___x_732_ = lean_uint32_shift_left(v___x_730_, v___x_731_);
v___x_733_ = lean_uint32_lor(v___x_729_, v___x_732_);
v___x_734_ = lean_uint8_to_uint32(v_b_u2083_722_);
v_r_735_ = lean_uint32_lor(v___x_733_, v___x_734_);
v___x_736_ = 65536;
v___x_737_ = lean_uint32_dec_le(v___x_736_, v_r_735_);
if (v___x_737_ == 0)
{
return v___x_697_;
}
else
{
uint32_t v___x_738_; uint8_t v___x_739_; 
v___x_738_ = 1114111;
v___x_739_ = lean_uint32_dec_le(v_r_735_, v___x_738_);
if (v___x_739_ == 0)
{
return v___x_697_;
}
else
{
return v___x_716_;
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
lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_740_ = lean_unsigned_to_nat(2u);
v___x_741_ = lean_nat_add(v_i_683_, v___x_740_);
v___x_742_ = lean_nat_dec_lt(v___x_741_, v___x_684_);
if (v___x_742_ == 0)
{
lean_dec(v___x_741_);
return v___x_694_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; uint8_t v___x_746_; uint8_t v___x_747_; 
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = lean_nat_add(v_i_683_, v___x_743_);
v___x_745_ = lean_byte_array_fget(v_bytes_682_, v___x_744_);
lean_dec(v___x_744_);
v___x_746_ = lean_uint8_land(v___x_745_, v___x_693_);
v___x_747_ = lean_uint8_dec_eq(v___x_746_, v___x_687_);
if (v___x_747_ == 0)
{
lean_dec(v___x_741_);
return v___x_747_;
}
else
{
uint8_t v___x_748_; uint8_t v___x_749_; uint8_t v___x_750_; 
v___x_748_ = lean_byte_array_fget(v_bytes_682_, v___x_741_);
lean_dec(v___x_741_);
v___x_749_ = lean_uint8_land(v___x_748_, v___x_693_);
v___x_750_ = lean_uint8_dec_eq(v___x_749_, v___x_687_);
if (v___x_750_ == 0)
{
return v___x_750_;
}
else
{
uint8_t v___x_751_; uint8_t v_b_u2080_752_; uint8_t v___x_753_; uint8_t v_b_u2081_754_; uint8_t v_b_u2082_755_; uint32_t v___x_756_; uint32_t v___x_757_; uint32_t v___x_758_; uint32_t v___x_759_; uint32_t v___x_760_; uint32_t v___x_761_; uint32_t v___x_762_; uint32_t v___x_763_; uint32_t v_r_764_; uint32_t v___x_765_; uint8_t v___x_766_; 
v___x_751_ = 15;
v_b_u2080_752_ = lean_uint8_land(v___x_686_, v___x_751_);
v___x_753_ = 63;
v_b_u2081_754_ = lean_uint8_land(v___x_745_, v___x_753_);
v_b_u2082_755_ = lean_uint8_land(v___x_748_, v___x_753_);
v___x_756_ = lean_uint8_to_uint32(v_b_u2080_752_);
v___x_757_ = 12;
v___x_758_ = lean_uint32_shift_left(v___x_756_, v___x_757_);
v___x_759_ = lean_uint8_to_uint32(v_b_u2081_754_);
v___x_760_ = 6;
v___x_761_ = lean_uint32_shift_left(v___x_759_, v___x_760_);
v___x_762_ = lean_uint32_lor(v___x_758_, v___x_761_);
v___x_763_ = lean_uint8_to_uint32(v_b_u2082_755_);
v_r_764_ = lean_uint32_lor(v___x_762_, v___x_763_);
v___x_765_ = 2048;
v___x_766_ = lean_uint32_dec_le(v___x_765_, v_r_764_);
if (v___x_766_ == 0)
{
return v___x_694_;
}
else
{
uint32_t v___x_767_; uint8_t v___x_768_; 
v___x_767_ = 55296;
v___x_768_ = lean_uint32_dec_lt(v_r_764_, v___x_767_);
if (v___x_768_ == 0)
{
uint32_t v___x_769_; uint8_t v___x_770_; 
v___x_769_ = 57343;
v___x_770_ = lean_uint32_dec_lt(v___x_769_, v_r_764_);
if (v___x_770_ == 0)
{
return v___x_694_;
}
else
{
return v___x_750_;
}
}
else
{
return v___x_750_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_nat_add(v_i_683_, v___x_771_);
v___x_773_ = lean_nat_dec_lt(v___x_772_, v___x_684_);
if (v___x_773_ == 0)
{
lean_dec(v___x_772_);
return v___x_690_;
}
else
{
uint8_t v___x_774_; uint8_t v___x_775_; uint8_t v___x_776_; 
v___x_774_ = lean_byte_array_fget(v_bytes_682_, v___x_772_);
lean_dec(v___x_772_);
v___x_775_ = lean_uint8_land(v___x_774_, v___x_693_);
v___x_776_ = lean_uint8_dec_eq(v___x_775_, v___x_687_);
if (v___x_776_ == 0)
{
return v___x_776_;
}
else
{
uint8_t v___x_777_; uint8_t v_b_u2080_778_; uint8_t v___x_779_; uint8_t v_b_u2081_780_; uint32_t v___x_781_; uint32_t v___x_782_; uint32_t v___x_783_; uint32_t v___x_784_; uint32_t v_r_785_; uint32_t v___x_786_; uint8_t v___x_787_; 
v___x_777_ = 31;
v_b_u2080_778_ = lean_uint8_land(v___x_686_, v___x_777_);
v___x_779_ = 63;
v_b_u2081_780_ = lean_uint8_land(v___x_774_, v___x_779_);
v___x_781_ = lean_uint8_to_uint32(v_b_u2080_778_);
v___x_782_ = 6;
v___x_783_ = lean_uint32_shift_left(v___x_781_, v___x_782_);
v___x_784_ = lean_uint8_to_uint32(v_b_u2081_780_);
v_r_785_ = lean_uint32_lor(v___x_783_, v___x_784_);
v___x_786_ = 128;
v___x_787_ = lean_uint32_dec_le(v___x_786_, v_r_785_);
return v___x_787_;
}
}
}
}
else
{
return v___x_690_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8At___boxed(lean_object* v_bytes_788_, lean_object* v_i_789_){
_start:
{
uint8_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l_ByteArray_validateUTF8At(v_bytes_788_, v_i_789_);
lean_dec(v_i_789_);
lean_dec_ref(v_bytes_788_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t v_x_792_, lean_object* v_h__1_793_, lean_object* v_h__2_794_, lean_object* v_h__3_795_, lean_object* v_h__4_796_, lean_object* v_h__5_797_){
_start:
{
switch(v_x_792_)
{
case 0:
{
lean_object* v___x_798_; 
lean_dec(v_h__5_797_);
lean_dec(v_h__4_796_);
lean_dec(v_h__3_795_);
lean_dec(v_h__2_794_);
v___x_798_ = lean_apply_1(v_h__1_793_, lean_box(0));
return v___x_798_;
}
case 1:
{
lean_object* v___x_799_; 
lean_dec(v_h__5_797_);
lean_dec(v_h__4_796_);
lean_dec(v_h__3_795_);
lean_dec(v_h__1_793_);
v___x_799_ = lean_apply_1(v_h__2_794_, lean_box(0));
return v___x_799_;
}
case 2:
{
lean_object* v___x_800_; 
lean_dec(v_h__5_797_);
lean_dec(v_h__4_796_);
lean_dec(v_h__2_794_);
lean_dec(v_h__1_793_);
v___x_800_ = lean_apply_1(v_h__3_795_, lean_box(0));
return v___x_800_;
}
case 3:
{
lean_object* v___x_801_; 
lean_dec(v_h__5_797_);
lean_dec(v_h__3_795_);
lean_dec(v_h__2_794_);
lean_dec(v_h__1_793_);
v___x_801_ = lean_apply_1(v_h__4_796_, lean_box(0));
return v___x_801_;
}
default: 
{
lean_object* v___x_802_; 
lean_dec(v_h__4_796_);
lean_dec(v_h__3_795_);
lean_dec(v_h__2_794_);
lean_dec(v_h__1_793_);
v___x_802_ = lean_apply_1(v_h__5_797_, lean_box(0));
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_803_, lean_object* v_h__1_804_, lean_object* v_h__2_805_, lean_object* v_h__3_806_, lean_object* v_h__4_807_, lean_object* v_h__5_808_){
_start:
{
uint8_t v_x_47__boxed_809_; lean_object* v_res_810_; 
v_x_47__boxed_809_ = lean_unbox(v_x_803_);
v_res_810_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(v_x_47__boxed_809_, v_h__1_804_, v_h__2_805_, v_h__3_806_, v_h__4_807_, v_h__5_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object* v_motive_811_, uint8_t v_x_812_, lean_object* v_h__1_813_, lean_object* v_h__2_814_, lean_object* v_h__3_815_, lean_object* v_h__4_816_, lean_object* v_h__5_817_){
_start:
{
switch(v_x_812_)
{
case 0:
{
lean_object* v___x_818_; 
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
v___x_818_ = lean_apply_1(v_h__1_813_, lean_box(0));
return v___x_818_;
}
case 1:
{
lean_object* v___x_819_; 
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__1_813_);
v___x_819_ = lean_apply_1(v_h__2_814_, lean_box(0));
return v___x_819_;
}
case 2:
{
lean_object* v___x_820_; 
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v___x_820_ = lean_apply_1(v_h__3_815_, lean_box(0));
return v___x_820_;
}
case 3:
{
lean_object* v___x_821_; 
lean_dec(v_h__5_817_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v___x_821_ = lean_apply_1(v_h__4_816_, lean_box(0));
return v___x_821_;
}
default: 
{
lean_object* v___x_822_; 
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v___x_822_ = lean_apply_1(v_h__5_817_, lean_box(0));
return v___x_822_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object* v_motive_823_, lean_object* v_x_824_, lean_object* v_h__1_825_, lean_object* v_h__2_826_, lean_object* v_h__3_827_, lean_object* v_h__4_828_, lean_object* v_h__5_829_){
_start:
{
uint8_t v_x_60__boxed_830_; lean_object* v_res_831_; 
v_x_60__boxed_830_ = lean_unbox(v_x_824_);
v_res_831_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(v_motive_823_, v_x_60__boxed_830_, v_h__1_825_, v_h__2_826_, v_h__3_827_, v_h__4_828_, v_h__5_829_);
return v_res_831_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar___redArg(lean_object* v_bytes_832_, lean_object* v_i_833_){
_start:
{
lean_object* v___x_834_; uint8_t v___x_835_; uint8_t v___x_836_; uint8_t v___x_837_; uint8_t v___x_838_; uint8_t v___x_839_; uint8_t v___x_840_; 
v___x_834_ = lean_byte_array_size(v_bytes_832_);
v___x_835_ = lean_nat_dec_lt(v_i_833_, v___x_834_);
v___x_836_ = lean_byte_array_fget(v_bytes_832_, v_i_833_);
v___x_837_ = 128;
v___x_838_ = lean_uint8_land(v___x_836_, v___x_837_);
v___x_839_ = 0;
v___x_840_ = lean_uint8_dec_eq(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
uint8_t v___x_841_; uint8_t v___x_842_; uint8_t v___x_843_; uint8_t v___x_844_; 
v___x_841_ = 224;
v___x_842_ = lean_uint8_land(v___x_836_, v___x_841_);
v___x_843_ = 192;
v___x_844_ = lean_uint8_dec_eq(v___x_842_, v___x_843_);
if (v___x_844_ == 0)
{
uint8_t v___x_845_; uint8_t v___x_846_; uint8_t v___x_847_; 
v___x_845_ = 240;
v___x_846_ = lean_uint8_land(v___x_836_, v___x_845_);
v___x_847_ = lean_uint8_dec_eq(v___x_846_, v___x_841_);
if (v___x_847_ == 0)
{
uint8_t v___x_848_; uint8_t v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; uint8_t v___x_857_; uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; uint8_t v___x_862_; uint8_t v___x_863_; uint8_t v___x_864_; uint8_t v___x_865_; uint8_t v___x_866_; uint8_t v___x_867_; uint8_t v_b_u2080_868_; uint8_t v___x_869_; uint8_t v_b_u2081_870_; uint8_t v_b_u2082_871_; uint8_t v_b_u2083_872_; uint32_t v___x_873_; uint32_t v___x_874_; uint32_t v___x_875_; uint32_t v___x_876_; uint32_t v___x_877_; uint32_t v___x_878_; uint32_t v___x_879_; uint32_t v___x_880_; uint32_t v___x_881_; uint32_t v___x_882_; uint32_t v___x_883_; uint32_t v___x_884_; uint32_t v_r_885_; uint32_t v___x_886_; uint8_t v___x_887_; uint32_t v___x_888_; uint8_t v___x_889_; 
v___x_848_ = 248;
v___x_849_ = lean_uint8_land(v___x_836_, v___x_848_);
v___x_850_ = lean_uint8_dec_eq(v___x_849_, v___x_845_);
v___x_851_ = lean_unsigned_to_nat(3u);
v___x_852_ = lean_nat_add(v_i_833_, v___x_851_);
v___x_853_ = lean_nat_dec_lt(v___x_852_, v___x_834_);
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = lean_nat_add(v_i_833_, v___x_854_);
v___x_856_ = lean_byte_array_fget(v_bytes_832_, v___x_855_);
lean_dec(v___x_855_);
v___x_857_ = lean_uint8_land(v___x_856_, v___x_843_);
v___x_858_ = lean_uint8_dec_eq(v___x_857_, v___x_837_);
v___x_859_ = lean_unsigned_to_nat(2u);
v___x_860_ = lean_nat_add(v_i_833_, v___x_859_);
v___x_861_ = lean_byte_array_fget(v_bytes_832_, v___x_860_);
lean_dec(v___x_860_);
v___x_862_ = lean_uint8_land(v___x_861_, v___x_843_);
v___x_863_ = lean_uint8_dec_eq(v___x_862_, v___x_837_);
v___x_864_ = lean_byte_array_fget(v_bytes_832_, v___x_852_);
lean_dec(v___x_852_);
v___x_865_ = lean_uint8_land(v___x_864_, v___x_843_);
v___x_866_ = lean_uint8_dec_eq(v___x_865_, v___x_837_);
v___x_867_ = 7;
v_b_u2080_868_ = lean_uint8_land(v___x_836_, v___x_867_);
v___x_869_ = 63;
v_b_u2081_870_ = lean_uint8_land(v___x_856_, v___x_869_);
v_b_u2082_871_ = lean_uint8_land(v___x_861_, v___x_869_);
v_b_u2083_872_ = lean_uint8_land(v___x_864_, v___x_869_);
v___x_873_ = lean_uint8_to_uint32(v_b_u2080_868_);
v___x_874_ = 18;
v___x_875_ = lean_uint32_shift_left(v___x_873_, v___x_874_);
v___x_876_ = lean_uint8_to_uint32(v_b_u2081_870_);
v___x_877_ = 12;
v___x_878_ = lean_uint32_shift_left(v___x_876_, v___x_877_);
v___x_879_ = lean_uint32_lor(v___x_875_, v___x_878_);
v___x_880_ = lean_uint8_to_uint32(v_b_u2082_871_);
v___x_881_ = 6;
v___x_882_ = lean_uint32_shift_left(v___x_880_, v___x_881_);
v___x_883_ = lean_uint32_lor(v___x_879_, v___x_882_);
v___x_884_ = lean_uint8_to_uint32(v_b_u2083_872_);
v_r_885_ = lean_uint32_lor(v___x_883_, v___x_884_);
v___x_886_ = 65536;
v___x_887_ = lean_uint32_dec_lt(v_r_885_, v___x_886_);
v___x_888_ = 1114111;
v___x_889_ = lean_uint32_dec_lt(v___x_888_, v_r_885_);
return v_r_885_;
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; uint8_t v___x_896_; uint8_t v___x_897_; uint8_t v___x_898_; uint8_t v___x_899_; uint8_t v___x_900_; uint8_t v___x_901_; uint8_t v_b_u2080_902_; uint8_t v___x_903_; uint8_t v_b_u2081_904_; uint8_t v_b_u2082_905_; uint32_t v___x_906_; uint32_t v___x_907_; uint32_t v___x_908_; uint32_t v___x_909_; uint32_t v___x_910_; uint32_t v___x_911_; uint32_t v___x_912_; uint32_t v___x_913_; uint32_t v_r_914_; uint32_t v___x_915_; uint8_t v___x_916_; uint32_t v___x_917_; uint8_t v___x_918_; 
v___x_890_ = lean_unsigned_to_nat(2u);
v___x_891_ = lean_nat_add(v_i_833_, v___x_890_);
v___x_892_ = lean_nat_dec_lt(v___x_891_, v___x_834_);
v___x_893_ = lean_unsigned_to_nat(1u);
v___x_894_ = lean_nat_add(v_i_833_, v___x_893_);
v___x_895_ = lean_byte_array_fget(v_bytes_832_, v___x_894_);
lean_dec(v___x_894_);
v___x_896_ = lean_uint8_land(v___x_895_, v___x_843_);
v___x_897_ = lean_uint8_dec_eq(v___x_896_, v___x_837_);
v___x_898_ = lean_byte_array_fget(v_bytes_832_, v___x_891_);
lean_dec(v___x_891_);
v___x_899_ = lean_uint8_land(v___x_898_, v___x_843_);
v___x_900_ = lean_uint8_dec_eq(v___x_899_, v___x_837_);
v___x_901_ = 15;
v_b_u2080_902_ = lean_uint8_land(v___x_836_, v___x_901_);
v___x_903_ = 63;
v_b_u2081_904_ = lean_uint8_land(v___x_895_, v___x_903_);
v_b_u2082_905_ = lean_uint8_land(v___x_898_, v___x_903_);
v___x_906_ = lean_uint8_to_uint32(v_b_u2080_902_);
v___x_907_ = 12;
v___x_908_ = lean_uint32_shift_left(v___x_906_, v___x_907_);
v___x_909_ = lean_uint8_to_uint32(v_b_u2081_904_);
v___x_910_ = 6;
v___x_911_ = lean_uint32_shift_left(v___x_909_, v___x_910_);
v___x_912_ = lean_uint32_lor(v___x_908_, v___x_911_);
v___x_913_ = lean_uint8_to_uint32(v_b_u2082_905_);
v_r_914_ = lean_uint32_lor(v___x_912_, v___x_913_);
v___x_915_ = 2048;
v___x_916_ = lean_uint32_dec_lt(v_r_914_, v___x_915_);
v___x_917_ = 55296;
v___x_918_ = lean_uint32_dec_le(v___x_917_, v_r_914_);
if (v___x_918_ == 0)
{
return v_r_914_;
}
else
{
uint32_t v___x_919_; uint8_t v___x_920_; 
v___x_919_ = 57343;
v___x_920_ = lean_uint32_dec_le(v_r_914_, v___x_919_);
return v_r_914_;
}
}
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; uint8_t v___x_924_; uint8_t v___x_925_; uint8_t v___x_926_; uint8_t v___x_927_; uint8_t v_b_u2080_928_; uint8_t v___x_929_; uint8_t v_b_u2081_930_; uint32_t v___x_931_; uint32_t v___x_932_; uint32_t v___x_933_; uint32_t v___x_934_; uint32_t v_r_935_; uint32_t v___x_936_; uint8_t v___x_937_; 
v___x_921_ = lean_unsigned_to_nat(1u);
v___x_922_ = lean_nat_add(v_i_833_, v___x_921_);
v___x_923_ = lean_nat_dec_lt(v___x_922_, v___x_834_);
v___x_924_ = lean_byte_array_fget(v_bytes_832_, v___x_922_);
lean_dec(v___x_922_);
v___x_925_ = lean_uint8_land(v___x_924_, v___x_843_);
v___x_926_ = lean_uint8_dec_eq(v___x_925_, v___x_837_);
v___x_927_ = 31;
v_b_u2080_928_ = lean_uint8_land(v___x_836_, v___x_927_);
v___x_929_ = 63;
v_b_u2081_930_ = lean_uint8_land(v___x_924_, v___x_929_);
v___x_931_ = lean_uint8_to_uint32(v_b_u2080_928_);
v___x_932_ = 6;
v___x_933_ = lean_uint32_shift_left(v___x_931_, v___x_932_);
v___x_934_ = lean_uint8_to_uint32(v_b_u2081_930_);
v_r_935_ = lean_uint32_lor(v___x_933_, v___x_934_);
v___x_936_ = 128;
v___x_937_ = lean_uint32_dec_lt(v_r_935_, v___x_936_);
return v_r_935_;
}
}
else
{
uint32_t v___x_938_; 
v___x_938_ = lean_uint8_to_uint32(v___x_836_);
return v___x_938_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___redArg___boxed(lean_object* v_bytes_939_, lean_object* v_i_940_){
_start:
{
uint32_t v_res_941_; lean_object* v_r_942_; 
v_res_941_ = l_ByteArray_utf8DecodeChar___redArg(v_bytes_939_, v_i_940_);
lean_dec(v_i_940_);
lean_dec_ref(v_bytes_939_);
v_r_942_ = lean_box_uint32(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar(lean_object* v_bytes_943_, lean_object* v_i_944_, lean_object* v_h_945_){
_start:
{
lean_object* v___x_946_; uint8_t v___x_947_; uint8_t v___x_948_; uint8_t v___x_949_; uint8_t v___x_950_; uint8_t v___x_951_; uint8_t v___x_952_; 
v___x_946_ = lean_byte_array_size(v_bytes_943_);
v___x_947_ = lean_nat_dec_lt(v_i_944_, v___x_946_);
v___x_948_ = lean_byte_array_fget(v_bytes_943_, v_i_944_);
v___x_949_ = 128;
v___x_950_ = lean_uint8_land(v___x_948_, v___x_949_);
v___x_951_ = 0;
v___x_952_ = lean_uint8_dec_eq(v___x_950_, v___x_951_);
if (v___x_952_ == 0)
{
uint8_t v___x_953_; uint8_t v___x_954_; uint8_t v___x_955_; uint8_t v___x_956_; 
v___x_953_ = 224;
v___x_954_ = lean_uint8_land(v___x_948_, v___x_953_);
v___x_955_ = 192;
v___x_956_ = lean_uint8_dec_eq(v___x_954_, v___x_955_);
if (v___x_956_ == 0)
{
uint8_t v___x_957_; uint8_t v___x_958_; uint8_t v___x_959_; 
v___x_957_ = 240;
v___x_958_ = lean_uint8_land(v___x_948_, v___x_957_);
v___x_959_ = lean_uint8_dec_eq(v___x_958_, v___x_953_);
if (v___x_959_ == 0)
{
uint8_t v___x_960_; uint8_t v___x_961_; uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; uint8_t v___x_969_; uint8_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; uint8_t v___x_974_; uint8_t v___x_975_; uint8_t v___x_976_; uint8_t v___x_977_; uint8_t v___x_978_; uint8_t v___x_979_; uint8_t v_b_u2080_980_; uint8_t v___x_981_; uint8_t v_b_u2081_982_; uint8_t v_b_u2082_983_; uint8_t v_b_u2083_984_; uint32_t v___x_985_; uint32_t v___x_986_; uint32_t v___x_987_; uint32_t v___x_988_; uint32_t v___x_989_; uint32_t v___x_990_; uint32_t v___x_991_; uint32_t v___x_992_; uint32_t v___x_993_; uint32_t v___x_994_; uint32_t v___x_995_; uint32_t v___x_996_; uint32_t v_r_997_; uint32_t v___x_998_; uint8_t v___x_999_; uint32_t v___x_1000_; uint8_t v___x_1001_; 
v___x_960_ = 248;
v___x_961_ = lean_uint8_land(v___x_948_, v___x_960_);
v___x_962_ = lean_uint8_dec_eq(v___x_961_, v___x_957_);
v___x_963_ = lean_unsigned_to_nat(3u);
v___x_964_ = lean_nat_add(v_i_944_, v___x_963_);
v___x_965_ = lean_nat_dec_lt(v___x_964_, v___x_946_);
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_nat_add(v_i_944_, v___x_966_);
v___x_968_ = lean_byte_array_fget(v_bytes_943_, v___x_967_);
lean_dec(v___x_967_);
v___x_969_ = lean_uint8_land(v___x_968_, v___x_955_);
v___x_970_ = lean_uint8_dec_eq(v___x_969_, v___x_949_);
v___x_971_ = lean_unsigned_to_nat(2u);
v___x_972_ = lean_nat_add(v_i_944_, v___x_971_);
v___x_973_ = lean_byte_array_fget(v_bytes_943_, v___x_972_);
lean_dec(v___x_972_);
v___x_974_ = lean_uint8_land(v___x_973_, v___x_955_);
v___x_975_ = lean_uint8_dec_eq(v___x_974_, v___x_949_);
v___x_976_ = lean_byte_array_fget(v_bytes_943_, v___x_964_);
lean_dec(v___x_964_);
v___x_977_ = lean_uint8_land(v___x_976_, v___x_955_);
v___x_978_ = lean_uint8_dec_eq(v___x_977_, v___x_949_);
v___x_979_ = 7;
v_b_u2080_980_ = lean_uint8_land(v___x_948_, v___x_979_);
v___x_981_ = 63;
v_b_u2081_982_ = lean_uint8_land(v___x_968_, v___x_981_);
v_b_u2082_983_ = lean_uint8_land(v___x_973_, v___x_981_);
v_b_u2083_984_ = lean_uint8_land(v___x_976_, v___x_981_);
v___x_985_ = lean_uint8_to_uint32(v_b_u2080_980_);
v___x_986_ = 18;
v___x_987_ = lean_uint32_shift_left(v___x_985_, v___x_986_);
v___x_988_ = lean_uint8_to_uint32(v_b_u2081_982_);
v___x_989_ = 12;
v___x_990_ = lean_uint32_shift_left(v___x_988_, v___x_989_);
v___x_991_ = lean_uint32_lor(v___x_987_, v___x_990_);
v___x_992_ = lean_uint8_to_uint32(v_b_u2082_983_);
v___x_993_ = 6;
v___x_994_ = lean_uint32_shift_left(v___x_992_, v___x_993_);
v___x_995_ = lean_uint32_lor(v___x_991_, v___x_994_);
v___x_996_ = lean_uint8_to_uint32(v_b_u2083_984_);
v_r_997_ = lean_uint32_lor(v___x_995_, v___x_996_);
v___x_998_ = 65536;
v___x_999_ = lean_uint32_dec_lt(v_r_997_, v___x_998_);
v___x_1000_ = 1114111;
v___x_1001_ = lean_uint32_dec_lt(v___x_1000_, v_r_997_);
return v_r_997_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; uint8_t v___x_1008_; uint8_t v___x_1009_; uint8_t v___x_1010_; uint8_t v___x_1011_; uint8_t v___x_1012_; uint8_t v___x_1013_; uint8_t v_b_u2080_1014_; uint8_t v___x_1015_; uint8_t v_b_u2081_1016_; uint8_t v_b_u2082_1017_; uint32_t v___x_1018_; uint32_t v___x_1019_; uint32_t v___x_1020_; uint32_t v___x_1021_; uint32_t v___x_1022_; uint32_t v___x_1023_; uint32_t v___x_1024_; uint32_t v___x_1025_; uint32_t v_r_1026_; uint32_t v___x_1027_; uint8_t v___x_1028_; uint32_t v___x_1029_; uint8_t v___x_1030_; 
v___x_1002_ = lean_unsigned_to_nat(2u);
v___x_1003_ = lean_nat_add(v_i_944_, v___x_1002_);
v___x_1004_ = lean_nat_dec_lt(v___x_1003_, v___x_946_);
v___x_1005_ = lean_unsigned_to_nat(1u);
v___x_1006_ = lean_nat_add(v_i_944_, v___x_1005_);
v___x_1007_ = lean_byte_array_fget(v_bytes_943_, v___x_1006_);
lean_dec(v___x_1006_);
v___x_1008_ = lean_uint8_land(v___x_1007_, v___x_955_);
v___x_1009_ = lean_uint8_dec_eq(v___x_1008_, v___x_949_);
v___x_1010_ = lean_byte_array_fget(v_bytes_943_, v___x_1003_);
lean_dec(v___x_1003_);
v___x_1011_ = lean_uint8_land(v___x_1010_, v___x_955_);
v___x_1012_ = lean_uint8_dec_eq(v___x_1011_, v___x_949_);
v___x_1013_ = 15;
v_b_u2080_1014_ = lean_uint8_land(v___x_948_, v___x_1013_);
v___x_1015_ = 63;
v_b_u2081_1016_ = lean_uint8_land(v___x_1007_, v___x_1015_);
v_b_u2082_1017_ = lean_uint8_land(v___x_1010_, v___x_1015_);
v___x_1018_ = lean_uint8_to_uint32(v_b_u2080_1014_);
v___x_1019_ = 12;
v___x_1020_ = lean_uint32_shift_left(v___x_1018_, v___x_1019_);
v___x_1021_ = lean_uint8_to_uint32(v_b_u2081_1016_);
v___x_1022_ = 6;
v___x_1023_ = lean_uint32_shift_left(v___x_1021_, v___x_1022_);
v___x_1024_ = lean_uint32_lor(v___x_1020_, v___x_1023_);
v___x_1025_ = lean_uint8_to_uint32(v_b_u2082_1017_);
v_r_1026_ = lean_uint32_lor(v___x_1024_, v___x_1025_);
v___x_1027_ = 2048;
v___x_1028_ = lean_uint32_dec_lt(v_r_1026_, v___x_1027_);
v___x_1029_ = 55296;
v___x_1030_ = lean_uint32_dec_le(v___x_1029_, v_r_1026_);
if (v___x_1030_ == 0)
{
return v_r_1026_;
}
else
{
uint32_t v___x_1031_; uint8_t v___x_1032_; 
v___x_1031_ = 57343;
v___x_1032_ = lean_uint32_dec_le(v_r_1026_, v___x_1031_);
return v_r_1026_;
}
}
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; uint8_t v___x_1036_; uint8_t v___x_1037_; uint8_t v___x_1038_; uint8_t v___x_1039_; uint8_t v_b_u2080_1040_; uint8_t v___x_1041_; uint8_t v_b_u2081_1042_; uint32_t v___x_1043_; uint32_t v___x_1044_; uint32_t v___x_1045_; uint32_t v___x_1046_; uint32_t v_r_1047_; uint32_t v___x_1048_; uint8_t v___x_1049_; 
v___x_1033_ = lean_unsigned_to_nat(1u);
v___x_1034_ = lean_nat_add(v_i_944_, v___x_1033_);
v___x_1035_ = lean_nat_dec_lt(v___x_1034_, v___x_946_);
v___x_1036_ = lean_byte_array_fget(v_bytes_943_, v___x_1034_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_uint8_land(v___x_1036_, v___x_955_);
v___x_1038_ = lean_uint8_dec_eq(v___x_1037_, v___x_949_);
v___x_1039_ = 31;
v_b_u2080_1040_ = lean_uint8_land(v___x_948_, v___x_1039_);
v___x_1041_ = 63;
v_b_u2081_1042_ = lean_uint8_land(v___x_1036_, v___x_1041_);
v___x_1043_ = lean_uint8_to_uint32(v_b_u2080_1040_);
v___x_1044_ = 6;
v___x_1045_ = lean_uint32_shift_left(v___x_1043_, v___x_1044_);
v___x_1046_ = lean_uint8_to_uint32(v_b_u2081_1042_);
v_r_1047_ = lean_uint32_lor(v___x_1045_, v___x_1046_);
v___x_1048_ = 128;
v___x_1049_ = lean_uint32_dec_lt(v_r_1047_, v___x_1048_);
return v_r_1047_;
}
}
else
{
uint32_t v___x_1050_; 
v___x_1050_ = lean_uint8_to_uint32(v___x_948_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___boxed(lean_object* v_bytes_1051_, lean_object* v_i_1052_, lean_object* v_h_1053_){
_start:
{
uint32_t v_res_1054_; lean_object* v_r_1055_; 
v_res_1054_ = l_ByteArray_utf8DecodeChar(v_bytes_1051_, v_i_1052_, v_h_1053_);
lean_dec(v_i_1052_);
lean_dec_ref(v_bytes_1051_);
v_r_1055_ = lean_box_uint32(v_res_1054_);
return v_r_1055_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableIsUTF8FirstByte___aux__1(uint8_t v_c_1056_){
_start:
{
uint8_t v___x_1057_; uint8_t v___x_1058_; uint8_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1057_ = 128;
v___x_1058_ = lean_uint8_land(v_c_1056_, v___x_1057_);
v___x_1059_ = 0;
v___x_1060_ = lean_uint8_dec_eq(v___x_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
uint8_t v___x_1061_; uint8_t v___x_1062_; uint8_t v___x_1063_; uint8_t v___x_1064_; 
v___x_1061_ = 224;
v___x_1062_ = lean_uint8_land(v_c_1056_, v___x_1061_);
v___x_1063_ = 192;
v___x_1064_ = lean_uint8_dec_eq(v___x_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
uint8_t v___x_1065_; uint8_t v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = 240;
v___x_1066_ = lean_uint8_land(v_c_1056_, v___x_1065_);
v___x_1067_ = lean_uint8_dec_eq(v___x_1066_, v___x_1061_);
if (v___x_1067_ == 0)
{
uint8_t v___x_1068_; uint8_t v___x_1069_; uint8_t v___x_1070_; 
v___x_1068_ = 248;
v___x_1069_ = lean_uint8_land(v_c_1056_, v___x_1068_);
v___x_1070_ = lean_uint8_dec_eq(v___x_1069_, v___x_1065_);
return v___x_1070_;
}
else
{
return v___x_1067_;
}
}
else
{
return v___x_1064_;
}
}
else
{
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableIsUTF8FirstByte___aux__1___boxed(lean_object* v_c_1071_){
_start:
{
uint8_t v_c_boxed_1072_; uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_c_boxed_1072_ = lean_unbox(v_c_1071_);
v_res_1073_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v_c_boxed_1072_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableIsUTF8FirstByte(uint8_t v___y_1075_){
_start:
{
uint8_t v___x_1076_; 
v___x_1076_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v___y_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableIsUTF8FirstByte___boxed(lean_object* v___y_1077_){
_start:
{
uint8_t v___y_4__boxed_1078_; uint8_t v_res_1079_; lean_object* v_r_1080_; 
v___y_4__boxed_1078_ = lean_unbox(v___y_1077_);
v_res_1079_ = l_UInt8_instDecidableIsUTF8FirstByte(v___y_4__boxed_1078_);
v_r_1080_ = lean_box(v_res_1079_);
return v_r_1080_;
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg(uint8_t v_c_1081_){
_start:
{
uint8_t v___x_1082_; uint8_t v___x_1083_; uint8_t v___x_1084_; uint8_t v___x_1085_; 
v___x_1082_ = 128;
v___x_1083_ = lean_uint8_land(v_c_1081_, v___x_1082_);
v___x_1084_ = 0;
v___x_1085_ = lean_uint8_dec_eq(v___x_1083_, v___x_1084_);
if (v___x_1085_ == 0)
{
uint8_t v___x_1086_; uint8_t v___x_1087_; uint8_t v___x_1088_; uint8_t v___x_1089_; 
v___x_1086_ = 224;
v___x_1087_ = lean_uint8_land(v_c_1081_, v___x_1086_);
v___x_1088_ = 192;
v___x_1089_ = lean_uint8_dec_eq(v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
uint8_t v___x_1090_; uint8_t v___x_1091_; uint8_t v___x_1092_; 
v___x_1090_ = 240;
v___x_1091_ = lean_uint8_land(v_c_1081_, v___x_1090_);
v___x_1092_ = lean_uint8_dec_eq(v___x_1091_, v___x_1086_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_unsigned_to_nat(4u);
return v___x_1093_;
}
else
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_unsigned_to_nat(3u);
return v___x_1094_;
}
}
else
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_unsigned_to_nat(2u);
return v___x_1095_;
}
}
else
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_unsigned_to_nat(1u);
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg___boxed(lean_object* v_c_1097_){
_start:
{
uint8_t v_c_boxed_1098_; lean_object* v_res_1099_; 
v_c_boxed_1098_ = lean_unbox(v_c_1097_);
v_res_1099_ = l_UInt8_utf8ByteSize___redArg(v_c_boxed_1098_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize(uint8_t v_c_1100_, lean_object* v___h_1101_){
_start:
{
uint8_t v___x_1102_; uint8_t v___x_1103_; uint8_t v___x_1104_; uint8_t v___x_1105_; 
v___x_1102_ = 128;
v___x_1103_ = lean_uint8_land(v_c_1100_, v___x_1102_);
v___x_1104_ = 0;
v___x_1105_ = lean_uint8_dec_eq(v___x_1103_, v___x_1104_);
if (v___x_1105_ == 0)
{
uint8_t v___x_1106_; uint8_t v___x_1107_; uint8_t v___x_1108_; uint8_t v___x_1109_; 
v___x_1106_ = 224;
v___x_1107_ = lean_uint8_land(v_c_1100_, v___x_1106_);
v___x_1108_ = 192;
v___x_1109_ = lean_uint8_dec_eq(v___x_1107_, v___x_1108_);
if (v___x_1109_ == 0)
{
uint8_t v___x_1110_; uint8_t v___x_1111_; uint8_t v___x_1112_; 
v___x_1110_ = 240;
v___x_1111_ = lean_uint8_land(v_c_1100_, v___x_1110_);
v___x_1112_ = lean_uint8_dec_eq(v___x_1111_, v___x_1106_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_unsigned_to_nat(4u);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_unsigned_to_nat(3u);
return v___x_1114_;
}
}
else
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_unsigned_to_nat(2u);
return v___x_1115_;
}
}
else
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_unsigned_to_nat(1u);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___boxed(lean_object* v_c_1117_, lean_object* v___h_1118_){
_start:
{
uint8_t v_c_boxed_1119_; lean_object* v_res_1120_; 
v_c_boxed_1119_ = lean_unbox(v_c_1117_);
v_res_1120_ = l_UInt8_utf8ByteSize(v_c_boxed_1119_, v___h_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(uint8_t v_x_1121_){
_start:
{
switch(v_x_1121_)
{
case 0:
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_unsigned_to_nat(0u);
return v___x_1122_;
}
case 1:
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_unsigned_to_nat(1u);
return v___x_1123_;
}
case 2:
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_unsigned_to_nat(2u);
return v___x_1124_;
}
case 3:
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_unsigned_to_nat(3u);
return v___x_1125_;
}
default: 
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_unsigned_to_nat(4u);
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize___boxed(lean_object* v_x_1127_){
_start:
{
uint8_t v_x_54__boxed_1128_; lean_object* v_res_1129_; 
v_x_54__boxed_1128_ = lean_unbox(v_x_1127_);
v_res_1129_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(v_x_54__boxed_1128_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(uint8_t v_x_1130_, lean_object* v_h__1_1131_, lean_object* v_h__2_1132_, lean_object* v_h__3_1133_, lean_object* v_h__4_1134_, lean_object* v_h__5_1135_){
_start:
{
switch(v_x_1130_)
{
case 0:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec(v_h__5_1135_);
lean_dec(v_h__4_1134_);
lean_dec(v_h__3_1133_);
lean_dec(v_h__2_1132_);
v___x_1136_ = lean_box(0);
v___x_1137_ = lean_apply_1(v_h__1_1131_, v___x_1136_);
return v___x_1137_;
}
case 1:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v_h__5_1135_);
lean_dec(v_h__4_1134_);
lean_dec(v_h__3_1133_);
lean_dec(v_h__1_1131_);
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_apply_1(v_h__2_1132_, v___x_1138_);
return v___x_1139_;
}
case 2:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_dec(v_h__5_1135_);
lean_dec(v_h__4_1134_);
lean_dec(v_h__2_1132_);
lean_dec(v_h__1_1131_);
v___x_1140_ = lean_box(0);
v___x_1141_ = lean_apply_1(v_h__3_1133_, v___x_1140_);
return v___x_1141_;
}
case 3:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec(v_h__5_1135_);
lean_dec(v_h__3_1133_);
lean_dec(v_h__2_1132_);
lean_dec(v_h__1_1131_);
v___x_1142_ = lean_box(0);
v___x_1143_ = lean_apply_1(v_h__4_1134_, v___x_1142_);
return v___x_1143_;
}
default: 
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec(v_h__4_1134_);
lean_dec(v_h__3_1133_);
lean_dec(v_h__2_1132_);
lean_dec(v_h__1_1131_);
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_apply_1(v_h__5_1135_, v___x_1144_);
return v___x_1145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg___boxed(lean_object* v_x_1146_, lean_object* v_h__1_1147_, lean_object* v_h__2_1148_, lean_object* v_h__3_1149_, lean_object* v_h__4_1150_, lean_object* v_h__5_1151_){
_start:
{
uint8_t v_x_56__boxed_1152_; lean_object* v_res_1153_; 
v_x_56__boxed_1152_ = lean_unbox(v_x_1146_);
v_res_1153_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(v_x_56__boxed_1152_, v_h__1_1147_, v_h__2_1148_, v_h__3_1149_, v_h__4_1150_, v_h__5_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(lean_object* v_motive_1154_, uint8_t v_x_1155_, lean_object* v_h__1_1156_, lean_object* v_h__2_1157_, lean_object* v_h__3_1158_, lean_object* v_h__4_1159_, lean_object* v_h__5_1160_){
_start:
{
switch(v_x_1155_)
{
case 0:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec(v_h__5_1160_);
lean_dec(v_h__4_1159_);
lean_dec(v_h__3_1158_);
lean_dec(v_h__2_1157_);
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_apply_1(v_h__1_1156_, v___x_1161_);
return v___x_1162_;
}
case 1:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec(v_h__5_1160_);
lean_dec(v_h__4_1159_);
lean_dec(v_h__3_1158_);
lean_dec(v_h__1_1156_);
v___x_1163_ = lean_box(0);
v___x_1164_ = lean_apply_1(v_h__2_1157_, v___x_1163_);
return v___x_1164_;
}
case 2:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec(v_h__5_1160_);
lean_dec(v_h__4_1159_);
lean_dec(v_h__2_1157_);
lean_dec(v_h__1_1156_);
v___x_1165_ = lean_box(0);
v___x_1166_ = lean_apply_1(v_h__3_1158_, v___x_1165_);
return v___x_1166_;
}
case 3:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec(v_h__5_1160_);
lean_dec(v_h__3_1158_);
lean_dec(v_h__2_1157_);
lean_dec(v_h__1_1156_);
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_apply_1(v_h__4_1159_, v___x_1167_);
return v___x_1168_;
}
default: 
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_dec(v_h__4_1159_);
lean_dec(v_h__3_1158_);
lean_dec(v_h__2_1157_);
lean_dec(v_h__1_1156_);
v___x_1169_ = lean_box(0);
v___x_1170_ = lean_apply_1(v_h__5_1160_, v___x_1169_);
return v___x_1170_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___boxed(lean_object* v_motive_1171_, lean_object* v_x_1172_, lean_object* v_h__1_1173_, lean_object* v_h__2_1174_, lean_object* v_h__3_1175_, lean_object* v_h__4_1176_, lean_object* v_h__5_1177_){
_start:
{
uint8_t v_x_79__boxed_1178_; lean_object* v_res_1179_; 
v_x_79__boxed_1178_ = lean_unbox(v_x_1172_);
v_res_1179_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(v_motive_1171_, v_x_79__boxed_1178_, v_h__1_1173_, v_h__2_1174_, v_h__3_1175_, v_h__4_1176_, v_h__5_1177_);
return v_res_1179_;
}
}
lean_object* runtime_initialize_Init_Data_Char_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Bitwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Decode(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Decode(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Char_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Bitwise(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Decode(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Decode(builtin);
}
#ifdef __cplusplus
}
#endif

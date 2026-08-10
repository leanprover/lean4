// Lean compiler output
// Module: Init.Data.String.Decode
// Imports: import Init.Data.Char.Lemmas public import Init.Data.ByteArray.Basic import Init.Data.ByteArray.Lemmas public import Init.Data.UInt.Basic import Init.Data.BitVec.Bootstrap import Init.Data.BitVec.Lemmas import Init.Data.Nat.Internal.Linear import Init.Data.Nat.MinMax import Init.Data.Option.Lemmas import Init.Data.UInt.Bitwise import Init.Data.UInt.Lemmas import Init.Omega
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
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg(lean_object* v_k_96_){
_start:
{
lean_inc(v_k_96_);
return v_k_96_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg___boxed(lean_object* v_k_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg(v_k_97_);
lean_dec(v_k_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim(lean_object* v_motive_99_, lean_object* v_ctorIdx_100_, uint8_t v_t_101_, lean_object* v_h_102_, lean_object* v_k_103_){
_start:
{
lean_inc(v_k_103_);
return v_k_103_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___boxed(lean_object* v_motive_104_, lean_object* v_ctorIdx_105_, lean_object* v_t_106_, lean_object* v_h_107_, lean_object* v_k_108_){
_start:
{
uint8_t v_t_boxed_109_; lean_object* v_res_110_; 
v_t_boxed_109_ = lean_unbox(v_t_106_);
v_res_110_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim(v_motive_104_, v_ctorIdx_105_, v_t_boxed_109_, v_h_107_, v_k_108_);
lean_dec(v_k_108_);
lean_dec(v_ctorIdx_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg(lean_object* v_invalid_111_){
_start:
{
lean_inc(v_invalid_111_);
return v_invalid_111_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg___boxed(lean_object* v_invalid_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg(v_invalid_112_);
lean_dec(v_invalid_112_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(lean_object* v_motive_114_, uint8_t v_t_115_, lean_object* v_h_116_, lean_object* v_invalid_117_){
_start:
{
lean_inc(v_invalid_117_);
return v_invalid_117_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___boxed(lean_object* v_motive_118_, lean_object* v_t_119_, lean_object* v_h_120_, lean_object* v_invalid_121_){
_start:
{
uint8_t v_t_boxed_122_; lean_object* v_res_123_; 
v_t_boxed_122_ = lean_unbox(v_t_119_);
v_res_123_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(v_motive_118_, v_t_boxed_122_, v_h_120_, v_invalid_121_);
lean_dec(v_invalid_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg(lean_object* v_done_124_){
_start:
{
lean_inc(v_done_124_);
return v_done_124_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg___boxed(lean_object* v_done_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg(v_done_125_);
lean_dec(v_done_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(lean_object* v_motive_127_, uint8_t v_t_128_, lean_object* v_h_129_, lean_object* v_done_130_){
_start:
{
lean_inc(v_done_130_);
return v_done_130_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___boxed(lean_object* v_motive_131_, lean_object* v_t_132_, lean_object* v_h_133_, lean_object* v_done_134_){
_start:
{
uint8_t v_t_boxed_135_; lean_object* v_res_136_; 
v_t_boxed_135_ = lean_unbox(v_t_132_);
v_res_136_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(v_motive_131_, v_t_boxed_135_, v_h_133_, v_done_134_);
lean_dec(v_done_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg(lean_object* v_oneMore_137_){
_start:
{
lean_inc(v_oneMore_137_);
return v_oneMore_137_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg___boxed(lean_object* v_oneMore_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg(v_oneMore_138_);
lean_dec(v_oneMore_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(lean_object* v_motive_140_, uint8_t v_t_141_, lean_object* v_h_142_, lean_object* v_oneMore_143_){
_start:
{
lean_inc(v_oneMore_143_);
return v_oneMore_143_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___boxed(lean_object* v_motive_144_, lean_object* v_t_145_, lean_object* v_h_146_, lean_object* v_oneMore_147_){
_start:
{
uint8_t v_t_boxed_148_; lean_object* v_res_149_; 
v_t_boxed_148_ = lean_unbox(v_t_145_);
v_res_149_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(v_motive_144_, v_t_boxed_148_, v_h_146_, v_oneMore_147_);
lean_dec(v_oneMore_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg(lean_object* v_twoMore_150_){
_start:
{
lean_inc(v_twoMore_150_);
return v_twoMore_150_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg___boxed(lean_object* v_twoMore_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg(v_twoMore_151_);
lean_dec(v_twoMore_151_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(lean_object* v_motive_153_, uint8_t v_t_154_, lean_object* v_h_155_, lean_object* v_twoMore_156_){
_start:
{
lean_inc(v_twoMore_156_);
return v_twoMore_156_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___boxed(lean_object* v_motive_157_, lean_object* v_t_158_, lean_object* v_h_159_, lean_object* v_twoMore_160_){
_start:
{
uint8_t v_t_boxed_161_; lean_object* v_res_162_; 
v_t_boxed_161_ = lean_unbox(v_t_158_);
v_res_162_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(v_motive_157_, v_t_boxed_161_, v_h_159_, v_twoMore_160_);
lean_dec(v_twoMore_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg(lean_object* v_threeMore_163_){
_start:
{
lean_inc(v_threeMore_163_);
return v_threeMore_163_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg___boxed(lean_object* v_threeMore_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg(v_threeMore_164_);
lean_dec(v_threeMore_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim(lean_object* v_motive_166_, uint8_t v_t_167_, lean_object* v_h_168_, lean_object* v_threeMore_169_){
_start:
{
lean_inc(v_threeMore_169_);
return v_threeMore_169_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___boxed(lean_object* v_motive_170_, lean_object* v_t_171_, lean_object* v_h_172_, lean_object* v_threeMore_173_){
_start:
{
uint8_t v_t_boxed_174_; lean_object* v_res_175_; 
v_t_boxed_174_ = lean_unbox(v_t_171_);
v_res_175_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim(v_motive_170_, v_t_boxed_174_, v_h_172_, v_threeMore_173_);
lean_dec(v_threeMore_173_);
return v_res_175_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(uint8_t v_b_176_){
_start:
{
uint8_t v___x_177_; uint8_t v___x_178_; uint8_t v___x_179_; uint8_t v___x_180_; 
v___x_177_ = 128;
v___x_178_ = lean_uint8_land(v_b_176_, v___x_177_);
v___x_179_ = 0;
v___x_180_ = lean_uint8_dec_eq(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
uint8_t v___x_181_; uint8_t v___x_182_; uint8_t v___x_183_; uint8_t v___x_184_; 
v___x_181_ = 224;
v___x_182_ = lean_uint8_land(v_b_176_, v___x_181_);
v___x_183_ = 192;
v___x_184_ = lean_uint8_dec_eq(v___x_182_, v___x_183_);
if (v___x_184_ == 0)
{
uint8_t v___x_185_; uint8_t v___x_186_; uint8_t v___x_187_; 
v___x_185_ = 240;
v___x_186_ = lean_uint8_land(v_b_176_, v___x_185_);
v___x_187_ = lean_uint8_dec_eq(v___x_186_, v___x_181_);
if (v___x_187_ == 0)
{
uint8_t v___x_188_; uint8_t v___x_189_; uint8_t v___x_190_; 
v___x_188_ = 248;
v___x_189_ = lean_uint8_land(v_b_176_, v___x_188_);
v___x_190_ = lean_uint8_dec_eq(v___x_189_, v___x_185_);
if (v___x_190_ == 0)
{
uint8_t v___x_191_; 
v___x_191_ = 0;
return v___x_191_;
}
else
{
uint8_t v___x_192_; 
v___x_192_ = 4;
return v___x_192_;
}
}
else
{
uint8_t v___x_193_; 
v___x_193_ = 3;
return v___x_193_;
}
}
else
{
uint8_t v___x_194_; 
v___x_194_ = 2;
return v___x_194_;
}
}
else
{
uint8_t v___x_195_; 
v___x_195_ = 1;
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_parseFirstByte___boxed(lean_object* v_b_196_){
_start:
{
uint8_t v_b_boxed_197_; uint8_t v_res_198_; lean_object* v_r_199_; 
v_b_boxed_197_ = lean_unbox(v_b_196_);
v_res_198_ = l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(v_b_boxed_197_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(uint8_t v_b_200_){
_start:
{
uint8_t v___x_201_; uint8_t v___x_202_; uint8_t v___x_203_; uint8_t v___x_204_; 
v___x_201_ = 192;
v___x_202_ = lean_uint8_land(v_b_200_, v___x_201_);
v___x_203_ = 128;
v___x_204_ = lean_uint8_dec_eq(v___x_202_, v___x_203_);
if (v___x_204_ == 0)
{
uint8_t v___x_205_; 
v___x_205_ = 1;
return v___x_205_;
}
else
{
uint8_t v___x_206_; 
v___x_206_ = 0;
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte___boxed(lean_object* v_b_207_){
_start:
{
uint8_t v_b_boxed_208_; uint8_t v_res_209_; lean_object* v_r_210_; 
v_b_boxed_208_ = lean_unbox(v_b_207_);
v_res_209_ = l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(v_b_boxed_208_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(uint8_t v_w_211_){
_start:
{
uint32_t v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_uint8_to_uint32(v_w_211_);
v___x_213_ = lean_box_uint32(v___x_212_);
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg___boxed(lean_object* v_w_215_){
_start:
{
uint8_t v_w_boxed_216_; lean_object* v_res_217_; 
v_w_boxed_216_ = lean_unbox(v_w_215_);
v_res_217_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(v_w_boxed_216_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(uint8_t v_w_218_, lean_object* v_h_219_){
_start:
{
uint32_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = lean_uint8_to_uint32(v_w_218_);
v___x_221_ = lean_box_uint32(v___x_220_);
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___boxed(lean_object* v_w_223_, lean_object* v_h_224_){
_start:
{
uint8_t v_w_boxed_225_; lean_object* v_res_226_; 
v_w_boxed_225_ = lean_unbox(v_w_223_);
v_res_226_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(v_w_boxed_225_, v_h_224_);
return v_res_226_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2081(uint8_t v_w_227_, uint8_t v___w_228_, lean_object* v___h_229_){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = 1;
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2081___boxed(lean_object* v_w_231_, lean_object* v___w_232_, lean_object* v___h_233_){
_start:
{
uint8_t v_w_boxed_234_; uint8_t v___w_boxed_235_; uint8_t v_res_236_; lean_object* v_r_237_; 
v_w_boxed_234_ = lean_unbox(v_w_231_);
v___w_boxed_235_ = lean_unbox(v___w_232_);
v_res_236_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2081(v_w_boxed_234_, v___w_boxed_235_, v___h_233_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(uint8_t v_w_238_, uint8_t v_x_239_){
_start:
{
uint8_t v___x_240_; uint8_t v_b_u2080_241_; uint8_t v___x_242_; uint8_t v_b_u2081_243_; uint32_t v___x_244_; uint32_t v___x_245_; uint32_t v___x_246_; uint32_t v___x_247_; uint32_t v___x_248_; 
v___x_240_ = 31;
v_b_u2080_241_ = lean_uint8_land(v_w_238_, v___x_240_);
v___x_242_ = 63;
v_b_u2081_243_ = lean_uint8_land(v_x_239_, v___x_242_);
v___x_244_ = lean_uint8_to_uint32(v_b_u2080_241_);
v___x_245_ = 6;
v___x_246_ = lean_uint32_shift_left(v___x_244_, v___x_245_);
v___x_247_ = lean_uint8_to_uint32(v_b_u2081_243_);
v___x_248_ = lean_uint32_lor(v___x_246_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked___boxed(lean_object* v_w_249_, lean_object* v_x_250_){
_start:
{
uint8_t v_w_boxed_251_; uint8_t v_x_boxed_252_; uint32_t v_res_253_; lean_object* v_r_254_; 
v_w_boxed_251_ = lean_unbox(v_w_249_);
v_x_boxed_252_ = lean_unbox(v_x_250_);
v_res_253_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(v_w_boxed_251_, v_x_boxed_252_);
v_r_254_ = lean_box_uint32(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(uint8_t v_w_255_, uint8_t v_x_256_){
_start:
{
uint8_t v___x_257_; uint8_t v___x_258_; uint8_t v___x_259_; uint8_t v___x_260_; 
v___x_257_ = 192;
v___x_258_ = lean_uint8_land(v_x_256_, v___x_257_);
v___x_259_ = 128;
v___x_260_ = lean_uint8_dec_eq(v___x_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_box(0);
return v___x_261_;
}
else
{
uint8_t v___x_262_; uint8_t v_b_u2080_263_; uint8_t v___x_264_; uint8_t v_b_u2081_265_; uint32_t v___x_266_; uint32_t v___x_267_; uint32_t v___x_268_; uint32_t v___x_269_; uint32_t v_r_270_; uint32_t v___x_271_; uint8_t v___x_272_; 
v___x_262_ = 31;
v_b_u2080_263_ = lean_uint8_land(v_w_255_, v___x_262_);
v___x_264_ = 63;
v_b_u2081_265_ = lean_uint8_land(v_x_256_, v___x_264_);
v___x_266_ = lean_uint8_to_uint32(v_b_u2080_263_);
v___x_267_ = 6;
v___x_268_ = lean_uint32_shift_left(v___x_266_, v___x_267_);
v___x_269_ = lean_uint8_to_uint32(v_b_u2081_265_);
v_r_270_ = lean_uint32_lor(v___x_268_, v___x_269_);
v___x_271_ = 128;
v___x_272_ = lean_uint32_dec_lt(v_r_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_box_uint32(v_r_270_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = lean_box(0);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082___boxed(lean_object* v_w_276_, lean_object* v_x_277_){
_start:
{
uint8_t v_w_boxed_278_; uint8_t v_x_boxed_279_; lean_object* v_res_280_; 
v_w_boxed_278_ = lean_unbox(v_w_276_);
v_x_boxed_279_ = lean_unbox(v_x_277_);
v_res_280_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(v_w_boxed_278_, v_x_boxed_279_);
return v_res_280_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2082(uint8_t v_w_281_, uint8_t v_x_282_){
_start:
{
uint8_t v___x_283_; uint8_t v___x_284_; uint8_t v___x_285_; uint8_t v___x_286_; 
v___x_283_ = 192;
v___x_284_ = lean_uint8_land(v_x_282_, v___x_283_);
v___x_285_ = 128;
v___x_286_ = lean_uint8_dec_eq(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
return v___x_286_;
}
else
{
uint8_t v___x_287_; uint8_t v_b_u2080_288_; uint8_t v___x_289_; uint8_t v_b_u2081_290_; uint32_t v___x_291_; uint32_t v___x_292_; uint32_t v___x_293_; uint32_t v___x_294_; uint32_t v_r_295_; uint32_t v___x_296_; uint8_t v___x_297_; 
v___x_287_ = 31;
v_b_u2080_288_ = lean_uint8_land(v_w_281_, v___x_287_);
v___x_289_ = 63;
v_b_u2081_290_ = lean_uint8_land(v_x_282_, v___x_289_);
v___x_291_ = lean_uint8_to_uint32(v_b_u2080_288_);
v___x_292_ = 6;
v___x_293_ = lean_uint32_shift_left(v___x_291_, v___x_292_);
v___x_294_ = lean_uint8_to_uint32(v_b_u2081_290_);
v_r_295_ = lean_uint32_lor(v___x_293_, v___x_294_);
v___x_296_ = 128;
v___x_297_ = lean_uint32_dec_le(v___x_296_, v_r_295_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2082___boxed(lean_object* v_w_298_, lean_object* v_x_299_){
_start:
{
uint8_t v_w_boxed_300_; uint8_t v_x_boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_w_boxed_300_ = lean_unbox(v_w_298_);
v_x_boxed_301_ = lean_unbox(v_x_299_);
v_res_302_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2082(v_w_boxed_300_, v_x_boxed_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(uint8_t v_w_304_, uint8_t v_x_305_, uint8_t v_y_306_){
_start:
{
uint8_t v___x_307_; uint8_t v_b_u2080_308_; uint8_t v___x_309_; uint8_t v_b_u2081_310_; uint8_t v_b_u2082_311_; uint32_t v___x_312_; uint32_t v___x_313_; uint32_t v___x_314_; uint32_t v___x_315_; uint32_t v___x_316_; uint32_t v___x_317_; uint32_t v___x_318_; uint32_t v___x_319_; uint32_t v___x_320_; 
v___x_307_ = 15;
v_b_u2080_308_ = lean_uint8_land(v_w_304_, v___x_307_);
v___x_309_ = 63;
v_b_u2081_310_ = lean_uint8_land(v_x_305_, v___x_309_);
v_b_u2082_311_ = lean_uint8_land(v_y_306_, v___x_309_);
v___x_312_ = lean_uint8_to_uint32(v_b_u2080_308_);
v___x_313_ = 12;
v___x_314_ = lean_uint32_shift_left(v___x_312_, v___x_313_);
v___x_315_ = lean_uint8_to_uint32(v_b_u2081_310_);
v___x_316_ = 6;
v___x_317_ = lean_uint32_shift_left(v___x_315_, v___x_316_);
v___x_318_ = lean_uint32_lor(v___x_314_, v___x_317_);
v___x_319_ = lean_uint8_to_uint32(v_b_u2082_311_);
v___x_320_ = lean_uint32_lor(v___x_318_, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked___boxed(lean_object* v_w_321_, lean_object* v_x_322_, lean_object* v_y_323_){
_start:
{
uint8_t v_w_boxed_324_; uint8_t v_x_boxed_325_; uint8_t v_y_boxed_326_; uint32_t v_res_327_; lean_object* v_r_328_; 
v_w_boxed_324_ = lean_unbox(v_w_321_);
v_x_boxed_325_ = lean_unbox(v_x_322_);
v_y_boxed_326_ = lean_unbox(v_y_323_);
v_res_327_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(v_w_boxed_324_, v_x_boxed_325_, v_y_boxed_326_);
v_r_328_ = lean_box_uint32(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(uint8_t v_w_329_, uint8_t v_x_330_, uint8_t v_y_331_){
_start:
{
uint8_t v___x_332_; uint8_t v___x_333_; uint8_t v___x_334_; uint8_t v___x_335_; 
v___x_332_ = 192;
v___x_333_ = lean_uint8_land(v_x_330_, v___x_332_);
v___x_334_ = 128;
v___x_335_ = lean_uint8_dec_eq(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
v___x_336_ = lean_box(0);
return v___x_336_;
}
else
{
uint8_t v___x_337_; uint8_t v___x_338_; 
v___x_337_ = lean_uint8_land(v_y_331_, v___x_332_);
v___x_338_ = lean_uint8_dec_eq(v___x_337_, v___x_334_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
v___x_339_ = lean_box(0);
return v___x_339_;
}
else
{
uint8_t v___x_340_; uint8_t v_b_u2080_341_; uint8_t v___x_342_; uint8_t v_b_u2081_343_; uint8_t v_b_u2082_344_; uint32_t v___x_345_; uint32_t v___x_346_; uint32_t v___x_347_; uint32_t v___x_348_; uint32_t v___x_349_; uint32_t v___x_350_; uint32_t v___x_351_; uint32_t v___x_352_; uint32_t v_r_353_; uint32_t v___x_354_; uint8_t v___x_355_; 
v___x_340_ = 15;
v_b_u2080_341_ = lean_uint8_land(v_w_329_, v___x_340_);
v___x_342_ = 63;
v_b_u2081_343_ = lean_uint8_land(v_x_330_, v___x_342_);
v_b_u2082_344_ = lean_uint8_land(v_y_331_, v___x_342_);
v___x_345_ = lean_uint8_to_uint32(v_b_u2080_341_);
v___x_346_ = 12;
v___x_347_ = lean_uint32_shift_left(v___x_345_, v___x_346_);
v___x_348_ = lean_uint8_to_uint32(v_b_u2081_343_);
v___x_349_ = 6;
v___x_350_ = lean_uint32_shift_left(v___x_348_, v___x_349_);
v___x_351_ = lean_uint32_lor(v___x_347_, v___x_350_);
v___x_352_ = lean_uint8_to_uint32(v_b_u2082_344_);
v_r_353_ = lean_uint32_lor(v___x_351_, v___x_352_);
v___x_354_ = 2048;
v___x_355_ = lean_uint32_dec_lt(v_r_353_, v___x_354_);
if (v___x_355_ == 0)
{
uint32_t v___x_356_; uint8_t v___x_357_; 
v___x_356_ = 55296;
v___x_357_ = lean_uint32_dec_le(v___x_356_, v_r_353_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_box_uint32(v_r_353_);
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
else
{
uint32_t v___x_360_; uint8_t v___x_361_; 
v___x_360_ = 57343;
v___x_361_ = lean_uint32_dec_le(v_r_353_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_box_uint32(v_r_353_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; 
v___x_364_ = lean_box(0);
return v___x_364_;
}
}
}
else
{
lean_object* v___x_365_; 
v___x_365_ = lean_box(0);
return v___x_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083___boxed(lean_object* v_w_366_, lean_object* v_x_367_, lean_object* v_y_368_){
_start:
{
uint8_t v_w_boxed_369_; uint8_t v_x_boxed_370_; uint8_t v_y_boxed_371_; lean_object* v_res_372_; 
v_w_boxed_369_ = lean_unbox(v_w_366_);
v_x_boxed_370_ = lean_unbox(v_x_367_);
v_y_boxed_371_ = lean_unbox(v_y_368_);
v_res_372_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(v_w_boxed_369_, v_x_boxed_370_, v_y_boxed_371_);
return v_res_372_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2083(uint8_t v_w_373_, uint8_t v_x_374_, uint8_t v_y_375_){
_start:
{
uint8_t v___x_376_; uint8_t v___x_377_; uint8_t v___x_378_; uint8_t v___x_379_; 
v___x_376_ = 192;
v___x_377_ = lean_uint8_land(v_x_374_, v___x_376_);
v___x_378_ = 128;
v___x_379_ = lean_uint8_dec_eq(v___x_377_, v___x_378_);
if (v___x_379_ == 0)
{
return v___x_379_;
}
else
{
uint8_t v___x_380_; uint8_t v___x_381_; 
v___x_380_ = lean_uint8_land(v_y_375_, v___x_376_);
v___x_381_ = lean_uint8_dec_eq(v___x_380_, v___x_378_);
if (v___x_381_ == 0)
{
return v___x_381_;
}
else
{
uint8_t v___x_382_; uint8_t v___x_383_; uint8_t v_b_u2080_384_; uint8_t v___x_385_; uint8_t v_b_u2081_386_; uint8_t v_b_u2082_387_; uint32_t v___x_388_; uint32_t v___x_389_; uint32_t v___x_390_; uint32_t v___x_391_; uint32_t v___x_392_; uint32_t v___x_393_; uint32_t v___x_394_; uint32_t v___x_395_; uint32_t v_r_396_; uint32_t v___x_397_; uint8_t v___x_398_; 
v___x_382_ = 0;
v___x_383_ = 15;
v_b_u2080_384_ = lean_uint8_land(v_w_373_, v___x_383_);
v___x_385_ = 63;
v_b_u2081_386_ = lean_uint8_land(v_x_374_, v___x_385_);
v_b_u2082_387_ = lean_uint8_land(v_y_375_, v___x_385_);
v___x_388_ = lean_uint8_to_uint32(v_b_u2080_384_);
v___x_389_ = 12;
v___x_390_ = lean_uint32_shift_left(v___x_388_, v___x_389_);
v___x_391_ = lean_uint8_to_uint32(v_b_u2081_386_);
v___x_392_ = 6;
v___x_393_ = lean_uint32_shift_left(v___x_391_, v___x_392_);
v___x_394_ = lean_uint32_lor(v___x_390_, v___x_393_);
v___x_395_ = lean_uint8_to_uint32(v_b_u2082_387_);
v_r_396_ = lean_uint32_lor(v___x_394_, v___x_395_);
v___x_397_ = 2048;
v___x_398_ = lean_uint32_dec_le(v___x_397_, v_r_396_);
if (v___x_398_ == 0)
{
return v___x_382_;
}
else
{
uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_399_ = 55296;
v___x_400_ = lean_uint32_dec_lt(v_r_396_, v___x_399_);
if (v___x_400_ == 0)
{
uint32_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = 57343;
v___x_402_ = lean_uint32_dec_lt(v___x_401_, v_r_396_);
if (v___x_402_ == 0)
{
return v___x_382_;
}
else
{
return v___x_381_;
}
}
else
{
return v___x_381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2083___boxed(lean_object* v_w_403_, lean_object* v_x_404_, lean_object* v_y_405_){
_start:
{
uint8_t v_w_boxed_406_; uint8_t v_x_boxed_407_; uint8_t v_y_boxed_408_; uint8_t v_res_409_; lean_object* v_r_410_; 
v_w_boxed_406_ = lean_unbox(v_w_403_);
v_x_boxed_407_ = lean_unbox(v_x_404_);
v_y_boxed_408_ = lean_unbox(v_y_405_);
v_res_409_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2083(v_w_boxed_406_, v_x_boxed_407_, v_y_boxed_408_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(uint8_t v_w_411_, uint8_t v_x_412_, uint8_t v_y_413_, uint8_t v_z_414_){
_start:
{
uint8_t v___x_415_; uint8_t v_b_u2080_416_; uint8_t v___x_417_; uint8_t v_b_u2081_418_; uint8_t v_b_u2082_419_; uint8_t v_b_u2083_420_; uint32_t v___x_421_; uint32_t v___x_422_; uint32_t v___x_423_; uint32_t v___x_424_; uint32_t v___x_425_; uint32_t v___x_426_; uint32_t v___x_427_; uint32_t v___x_428_; uint32_t v___x_429_; uint32_t v___x_430_; uint32_t v___x_431_; uint32_t v___x_432_; uint32_t v___x_433_; 
v___x_415_ = 7;
v_b_u2080_416_ = lean_uint8_land(v_w_411_, v___x_415_);
v___x_417_ = 63;
v_b_u2081_418_ = lean_uint8_land(v_x_412_, v___x_417_);
v_b_u2082_419_ = lean_uint8_land(v_y_413_, v___x_417_);
v_b_u2083_420_ = lean_uint8_land(v_z_414_, v___x_417_);
v___x_421_ = lean_uint8_to_uint32(v_b_u2080_416_);
v___x_422_ = 18;
v___x_423_ = lean_uint32_shift_left(v___x_421_, v___x_422_);
v___x_424_ = lean_uint8_to_uint32(v_b_u2081_418_);
v___x_425_ = 12;
v___x_426_ = lean_uint32_shift_left(v___x_424_, v___x_425_);
v___x_427_ = lean_uint32_lor(v___x_423_, v___x_426_);
v___x_428_ = lean_uint8_to_uint32(v_b_u2082_419_);
v___x_429_ = 6;
v___x_430_ = lean_uint32_shift_left(v___x_428_, v___x_429_);
v___x_431_ = lean_uint32_lor(v___x_427_, v___x_430_);
v___x_432_ = lean_uint8_to_uint32(v_b_u2083_420_);
v___x_433_ = lean_uint32_lor(v___x_431_, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked___boxed(lean_object* v_w_434_, lean_object* v_x_435_, lean_object* v_y_436_, lean_object* v_z_437_){
_start:
{
uint8_t v_w_boxed_438_; uint8_t v_x_boxed_439_; uint8_t v_y_boxed_440_; uint8_t v_z_boxed_441_; uint32_t v_res_442_; lean_object* v_r_443_; 
v_w_boxed_438_ = lean_unbox(v_w_434_);
v_x_boxed_439_ = lean_unbox(v_x_435_);
v_y_boxed_440_ = lean_unbox(v_y_436_);
v_z_boxed_441_ = lean_unbox(v_z_437_);
v_res_442_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(v_w_boxed_438_, v_x_boxed_439_, v_y_boxed_440_, v_z_boxed_441_);
v_r_443_ = lean_box_uint32(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(uint8_t v_w_444_, uint8_t v_x_445_, uint8_t v_y_446_, uint8_t v_z_447_){
_start:
{
uint8_t v___x_448_; uint8_t v___x_449_; uint8_t v___x_450_; uint8_t v___x_451_; 
v___x_448_ = 192;
v___x_449_ = lean_uint8_land(v_x_445_, v___x_448_);
v___x_450_ = 128;
v___x_451_ = lean_uint8_dec_eq(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
v___x_452_ = lean_box(0);
return v___x_452_;
}
else
{
uint8_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_uint8_land(v_y_446_, v___x_448_);
v___x_454_ = lean_uint8_dec_eq(v___x_453_, v___x_450_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
v___x_455_ = lean_box(0);
return v___x_455_;
}
else
{
uint8_t v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_uint8_land(v_z_447_, v___x_448_);
v___x_457_ = lean_uint8_dec_eq(v___x_456_, v___x_450_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
v___x_458_ = lean_box(0);
return v___x_458_;
}
else
{
uint8_t v___x_459_; uint8_t v_b_u2080_460_; uint8_t v___x_461_; uint8_t v_b_u2081_462_; uint8_t v_b_u2082_463_; uint8_t v_b_u2083_464_; uint32_t v___x_465_; uint32_t v___x_466_; uint32_t v___x_467_; uint32_t v___x_468_; uint32_t v___x_469_; uint32_t v___x_470_; uint32_t v___x_471_; uint32_t v___x_472_; uint32_t v___x_473_; uint32_t v___x_474_; uint32_t v___x_475_; uint32_t v___x_476_; uint32_t v_r_477_; uint32_t v___x_478_; uint8_t v___x_479_; 
v___x_459_ = 7;
v_b_u2080_460_ = lean_uint8_land(v_w_444_, v___x_459_);
v___x_461_ = 63;
v_b_u2081_462_ = lean_uint8_land(v_x_445_, v___x_461_);
v_b_u2082_463_ = lean_uint8_land(v_y_446_, v___x_461_);
v_b_u2083_464_ = lean_uint8_land(v_z_447_, v___x_461_);
v___x_465_ = lean_uint8_to_uint32(v_b_u2080_460_);
v___x_466_ = 18;
v___x_467_ = lean_uint32_shift_left(v___x_465_, v___x_466_);
v___x_468_ = lean_uint8_to_uint32(v_b_u2081_462_);
v___x_469_ = 12;
v___x_470_ = lean_uint32_shift_left(v___x_468_, v___x_469_);
v___x_471_ = lean_uint32_lor(v___x_467_, v___x_470_);
v___x_472_ = lean_uint8_to_uint32(v_b_u2082_463_);
v___x_473_ = 6;
v___x_474_ = lean_uint32_shift_left(v___x_472_, v___x_473_);
v___x_475_ = lean_uint32_lor(v___x_471_, v___x_474_);
v___x_476_ = lean_uint8_to_uint32(v_b_u2083_464_);
v_r_477_ = lean_uint32_lor(v___x_475_, v___x_476_);
v___x_478_ = 65536;
v___x_479_ = lean_uint32_dec_lt(v_r_477_, v___x_478_);
if (v___x_479_ == 0)
{
uint32_t v___x_480_; uint8_t v___x_481_; 
v___x_480_ = 1114111;
v___x_481_ = lean_uint32_dec_lt(v___x_480_, v_r_477_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_box_uint32(v_r_477_);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
else
{
lean_object* v___x_484_; 
v___x_484_ = lean_box(0);
return v___x_484_;
}
}
else
{
lean_object* v___x_485_; 
v___x_485_ = lean_box(0);
return v___x_485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084___boxed(lean_object* v_w_486_, lean_object* v_x_487_, lean_object* v_y_488_, lean_object* v_z_489_){
_start:
{
uint8_t v_w_boxed_490_; uint8_t v_x_boxed_491_; uint8_t v_y_boxed_492_; uint8_t v_z_boxed_493_; lean_object* v_res_494_; 
v_w_boxed_490_ = lean_unbox(v_w_486_);
v_x_boxed_491_ = lean_unbox(v_x_487_);
v_y_boxed_492_ = lean_unbox(v_y_488_);
v_z_boxed_493_ = lean_unbox(v_z_489_);
v_res_494_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(v_w_boxed_490_, v_x_boxed_491_, v_y_boxed_492_, v_z_boxed_493_);
return v_res_494_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2084(uint8_t v_w_495_, uint8_t v_x_496_, uint8_t v_y_497_, uint8_t v_z_498_){
_start:
{
uint8_t v___x_499_; uint8_t v___x_500_; uint8_t v___x_501_; uint8_t v___x_502_; 
v___x_499_ = 192;
v___x_500_ = lean_uint8_land(v_x_496_, v___x_499_);
v___x_501_ = 128;
v___x_502_ = lean_uint8_dec_eq(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
return v___x_502_;
}
else
{
uint8_t v___x_503_; uint8_t v___x_504_; 
v___x_503_ = lean_uint8_land(v_y_497_, v___x_499_);
v___x_504_ = lean_uint8_dec_eq(v___x_503_, v___x_501_);
if (v___x_504_ == 0)
{
return v___x_504_;
}
else
{
uint8_t v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_uint8_land(v_z_498_, v___x_499_);
v___x_506_ = lean_uint8_dec_eq(v___x_505_, v___x_501_);
if (v___x_506_ == 0)
{
return v___x_506_;
}
else
{
uint8_t v___x_507_; uint8_t v___x_508_; uint8_t v_b_u2080_509_; uint8_t v___x_510_; uint8_t v_b_u2081_511_; uint8_t v_b_u2082_512_; uint8_t v_b_u2083_513_; uint32_t v___x_514_; uint32_t v___x_515_; uint32_t v___x_516_; uint32_t v___x_517_; uint32_t v___x_518_; uint32_t v___x_519_; uint32_t v___x_520_; uint32_t v___x_521_; uint32_t v___x_522_; uint32_t v___x_523_; uint32_t v___x_524_; uint32_t v___x_525_; uint32_t v_r_526_; uint32_t v___x_527_; uint8_t v___x_528_; 
v___x_507_ = 0;
v___x_508_ = 7;
v_b_u2080_509_ = lean_uint8_land(v_w_495_, v___x_508_);
v___x_510_ = 63;
v_b_u2081_511_ = lean_uint8_land(v_x_496_, v___x_510_);
v_b_u2082_512_ = lean_uint8_land(v_y_497_, v___x_510_);
v_b_u2083_513_ = lean_uint8_land(v_z_498_, v___x_510_);
v___x_514_ = lean_uint8_to_uint32(v_b_u2080_509_);
v___x_515_ = 18;
v___x_516_ = lean_uint32_shift_left(v___x_514_, v___x_515_);
v___x_517_ = lean_uint8_to_uint32(v_b_u2081_511_);
v___x_518_ = 12;
v___x_519_ = lean_uint32_shift_left(v___x_517_, v___x_518_);
v___x_520_ = lean_uint32_lor(v___x_516_, v___x_519_);
v___x_521_ = lean_uint8_to_uint32(v_b_u2082_512_);
v___x_522_ = 6;
v___x_523_ = lean_uint32_shift_left(v___x_521_, v___x_522_);
v___x_524_ = lean_uint32_lor(v___x_520_, v___x_523_);
v___x_525_ = lean_uint8_to_uint32(v_b_u2083_513_);
v_r_526_ = lean_uint32_lor(v___x_524_, v___x_525_);
v___x_527_ = 65536;
v___x_528_ = lean_uint32_dec_le(v___x_527_, v_r_526_);
if (v___x_528_ == 0)
{
return v___x_507_;
}
else
{
uint32_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = 1114111;
v___x_530_ = lean_uint32_dec_le(v_r_526_, v___x_529_);
if (v___x_530_ == 0)
{
return v___x_507_;
}
else
{
return v___x_506_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2084___boxed(lean_object* v_w_531_, lean_object* v_x_532_, lean_object* v_y_533_, lean_object* v_z_534_){
_start:
{
uint8_t v_w_boxed_535_; uint8_t v_x_boxed_536_; uint8_t v_y_boxed_537_; uint8_t v_z_boxed_538_; uint8_t v_res_539_; lean_object* v_r_540_; 
v_w_boxed_535_ = lean_unbox(v_w_531_);
v_x_boxed_536_ = lean_unbox(v_x_532_);
v_y_boxed_537_ = lean_unbox(v_y_533_);
v_z_boxed_538_ = lean_unbox(v_z_534_);
v_res_539_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2084(v_w_boxed_535_, v_x_boxed_536_, v_y_boxed_537_, v_z_boxed_538_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f(lean_object* v_bytes_541_, lean_object* v_i_542_){
_start:
{
lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_byte_array_size(v_bytes_541_);
v___x_544_ = lean_nat_dec_lt(v_i_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; 
v___x_545_ = lean_box(0);
return v___x_545_;
}
else
{
uint8_t v___x_546_; uint8_t v___x_547_; uint8_t v___x_548_; uint8_t v___x_549_; uint8_t v___x_550_; 
v___x_546_ = lean_byte_array_fget(v_bytes_541_, v_i_542_);
v___x_547_ = 128;
v___x_548_ = lean_uint8_land(v___x_546_, v___x_547_);
v___x_549_ = 0;
v___x_550_ = lean_uint8_dec_eq(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
uint8_t v___x_551_; uint8_t v___x_552_; uint8_t v___x_553_; uint8_t v___x_554_; 
v___x_551_ = 224;
v___x_552_ = lean_uint8_land(v___x_546_, v___x_551_);
v___x_553_ = 192;
v___x_554_ = lean_uint8_dec_eq(v___x_552_, v___x_553_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; uint8_t v___x_556_; uint8_t v___x_557_; 
v___x_555_ = 240;
v___x_556_ = lean_uint8_land(v___x_546_, v___x_555_);
v___x_557_ = lean_uint8_dec_eq(v___x_556_, v___x_551_);
if (v___x_557_ == 0)
{
uint8_t v___x_558_; uint8_t v___x_559_; uint8_t v___x_560_; 
v___x_558_ = 248;
v___x_559_ = lean_uint8_land(v___x_546_, v___x_558_);
v___x_560_ = lean_uint8_dec_eq(v___x_559_, v___x_555_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_box(0);
return v___x_561_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_562_ = lean_unsigned_to_nat(3u);
v___x_563_ = lean_nat_add(v_i_542_, v___x_562_);
v___x_564_ = lean_nat_dec_lt(v___x_563_, v___x_543_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
lean_dec(v___x_563_);
v___x_565_ = lean_box(0);
return v___x_565_;
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; uint8_t v___x_569_; uint8_t v___x_570_; 
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = lean_nat_add(v_i_542_, v___x_566_);
v___x_568_ = lean_byte_array_fget(v_bytes_541_, v___x_567_);
lean_dec(v___x_567_);
v___x_569_ = lean_uint8_land(v___x_568_, v___x_553_);
v___x_570_ = lean_uint8_dec_eq(v___x_569_, v___x_547_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
lean_dec(v___x_563_);
v___x_571_ = lean_box(0);
return v___x_571_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; uint8_t v___x_575_; uint8_t v___x_576_; 
v___x_572_ = lean_unsigned_to_nat(2u);
v___x_573_ = lean_nat_add(v_i_542_, v___x_572_);
v___x_574_ = lean_byte_array_fget(v_bytes_541_, v___x_573_);
lean_dec(v___x_573_);
v___x_575_ = lean_uint8_land(v___x_574_, v___x_553_);
v___x_576_ = lean_uint8_dec_eq(v___x_575_, v___x_547_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
lean_dec(v___x_563_);
v___x_577_ = lean_box(0);
return v___x_577_;
}
else
{
uint8_t v___x_578_; uint8_t v___x_579_; uint8_t v___x_580_; 
v___x_578_ = lean_byte_array_fget(v_bytes_541_, v___x_563_);
lean_dec(v___x_563_);
v___x_579_ = lean_uint8_land(v___x_578_, v___x_553_);
v___x_580_ = lean_uint8_dec_eq(v___x_579_, v___x_547_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
v___x_581_ = lean_box(0);
return v___x_581_;
}
else
{
uint8_t v___x_582_; uint8_t v_b_u2080_583_; uint8_t v___x_584_; uint8_t v_b_u2081_585_; uint8_t v_b_u2082_586_; uint8_t v_b_u2083_587_; uint32_t v___x_588_; uint32_t v___x_589_; uint32_t v___x_590_; uint32_t v___x_591_; uint32_t v___x_592_; uint32_t v___x_593_; uint32_t v___x_594_; uint32_t v___x_595_; uint32_t v___x_596_; uint32_t v___x_597_; uint32_t v___x_598_; uint32_t v___x_599_; uint32_t v_r_600_; uint32_t v___x_601_; uint8_t v___x_602_; 
v___x_582_ = 7;
v_b_u2080_583_ = lean_uint8_land(v___x_546_, v___x_582_);
v___x_584_ = 63;
v_b_u2081_585_ = lean_uint8_land(v___x_568_, v___x_584_);
v_b_u2082_586_ = lean_uint8_land(v___x_574_, v___x_584_);
v_b_u2083_587_ = lean_uint8_land(v___x_578_, v___x_584_);
v___x_588_ = lean_uint8_to_uint32(v_b_u2080_583_);
v___x_589_ = 18;
v___x_590_ = lean_uint32_shift_left(v___x_588_, v___x_589_);
v___x_591_ = lean_uint8_to_uint32(v_b_u2081_585_);
v___x_592_ = 12;
v___x_593_ = lean_uint32_shift_left(v___x_591_, v___x_592_);
v___x_594_ = lean_uint32_lor(v___x_590_, v___x_593_);
v___x_595_ = lean_uint8_to_uint32(v_b_u2082_586_);
v___x_596_ = 6;
v___x_597_ = lean_uint32_shift_left(v___x_595_, v___x_596_);
v___x_598_ = lean_uint32_lor(v___x_594_, v___x_597_);
v___x_599_ = lean_uint8_to_uint32(v_b_u2083_587_);
v_r_600_ = lean_uint32_lor(v___x_598_, v___x_599_);
v___x_601_ = 65536;
v___x_602_ = lean_uint32_dec_lt(v_r_600_, v___x_601_);
if (v___x_602_ == 0)
{
uint32_t v___x_603_; uint8_t v___x_604_; 
v___x_603_ = 1114111;
v___x_604_ = lean_uint32_dec_lt(v___x_603_, v_r_600_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_box_uint32(v_r_600_);
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; 
v___x_607_ = lean_box(0);
return v___x_607_;
}
}
else
{
lean_object* v___x_608_; 
v___x_608_ = lean_box(0);
return v___x_608_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_609_ = lean_unsigned_to_nat(2u);
v___x_610_ = lean_nat_add(v_i_542_, v___x_609_);
v___x_611_ = lean_nat_dec_lt(v___x_610_, v___x_543_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
lean_dec(v___x_610_);
v___x_612_ = lean_box(0);
return v___x_612_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; uint8_t v___x_616_; uint8_t v___x_617_; 
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_add(v_i_542_, v___x_613_);
v___x_615_ = lean_byte_array_fget(v_bytes_541_, v___x_614_);
lean_dec(v___x_614_);
v___x_616_ = lean_uint8_land(v___x_615_, v___x_553_);
v___x_617_ = lean_uint8_dec_eq(v___x_616_, v___x_547_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_dec(v___x_610_);
v___x_618_ = lean_box(0);
return v___x_618_;
}
else
{
uint8_t v___x_619_; uint8_t v___x_620_; uint8_t v___x_621_; 
v___x_619_ = lean_byte_array_fget(v_bytes_541_, v___x_610_);
lean_dec(v___x_610_);
v___x_620_ = lean_uint8_land(v___x_619_, v___x_553_);
v___x_621_ = lean_uint8_dec_eq(v___x_620_, v___x_547_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
v___x_622_ = lean_box(0);
return v___x_622_;
}
else
{
uint8_t v___x_623_; uint8_t v_b_u2080_624_; uint8_t v___x_625_; uint8_t v_b_u2081_626_; uint8_t v_b_u2082_627_; uint32_t v___x_628_; uint32_t v___x_629_; uint32_t v___x_630_; uint32_t v___x_631_; uint32_t v___x_632_; uint32_t v___x_633_; uint32_t v___x_634_; uint32_t v___x_635_; uint32_t v_r_636_; uint32_t v___x_637_; uint8_t v___x_638_; 
v___x_623_ = 15;
v_b_u2080_624_ = lean_uint8_land(v___x_546_, v___x_623_);
v___x_625_ = 63;
v_b_u2081_626_ = lean_uint8_land(v___x_615_, v___x_625_);
v_b_u2082_627_ = lean_uint8_land(v___x_619_, v___x_625_);
v___x_628_ = lean_uint8_to_uint32(v_b_u2080_624_);
v___x_629_ = 12;
v___x_630_ = lean_uint32_shift_left(v___x_628_, v___x_629_);
v___x_631_ = lean_uint8_to_uint32(v_b_u2081_626_);
v___x_632_ = 6;
v___x_633_ = lean_uint32_shift_left(v___x_631_, v___x_632_);
v___x_634_ = lean_uint32_lor(v___x_630_, v___x_633_);
v___x_635_ = lean_uint8_to_uint32(v_b_u2082_627_);
v_r_636_ = lean_uint32_lor(v___x_634_, v___x_635_);
v___x_637_ = 2048;
v___x_638_ = lean_uint32_dec_lt(v_r_636_, v___x_637_);
if (v___x_638_ == 0)
{
uint32_t v___x_639_; uint8_t v___x_640_; 
v___x_639_ = 55296;
v___x_640_ = lean_uint32_dec_le(v___x_639_, v_r_636_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_box_uint32(v_r_636_);
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
else
{
uint32_t v___x_643_; uint8_t v___x_644_; 
v___x_643_ = 57343;
v___x_644_ = lean_uint32_dec_le(v_r_636_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_box_uint32(v_r_636_);
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = lean_box(0);
return v___x_647_;
}
}
}
else
{
lean_object* v___x_648_; 
v___x_648_ = lean_box(0);
return v___x_648_;
}
}
}
}
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_i_542_, v___x_649_);
v___x_651_ = lean_nat_dec_lt(v___x_650_, v___x_543_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_dec(v___x_650_);
v___x_652_ = lean_box(0);
return v___x_652_;
}
else
{
uint8_t v___x_653_; uint8_t v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_byte_array_fget(v_bytes_541_, v___x_650_);
lean_dec(v___x_650_);
v___x_654_ = lean_uint8_land(v___x_653_, v___x_553_);
v___x_655_ = lean_uint8_dec_eq(v___x_654_, v___x_547_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
v___x_656_ = lean_box(0);
return v___x_656_;
}
else
{
uint8_t v___x_657_; uint8_t v_b_u2080_658_; uint8_t v___x_659_; uint8_t v_b_u2081_660_; uint32_t v___x_661_; uint32_t v___x_662_; uint32_t v___x_663_; uint32_t v___x_664_; uint32_t v_r_665_; uint32_t v___x_666_; uint8_t v___x_667_; 
v___x_657_ = 31;
v_b_u2080_658_ = lean_uint8_land(v___x_546_, v___x_657_);
v___x_659_ = 63;
v_b_u2081_660_ = lean_uint8_land(v___x_653_, v___x_659_);
v___x_661_ = lean_uint8_to_uint32(v_b_u2080_658_);
v___x_662_ = 6;
v___x_663_ = lean_uint32_shift_left(v___x_661_, v___x_662_);
v___x_664_ = lean_uint8_to_uint32(v_b_u2081_660_);
v_r_665_ = lean_uint32_lor(v___x_663_, v___x_664_);
v___x_666_ = 128;
v___x_667_ = lean_uint32_dec_lt(v_r_665_, v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_box_uint32(v_r_665_);
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
else
{
lean_object* v___x_670_; 
v___x_670_ = lean_box(0);
return v___x_670_;
}
}
}
}
}
else
{
uint32_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_uint8_to_uint32(v___x_546_);
v___x_672_ = lean_box_uint32(v___x_671_);
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f___boxed(lean_object* v_bytes_674_, lean_object* v_i_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_ByteArray_utf8DecodeChar_x3f(v_bytes_674_, v_i_675_);
lean_dec(v_i_675_);
lean_dec_ref(v_bytes_674_);
return v_res_676_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8At(lean_object* v_bytes_677_, lean_object* v_i_678_){
_start:
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_byte_array_size(v_bytes_677_);
v___x_680_ = lean_nat_dec_lt(v_i_678_, v___x_679_);
if (v___x_680_ == 0)
{
return v___x_680_;
}
else
{
uint8_t v___x_681_; uint8_t v___x_682_; uint8_t v___x_683_; uint8_t v___x_684_; uint8_t v___x_685_; 
v___x_681_ = lean_byte_array_fget(v_bytes_677_, v_i_678_);
v___x_682_ = 128;
v___x_683_ = lean_uint8_land(v___x_681_, v___x_682_);
v___x_684_ = 0;
v___x_685_ = lean_uint8_dec_eq(v___x_683_, v___x_684_);
if (v___x_685_ == 0)
{
uint8_t v___x_686_; uint8_t v___x_687_; uint8_t v___x_688_; uint8_t v___x_689_; 
v___x_686_ = 224;
v___x_687_ = lean_uint8_land(v___x_681_, v___x_686_);
v___x_688_ = 192;
v___x_689_ = lean_uint8_dec_eq(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
uint8_t v___x_690_; uint8_t v___x_691_; uint8_t v___x_692_; 
v___x_690_ = 240;
v___x_691_ = lean_uint8_land(v___x_681_, v___x_690_);
v___x_692_ = lean_uint8_dec_eq(v___x_691_, v___x_686_);
if (v___x_692_ == 0)
{
uint8_t v___x_693_; uint8_t v___x_694_; uint8_t v___x_695_; 
v___x_693_ = 248;
v___x_694_ = lean_uint8_land(v___x_681_, v___x_693_);
v___x_695_ = lean_uint8_dec_eq(v___x_694_, v___x_690_);
if (v___x_695_ == 0)
{
return v___x_695_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_696_ = lean_unsigned_to_nat(3u);
v___x_697_ = lean_nat_add(v_i_678_, v___x_696_);
v___x_698_ = lean_nat_dec_lt(v___x_697_, v___x_679_);
if (v___x_698_ == 0)
{
lean_dec(v___x_697_);
return v___x_692_;
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; uint8_t v___x_702_; uint8_t v___x_703_; 
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = lean_nat_add(v_i_678_, v___x_699_);
v___x_701_ = lean_byte_array_fget(v_bytes_677_, v___x_700_);
lean_dec(v___x_700_);
v___x_702_ = lean_uint8_land(v___x_701_, v___x_688_);
v___x_703_ = lean_uint8_dec_eq(v___x_702_, v___x_682_);
if (v___x_703_ == 0)
{
lean_dec(v___x_697_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; uint8_t v___x_707_; uint8_t v___x_708_; 
v___x_704_ = lean_unsigned_to_nat(2u);
v___x_705_ = lean_nat_add(v_i_678_, v___x_704_);
v___x_706_ = lean_byte_array_fget(v_bytes_677_, v___x_705_);
lean_dec(v___x_705_);
v___x_707_ = lean_uint8_land(v___x_706_, v___x_688_);
v___x_708_ = lean_uint8_dec_eq(v___x_707_, v___x_682_);
if (v___x_708_ == 0)
{
lean_dec(v___x_697_);
return v___x_708_;
}
else
{
uint8_t v___x_709_; uint8_t v___x_710_; uint8_t v___x_711_; 
v___x_709_ = lean_byte_array_fget(v_bytes_677_, v___x_697_);
lean_dec(v___x_697_);
v___x_710_ = lean_uint8_land(v___x_709_, v___x_688_);
v___x_711_ = lean_uint8_dec_eq(v___x_710_, v___x_682_);
if (v___x_711_ == 0)
{
return v___x_711_;
}
else
{
uint8_t v___x_712_; uint8_t v_b_u2080_713_; uint8_t v___x_714_; uint8_t v_b_u2081_715_; uint8_t v_b_u2082_716_; uint8_t v_b_u2083_717_; uint32_t v___x_718_; uint32_t v___x_719_; uint32_t v___x_720_; uint32_t v___x_721_; uint32_t v___x_722_; uint32_t v___x_723_; uint32_t v___x_724_; uint32_t v___x_725_; uint32_t v___x_726_; uint32_t v___x_727_; uint32_t v___x_728_; uint32_t v___x_729_; uint32_t v_r_730_; uint32_t v___x_731_; uint8_t v___x_732_; 
v___x_712_ = 7;
v_b_u2080_713_ = lean_uint8_land(v___x_681_, v___x_712_);
v___x_714_ = 63;
v_b_u2081_715_ = lean_uint8_land(v___x_701_, v___x_714_);
v_b_u2082_716_ = lean_uint8_land(v___x_706_, v___x_714_);
v_b_u2083_717_ = lean_uint8_land(v___x_709_, v___x_714_);
v___x_718_ = lean_uint8_to_uint32(v_b_u2080_713_);
v___x_719_ = 18;
v___x_720_ = lean_uint32_shift_left(v___x_718_, v___x_719_);
v___x_721_ = lean_uint8_to_uint32(v_b_u2081_715_);
v___x_722_ = 12;
v___x_723_ = lean_uint32_shift_left(v___x_721_, v___x_722_);
v___x_724_ = lean_uint32_lor(v___x_720_, v___x_723_);
v___x_725_ = lean_uint8_to_uint32(v_b_u2082_716_);
v___x_726_ = 6;
v___x_727_ = lean_uint32_shift_left(v___x_725_, v___x_726_);
v___x_728_ = lean_uint32_lor(v___x_724_, v___x_727_);
v___x_729_ = lean_uint8_to_uint32(v_b_u2083_717_);
v_r_730_ = lean_uint32_lor(v___x_728_, v___x_729_);
v___x_731_ = 65536;
v___x_732_ = lean_uint32_dec_le(v___x_731_, v_r_730_);
if (v___x_732_ == 0)
{
return v___x_692_;
}
else
{
uint32_t v___x_733_; uint8_t v___x_734_; 
v___x_733_ = 1114111;
v___x_734_ = lean_uint32_dec_le(v_r_730_, v___x_733_);
if (v___x_734_ == 0)
{
return v___x_692_;
}
else
{
return v___x_711_;
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
lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_735_ = lean_unsigned_to_nat(2u);
v___x_736_ = lean_nat_add(v_i_678_, v___x_735_);
v___x_737_ = lean_nat_dec_lt(v___x_736_, v___x_679_);
if (v___x_737_ == 0)
{
lean_dec(v___x_736_);
return v___x_689_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; uint8_t v___x_741_; uint8_t v___x_742_; 
v___x_738_ = lean_unsigned_to_nat(1u);
v___x_739_ = lean_nat_add(v_i_678_, v___x_738_);
v___x_740_ = lean_byte_array_fget(v_bytes_677_, v___x_739_);
lean_dec(v___x_739_);
v___x_741_ = lean_uint8_land(v___x_740_, v___x_688_);
v___x_742_ = lean_uint8_dec_eq(v___x_741_, v___x_682_);
if (v___x_742_ == 0)
{
lean_dec(v___x_736_);
return v___x_742_;
}
else
{
uint8_t v___x_743_; uint8_t v___x_744_; uint8_t v___x_745_; 
v___x_743_ = lean_byte_array_fget(v_bytes_677_, v___x_736_);
lean_dec(v___x_736_);
v___x_744_ = lean_uint8_land(v___x_743_, v___x_688_);
v___x_745_ = lean_uint8_dec_eq(v___x_744_, v___x_682_);
if (v___x_745_ == 0)
{
return v___x_745_;
}
else
{
uint8_t v___x_746_; uint8_t v_b_u2080_747_; uint8_t v___x_748_; uint8_t v_b_u2081_749_; uint8_t v_b_u2082_750_; uint32_t v___x_751_; uint32_t v___x_752_; uint32_t v___x_753_; uint32_t v___x_754_; uint32_t v___x_755_; uint32_t v___x_756_; uint32_t v___x_757_; uint32_t v___x_758_; uint32_t v_r_759_; uint32_t v___x_760_; uint8_t v___x_761_; 
v___x_746_ = 15;
v_b_u2080_747_ = lean_uint8_land(v___x_681_, v___x_746_);
v___x_748_ = 63;
v_b_u2081_749_ = lean_uint8_land(v___x_740_, v___x_748_);
v_b_u2082_750_ = lean_uint8_land(v___x_743_, v___x_748_);
v___x_751_ = lean_uint8_to_uint32(v_b_u2080_747_);
v___x_752_ = 12;
v___x_753_ = lean_uint32_shift_left(v___x_751_, v___x_752_);
v___x_754_ = lean_uint8_to_uint32(v_b_u2081_749_);
v___x_755_ = 6;
v___x_756_ = lean_uint32_shift_left(v___x_754_, v___x_755_);
v___x_757_ = lean_uint32_lor(v___x_753_, v___x_756_);
v___x_758_ = lean_uint8_to_uint32(v_b_u2082_750_);
v_r_759_ = lean_uint32_lor(v___x_757_, v___x_758_);
v___x_760_ = 2048;
v___x_761_ = lean_uint32_dec_le(v___x_760_, v_r_759_);
if (v___x_761_ == 0)
{
return v___x_689_;
}
else
{
uint32_t v___x_762_; uint8_t v___x_763_; 
v___x_762_ = 55296;
v___x_763_ = lean_uint32_dec_lt(v_r_759_, v___x_762_);
if (v___x_763_ == 0)
{
uint32_t v___x_764_; uint8_t v___x_765_; 
v___x_764_ = 57343;
v___x_765_ = lean_uint32_dec_lt(v___x_764_, v_r_759_);
if (v___x_765_ == 0)
{
return v___x_689_;
}
else
{
return v___x_745_;
}
}
else
{
return v___x_745_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_766_ = lean_unsigned_to_nat(1u);
v___x_767_ = lean_nat_add(v_i_678_, v___x_766_);
v___x_768_ = lean_nat_dec_lt(v___x_767_, v___x_679_);
if (v___x_768_ == 0)
{
lean_dec(v___x_767_);
return v___x_685_;
}
else
{
uint8_t v___x_769_; uint8_t v___x_770_; uint8_t v___x_771_; 
v___x_769_ = lean_byte_array_fget(v_bytes_677_, v___x_767_);
lean_dec(v___x_767_);
v___x_770_ = lean_uint8_land(v___x_769_, v___x_688_);
v___x_771_ = lean_uint8_dec_eq(v___x_770_, v___x_682_);
if (v___x_771_ == 0)
{
return v___x_771_;
}
else
{
uint8_t v___x_772_; uint8_t v_b_u2080_773_; uint8_t v___x_774_; uint8_t v_b_u2081_775_; uint32_t v___x_776_; uint32_t v___x_777_; uint32_t v___x_778_; uint32_t v___x_779_; uint32_t v_r_780_; uint32_t v___x_781_; uint8_t v___x_782_; 
v___x_772_ = 31;
v_b_u2080_773_ = lean_uint8_land(v___x_681_, v___x_772_);
v___x_774_ = 63;
v_b_u2081_775_ = lean_uint8_land(v___x_769_, v___x_774_);
v___x_776_ = lean_uint8_to_uint32(v_b_u2080_773_);
v___x_777_ = 6;
v___x_778_ = lean_uint32_shift_left(v___x_776_, v___x_777_);
v___x_779_ = lean_uint8_to_uint32(v_b_u2081_775_);
v_r_780_ = lean_uint32_lor(v___x_778_, v___x_779_);
v___x_781_ = 128;
v___x_782_ = lean_uint32_dec_le(v___x_781_, v_r_780_);
return v___x_782_;
}
}
}
}
else
{
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8At___boxed(lean_object* v_bytes_783_, lean_object* v_i_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l_ByteArray_validateUTF8At(v_bytes_783_, v_i_784_);
lean_dec(v_i_784_);
lean_dec_ref(v_bytes_783_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t v_x_787_, lean_object* v_h__1_788_, lean_object* v_h__2_789_, lean_object* v_h__3_790_, lean_object* v_h__4_791_, lean_object* v_h__5_792_){
_start:
{
switch(v_x_787_)
{
case 0:
{
lean_object* v___x_793_; 
lean_dec(v_h__5_792_);
lean_dec(v_h__4_791_);
lean_dec(v_h__3_790_);
lean_dec(v_h__2_789_);
v___x_793_ = lean_apply_1(v_h__1_788_, lean_box(0));
return v___x_793_;
}
case 1:
{
lean_object* v___x_794_; 
lean_dec(v_h__5_792_);
lean_dec(v_h__4_791_);
lean_dec(v_h__3_790_);
lean_dec(v_h__1_788_);
v___x_794_ = lean_apply_1(v_h__2_789_, lean_box(0));
return v___x_794_;
}
case 2:
{
lean_object* v___x_795_; 
lean_dec(v_h__5_792_);
lean_dec(v_h__4_791_);
lean_dec(v_h__2_789_);
lean_dec(v_h__1_788_);
v___x_795_ = lean_apply_1(v_h__3_790_, lean_box(0));
return v___x_795_;
}
case 3:
{
lean_object* v___x_796_; 
lean_dec(v_h__5_792_);
lean_dec(v_h__3_790_);
lean_dec(v_h__2_789_);
lean_dec(v_h__1_788_);
v___x_796_ = lean_apply_1(v_h__4_791_, lean_box(0));
return v___x_796_;
}
default: 
{
lean_object* v___x_797_; 
lean_dec(v_h__4_791_);
lean_dec(v_h__3_790_);
lean_dec(v_h__2_789_);
lean_dec(v_h__1_788_);
v___x_797_ = lean_apply_1(v_h__5_792_, lean_box(0));
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_798_, lean_object* v_h__1_799_, lean_object* v_h__2_800_, lean_object* v_h__3_801_, lean_object* v_h__4_802_, lean_object* v_h__5_803_){
_start:
{
uint8_t v_x_47__boxed_804_; lean_object* v_res_805_; 
v_x_47__boxed_804_ = lean_unbox(v_x_798_);
v_res_805_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(v_x_47__boxed_804_, v_h__1_799_, v_h__2_800_, v_h__3_801_, v_h__4_802_, v_h__5_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object* v_motive_806_, uint8_t v_x_807_, lean_object* v_h__1_808_, lean_object* v_h__2_809_, lean_object* v_h__3_810_, lean_object* v_h__4_811_, lean_object* v_h__5_812_){
_start:
{
switch(v_x_807_)
{
case 0:
{
lean_object* v___x_813_; 
lean_dec(v_h__5_812_);
lean_dec(v_h__4_811_);
lean_dec(v_h__3_810_);
lean_dec(v_h__2_809_);
v___x_813_ = lean_apply_1(v_h__1_808_, lean_box(0));
return v___x_813_;
}
case 1:
{
lean_object* v___x_814_; 
lean_dec(v_h__5_812_);
lean_dec(v_h__4_811_);
lean_dec(v_h__3_810_);
lean_dec(v_h__1_808_);
v___x_814_ = lean_apply_1(v_h__2_809_, lean_box(0));
return v___x_814_;
}
case 2:
{
lean_object* v___x_815_; 
lean_dec(v_h__5_812_);
lean_dec(v_h__4_811_);
lean_dec(v_h__2_809_);
lean_dec(v_h__1_808_);
v___x_815_ = lean_apply_1(v_h__3_810_, lean_box(0));
return v___x_815_;
}
case 3:
{
lean_object* v___x_816_; 
lean_dec(v_h__5_812_);
lean_dec(v_h__3_810_);
lean_dec(v_h__2_809_);
lean_dec(v_h__1_808_);
v___x_816_ = lean_apply_1(v_h__4_811_, lean_box(0));
return v___x_816_;
}
default: 
{
lean_object* v___x_817_; 
lean_dec(v_h__4_811_);
lean_dec(v_h__3_810_);
lean_dec(v_h__2_809_);
lean_dec(v_h__1_808_);
v___x_817_ = lean_apply_1(v_h__5_812_, lean_box(0));
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object* v_motive_818_, lean_object* v_x_819_, lean_object* v_h__1_820_, lean_object* v_h__2_821_, lean_object* v_h__3_822_, lean_object* v_h__4_823_, lean_object* v_h__5_824_){
_start:
{
uint8_t v_x_60__boxed_825_; lean_object* v_res_826_; 
v_x_60__boxed_825_ = lean_unbox(v_x_819_);
v_res_826_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(v_motive_818_, v_x_60__boxed_825_, v_h__1_820_, v_h__2_821_, v_h__3_822_, v_h__4_823_, v_h__5_824_);
return v_res_826_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar___redArg(lean_object* v_bytes_827_, lean_object* v_i_828_){
_start:
{
lean_object* v___x_829_; uint8_t v___x_830_; uint8_t v___x_831_; uint8_t v___x_832_; uint8_t v___x_833_; uint8_t v___x_834_; uint8_t v___x_835_; 
v___x_829_ = lean_byte_array_size(v_bytes_827_);
v___x_830_ = lean_nat_dec_lt(v_i_828_, v___x_829_);
v___x_831_ = lean_byte_array_fget(v_bytes_827_, v_i_828_);
v___x_832_ = 128;
v___x_833_ = lean_uint8_land(v___x_831_, v___x_832_);
v___x_834_ = 0;
v___x_835_ = lean_uint8_dec_eq(v___x_833_, v___x_834_);
if (v___x_835_ == 0)
{
uint8_t v___x_836_; uint8_t v___x_837_; uint8_t v___x_838_; uint8_t v___x_839_; 
v___x_836_ = 224;
v___x_837_ = lean_uint8_land(v___x_831_, v___x_836_);
v___x_838_ = 192;
v___x_839_ = lean_uint8_dec_eq(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
uint8_t v___x_840_; uint8_t v___x_841_; uint8_t v___x_842_; 
v___x_840_ = 240;
v___x_841_ = lean_uint8_land(v___x_831_, v___x_840_);
v___x_842_ = lean_uint8_dec_eq(v___x_841_, v___x_836_);
if (v___x_842_ == 0)
{
uint8_t v___x_843_; uint8_t v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; uint8_t v___x_852_; uint8_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; uint8_t v___x_857_; uint8_t v___x_858_; uint8_t v___x_859_; uint8_t v___x_860_; uint8_t v___x_861_; uint8_t v___x_862_; uint8_t v_b_u2080_863_; uint8_t v___x_864_; uint8_t v_b_u2081_865_; uint8_t v_b_u2082_866_; uint8_t v_b_u2083_867_; uint32_t v___x_868_; uint32_t v___x_869_; uint32_t v___x_870_; uint32_t v___x_871_; uint32_t v___x_872_; uint32_t v___x_873_; uint32_t v___x_874_; uint32_t v___x_875_; uint32_t v___x_876_; uint32_t v___x_877_; uint32_t v___x_878_; uint32_t v___x_879_; uint32_t v_r_880_; uint32_t v___x_881_; uint8_t v___x_882_; uint32_t v___x_883_; uint8_t v___x_884_; 
v___x_843_ = 248;
v___x_844_ = lean_uint8_land(v___x_831_, v___x_843_);
v___x_845_ = lean_uint8_dec_eq(v___x_844_, v___x_840_);
v___x_846_ = lean_unsigned_to_nat(3u);
v___x_847_ = lean_nat_add(v_i_828_, v___x_846_);
v___x_848_ = lean_nat_dec_lt(v___x_847_, v___x_829_);
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_nat_add(v_i_828_, v___x_849_);
v___x_851_ = lean_byte_array_fget(v_bytes_827_, v___x_850_);
lean_dec(v___x_850_);
v___x_852_ = lean_uint8_land(v___x_851_, v___x_838_);
v___x_853_ = lean_uint8_dec_eq(v___x_852_, v___x_832_);
v___x_854_ = lean_unsigned_to_nat(2u);
v___x_855_ = lean_nat_add(v_i_828_, v___x_854_);
v___x_856_ = lean_byte_array_fget(v_bytes_827_, v___x_855_);
lean_dec(v___x_855_);
v___x_857_ = lean_uint8_land(v___x_856_, v___x_838_);
v___x_858_ = lean_uint8_dec_eq(v___x_857_, v___x_832_);
v___x_859_ = lean_byte_array_fget(v_bytes_827_, v___x_847_);
lean_dec(v___x_847_);
v___x_860_ = lean_uint8_land(v___x_859_, v___x_838_);
v___x_861_ = lean_uint8_dec_eq(v___x_860_, v___x_832_);
v___x_862_ = 7;
v_b_u2080_863_ = lean_uint8_land(v___x_831_, v___x_862_);
v___x_864_ = 63;
v_b_u2081_865_ = lean_uint8_land(v___x_851_, v___x_864_);
v_b_u2082_866_ = lean_uint8_land(v___x_856_, v___x_864_);
v_b_u2083_867_ = lean_uint8_land(v___x_859_, v___x_864_);
v___x_868_ = lean_uint8_to_uint32(v_b_u2080_863_);
v___x_869_ = 18;
v___x_870_ = lean_uint32_shift_left(v___x_868_, v___x_869_);
v___x_871_ = lean_uint8_to_uint32(v_b_u2081_865_);
v___x_872_ = 12;
v___x_873_ = lean_uint32_shift_left(v___x_871_, v___x_872_);
v___x_874_ = lean_uint32_lor(v___x_870_, v___x_873_);
v___x_875_ = lean_uint8_to_uint32(v_b_u2082_866_);
v___x_876_ = 6;
v___x_877_ = lean_uint32_shift_left(v___x_875_, v___x_876_);
v___x_878_ = lean_uint32_lor(v___x_874_, v___x_877_);
v___x_879_ = lean_uint8_to_uint32(v_b_u2083_867_);
v_r_880_ = lean_uint32_lor(v___x_878_, v___x_879_);
v___x_881_ = 65536;
v___x_882_ = lean_uint32_dec_lt(v_r_880_, v___x_881_);
v___x_883_ = 1114111;
v___x_884_ = lean_uint32_dec_lt(v___x_883_, v_r_880_);
return v_r_880_;
}
else
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; uint8_t v___x_891_; uint8_t v___x_892_; uint8_t v___x_893_; uint8_t v___x_894_; uint8_t v___x_895_; uint8_t v___x_896_; uint8_t v_b_u2080_897_; uint8_t v___x_898_; uint8_t v_b_u2081_899_; uint8_t v_b_u2082_900_; uint32_t v___x_901_; uint32_t v___x_902_; uint32_t v___x_903_; uint32_t v___x_904_; uint32_t v___x_905_; uint32_t v___x_906_; uint32_t v___x_907_; uint32_t v___x_908_; uint32_t v_r_909_; uint32_t v___x_910_; uint8_t v___x_911_; uint32_t v___x_912_; uint8_t v___x_913_; 
v___x_885_ = lean_unsigned_to_nat(2u);
v___x_886_ = lean_nat_add(v_i_828_, v___x_885_);
v___x_887_ = lean_nat_dec_lt(v___x_886_, v___x_829_);
v___x_888_ = lean_unsigned_to_nat(1u);
v___x_889_ = lean_nat_add(v_i_828_, v___x_888_);
v___x_890_ = lean_byte_array_fget(v_bytes_827_, v___x_889_);
lean_dec(v___x_889_);
v___x_891_ = lean_uint8_land(v___x_890_, v___x_838_);
v___x_892_ = lean_uint8_dec_eq(v___x_891_, v___x_832_);
v___x_893_ = lean_byte_array_fget(v_bytes_827_, v___x_886_);
lean_dec(v___x_886_);
v___x_894_ = lean_uint8_land(v___x_893_, v___x_838_);
v___x_895_ = lean_uint8_dec_eq(v___x_894_, v___x_832_);
v___x_896_ = 15;
v_b_u2080_897_ = lean_uint8_land(v___x_831_, v___x_896_);
v___x_898_ = 63;
v_b_u2081_899_ = lean_uint8_land(v___x_890_, v___x_898_);
v_b_u2082_900_ = lean_uint8_land(v___x_893_, v___x_898_);
v___x_901_ = lean_uint8_to_uint32(v_b_u2080_897_);
v___x_902_ = 12;
v___x_903_ = lean_uint32_shift_left(v___x_901_, v___x_902_);
v___x_904_ = lean_uint8_to_uint32(v_b_u2081_899_);
v___x_905_ = 6;
v___x_906_ = lean_uint32_shift_left(v___x_904_, v___x_905_);
v___x_907_ = lean_uint32_lor(v___x_903_, v___x_906_);
v___x_908_ = lean_uint8_to_uint32(v_b_u2082_900_);
v_r_909_ = lean_uint32_lor(v___x_907_, v___x_908_);
v___x_910_ = 2048;
v___x_911_ = lean_uint32_dec_lt(v_r_909_, v___x_910_);
v___x_912_ = 55296;
v___x_913_ = lean_uint32_dec_le(v___x_912_, v_r_909_);
if (v___x_913_ == 0)
{
return v_r_909_;
}
else
{
uint32_t v___x_914_; uint8_t v___x_915_; 
v___x_914_ = 57343;
v___x_915_ = lean_uint32_dec_le(v_r_909_, v___x_914_);
return v_r_909_;
}
}
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; uint8_t v___x_919_; uint8_t v___x_920_; uint8_t v___x_921_; uint8_t v___x_922_; uint8_t v_b_u2080_923_; uint8_t v___x_924_; uint8_t v_b_u2081_925_; uint32_t v___x_926_; uint32_t v___x_927_; uint32_t v___x_928_; uint32_t v___x_929_; uint32_t v_r_930_; uint32_t v___x_931_; uint8_t v___x_932_; 
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_nat_add(v_i_828_, v___x_916_);
v___x_918_ = lean_nat_dec_lt(v___x_917_, v___x_829_);
v___x_919_ = lean_byte_array_fget(v_bytes_827_, v___x_917_);
lean_dec(v___x_917_);
v___x_920_ = lean_uint8_land(v___x_919_, v___x_838_);
v___x_921_ = lean_uint8_dec_eq(v___x_920_, v___x_832_);
v___x_922_ = 31;
v_b_u2080_923_ = lean_uint8_land(v___x_831_, v___x_922_);
v___x_924_ = 63;
v_b_u2081_925_ = lean_uint8_land(v___x_919_, v___x_924_);
v___x_926_ = lean_uint8_to_uint32(v_b_u2080_923_);
v___x_927_ = 6;
v___x_928_ = lean_uint32_shift_left(v___x_926_, v___x_927_);
v___x_929_ = lean_uint8_to_uint32(v_b_u2081_925_);
v_r_930_ = lean_uint32_lor(v___x_928_, v___x_929_);
v___x_931_ = 128;
v___x_932_ = lean_uint32_dec_lt(v_r_930_, v___x_931_);
return v_r_930_;
}
}
else
{
uint32_t v___x_933_; 
v___x_933_ = lean_uint8_to_uint32(v___x_831_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___redArg___boxed(lean_object* v_bytes_934_, lean_object* v_i_935_){
_start:
{
uint32_t v_res_936_; lean_object* v_r_937_; 
v_res_936_ = l_ByteArray_utf8DecodeChar___redArg(v_bytes_934_, v_i_935_);
lean_dec(v_i_935_);
lean_dec_ref(v_bytes_934_);
v_r_937_ = lean_box_uint32(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar(lean_object* v_bytes_938_, lean_object* v_i_939_, lean_object* v_h_940_){
_start:
{
lean_object* v___x_941_; uint8_t v___x_942_; uint8_t v___x_943_; uint8_t v___x_944_; uint8_t v___x_945_; uint8_t v___x_946_; uint8_t v___x_947_; 
v___x_941_ = lean_byte_array_size(v_bytes_938_);
v___x_942_ = lean_nat_dec_lt(v_i_939_, v___x_941_);
v___x_943_ = lean_byte_array_fget(v_bytes_938_, v_i_939_);
v___x_944_ = 128;
v___x_945_ = lean_uint8_land(v___x_943_, v___x_944_);
v___x_946_ = 0;
v___x_947_ = lean_uint8_dec_eq(v___x_945_, v___x_946_);
if (v___x_947_ == 0)
{
uint8_t v___x_948_; uint8_t v___x_949_; uint8_t v___x_950_; uint8_t v___x_951_; 
v___x_948_ = 224;
v___x_949_ = lean_uint8_land(v___x_943_, v___x_948_);
v___x_950_ = 192;
v___x_951_ = lean_uint8_dec_eq(v___x_949_, v___x_950_);
if (v___x_951_ == 0)
{
uint8_t v___x_952_; uint8_t v___x_953_; uint8_t v___x_954_; 
v___x_952_ = 240;
v___x_953_ = lean_uint8_land(v___x_943_, v___x_952_);
v___x_954_ = lean_uint8_dec_eq(v___x_953_, v___x_948_);
if (v___x_954_ == 0)
{
uint8_t v___x_955_; uint8_t v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; uint8_t v___x_964_; uint8_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; uint8_t v___x_969_; uint8_t v___x_970_; uint8_t v___x_971_; uint8_t v___x_972_; uint8_t v___x_973_; uint8_t v___x_974_; uint8_t v_b_u2080_975_; uint8_t v___x_976_; uint8_t v_b_u2081_977_; uint8_t v_b_u2082_978_; uint8_t v_b_u2083_979_; uint32_t v___x_980_; uint32_t v___x_981_; uint32_t v___x_982_; uint32_t v___x_983_; uint32_t v___x_984_; uint32_t v___x_985_; uint32_t v___x_986_; uint32_t v___x_987_; uint32_t v___x_988_; uint32_t v___x_989_; uint32_t v___x_990_; uint32_t v___x_991_; uint32_t v_r_992_; uint32_t v___x_993_; uint8_t v___x_994_; uint32_t v___x_995_; uint8_t v___x_996_; 
v___x_955_ = 248;
v___x_956_ = lean_uint8_land(v___x_943_, v___x_955_);
v___x_957_ = lean_uint8_dec_eq(v___x_956_, v___x_952_);
v___x_958_ = lean_unsigned_to_nat(3u);
v___x_959_ = lean_nat_add(v_i_939_, v___x_958_);
v___x_960_ = lean_nat_dec_lt(v___x_959_, v___x_941_);
v___x_961_ = lean_unsigned_to_nat(1u);
v___x_962_ = lean_nat_add(v_i_939_, v___x_961_);
v___x_963_ = lean_byte_array_fget(v_bytes_938_, v___x_962_);
lean_dec(v___x_962_);
v___x_964_ = lean_uint8_land(v___x_963_, v___x_950_);
v___x_965_ = lean_uint8_dec_eq(v___x_964_, v___x_944_);
v___x_966_ = lean_unsigned_to_nat(2u);
v___x_967_ = lean_nat_add(v_i_939_, v___x_966_);
v___x_968_ = lean_byte_array_fget(v_bytes_938_, v___x_967_);
lean_dec(v___x_967_);
v___x_969_ = lean_uint8_land(v___x_968_, v___x_950_);
v___x_970_ = lean_uint8_dec_eq(v___x_969_, v___x_944_);
v___x_971_ = lean_byte_array_fget(v_bytes_938_, v___x_959_);
lean_dec(v___x_959_);
v___x_972_ = lean_uint8_land(v___x_971_, v___x_950_);
v___x_973_ = lean_uint8_dec_eq(v___x_972_, v___x_944_);
v___x_974_ = 7;
v_b_u2080_975_ = lean_uint8_land(v___x_943_, v___x_974_);
v___x_976_ = 63;
v_b_u2081_977_ = lean_uint8_land(v___x_963_, v___x_976_);
v_b_u2082_978_ = lean_uint8_land(v___x_968_, v___x_976_);
v_b_u2083_979_ = lean_uint8_land(v___x_971_, v___x_976_);
v___x_980_ = lean_uint8_to_uint32(v_b_u2080_975_);
v___x_981_ = 18;
v___x_982_ = lean_uint32_shift_left(v___x_980_, v___x_981_);
v___x_983_ = lean_uint8_to_uint32(v_b_u2081_977_);
v___x_984_ = 12;
v___x_985_ = lean_uint32_shift_left(v___x_983_, v___x_984_);
v___x_986_ = lean_uint32_lor(v___x_982_, v___x_985_);
v___x_987_ = lean_uint8_to_uint32(v_b_u2082_978_);
v___x_988_ = 6;
v___x_989_ = lean_uint32_shift_left(v___x_987_, v___x_988_);
v___x_990_ = lean_uint32_lor(v___x_986_, v___x_989_);
v___x_991_ = lean_uint8_to_uint32(v_b_u2083_979_);
v_r_992_ = lean_uint32_lor(v___x_990_, v___x_991_);
v___x_993_ = 65536;
v___x_994_ = lean_uint32_dec_lt(v_r_992_, v___x_993_);
v___x_995_ = 1114111;
v___x_996_ = lean_uint32_dec_lt(v___x_995_, v_r_992_);
return v_r_992_;
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; uint8_t v___x_1003_; uint8_t v___x_1004_; uint8_t v___x_1005_; uint8_t v___x_1006_; uint8_t v___x_1007_; uint8_t v___x_1008_; uint8_t v_b_u2080_1009_; uint8_t v___x_1010_; uint8_t v_b_u2081_1011_; uint8_t v_b_u2082_1012_; uint32_t v___x_1013_; uint32_t v___x_1014_; uint32_t v___x_1015_; uint32_t v___x_1016_; uint32_t v___x_1017_; uint32_t v___x_1018_; uint32_t v___x_1019_; uint32_t v___x_1020_; uint32_t v_r_1021_; uint32_t v___x_1022_; uint8_t v___x_1023_; uint32_t v___x_1024_; uint8_t v___x_1025_; 
v___x_997_ = lean_unsigned_to_nat(2u);
v___x_998_ = lean_nat_add(v_i_939_, v___x_997_);
v___x_999_ = lean_nat_dec_lt(v___x_998_, v___x_941_);
v___x_1000_ = lean_unsigned_to_nat(1u);
v___x_1001_ = lean_nat_add(v_i_939_, v___x_1000_);
v___x_1002_ = lean_byte_array_fget(v_bytes_938_, v___x_1001_);
lean_dec(v___x_1001_);
v___x_1003_ = lean_uint8_land(v___x_1002_, v___x_950_);
v___x_1004_ = lean_uint8_dec_eq(v___x_1003_, v___x_944_);
v___x_1005_ = lean_byte_array_fget(v_bytes_938_, v___x_998_);
lean_dec(v___x_998_);
v___x_1006_ = lean_uint8_land(v___x_1005_, v___x_950_);
v___x_1007_ = lean_uint8_dec_eq(v___x_1006_, v___x_944_);
v___x_1008_ = 15;
v_b_u2080_1009_ = lean_uint8_land(v___x_943_, v___x_1008_);
v___x_1010_ = 63;
v_b_u2081_1011_ = lean_uint8_land(v___x_1002_, v___x_1010_);
v_b_u2082_1012_ = lean_uint8_land(v___x_1005_, v___x_1010_);
v___x_1013_ = lean_uint8_to_uint32(v_b_u2080_1009_);
v___x_1014_ = 12;
v___x_1015_ = lean_uint32_shift_left(v___x_1013_, v___x_1014_);
v___x_1016_ = lean_uint8_to_uint32(v_b_u2081_1011_);
v___x_1017_ = 6;
v___x_1018_ = lean_uint32_shift_left(v___x_1016_, v___x_1017_);
v___x_1019_ = lean_uint32_lor(v___x_1015_, v___x_1018_);
v___x_1020_ = lean_uint8_to_uint32(v_b_u2082_1012_);
v_r_1021_ = lean_uint32_lor(v___x_1019_, v___x_1020_);
v___x_1022_ = 2048;
v___x_1023_ = lean_uint32_dec_lt(v_r_1021_, v___x_1022_);
v___x_1024_ = 55296;
v___x_1025_ = lean_uint32_dec_le(v___x_1024_, v_r_1021_);
if (v___x_1025_ == 0)
{
return v_r_1021_;
}
else
{
uint32_t v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = 57343;
v___x_1027_ = lean_uint32_dec_le(v_r_1021_, v___x_1026_);
return v_r_1021_;
}
}
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; uint8_t v___x_1031_; uint8_t v___x_1032_; uint8_t v___x_1033_; uint8_t v___x_1034_; uint8_t v_b_u2080_1035_; uint8_t v___x_1036_; uint8_t v_b_u2081_1037_; uint32_t v___x_1038_; uint32_t v___x_1039_; uint32_t v___x_1040_; uint32_t v___x_1041_; uint32_t v_r_1042_; uint32_t v___x_1043_; uint8_t v___x_1044_; 
v___x_1028_ = lean_unsigned_to_nat(1u);
v___x_1029_ = lean_nat_add(v_i_939_, v___x_1028_);
v___x_1030_ = lean_nat_dec_lt(v___x_1029_, v___x_941_);
v___x_1031_ = lean_byte_array_fget(v_bytes_938_, v___x_1029_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_uint8_land(v___x_1031_, v___x_950_);
v___x_1033_ = lean_uint8_dec_eq(v___x_1032_, v___x_944_);
v___x_1034_ = 31;
v_b_u2080_1035_ = lean_uint8_land(v___x_943_, v___x_1034_);
v___x_1036_ = 63;
v_b_u2081_1037_ = lean_uint8_land(v___x_1031_, v___x_1036_);
v___x_1038_ = lean_uint8_to_uint32(v_b_u2080_1035_);
v___x_1039_ = 6;
v___x_1040_ = lean_uint32_shift_left(v___x_1038_, v___x_1039_);
v___x_1041_ = lean_uint8_to_uint32(v_b_u2081_1037_);
v_r_1042_ = lean_uint32_lor(v___x_1040_, v___x_1041_);
v___x_1043_ = 128;
v___x_1044_ = lean_uint32_dec_lt(v_r_1042_, v___x_1043_);
return v_r_1042_;
}
}
else
{
uint32_t v___x_1045_; 
v___x_1045_ = lean_uint8_to_uint32(v___x_943_);
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___boxed(lean_object* v_bytes_1046_, lean_object* v_i_1047_, lean_object* v_h_1048_){
_start:
{
uint32_t v_res_1049_; lean_object* v_r_1050_; 
v_res_1049_ = l_ByteArray_utf8DecodeChar(v_bytes_1046_, v_i_1047_, v_h_1048_);
lean_dec(v_i_1047_);
lean_dec_ref(v_bytes_1046_);
v_r_1050_ = lean_box_uint32(v_res_1049_);
return v_r_1050_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableIsUTF8FirstByte___aux__1(uint8_t v_c_1051_){
_start:
{
uint8_t v___x_1052_; uint8_t v___x_1053_; uint8_t v___x_1054_; uint8_t v___x_1055_; 
v___x_1052_ = 128;
v___x_1053_ = lean_uint8_land(v_c_1051_, v___x_1052_);
v___x_1054_ = 0;
v___x_1055_ = lean_uint8_dec_eq(v___x_1053_, v___x_1054_);
if (v___x_1055_ == 0)
{
uint8_t v___x_1056_; uint8_t v___x_1057_; uint8_t v___x_1058_; uint8_t v___x_1059_; 
v___x_1056_ = 224;
v___x_1057_ = lean_uint8_land(v_c_1051_, v___x_1056_);
v___x_1058_ = 192;
v___x_1059_ = lean_uint8_dec_eq(v___x_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
uint8_t v___x_1060_; uint8_t v___x_1061_; uint8_t v___x_1062_; 
v___x_1060_ = 240;
v___x_1061_ = lean_uint8_land(v_c_1051_, v___x_1060_);
v___x_1062_ = lean_uint8_dec_eq(v___x_1061_, v___x_1056_);
if (v___x_1062_ == 0)
{
uint8_t v___x_1063_; uint8_t v___x_1064_; uint8_t v___x_1065_; 
v___x_1063_ = 248;
v___x_1064_ = lean_uint8_land(v_c_1051_, v___x_1063_);
v___x_1065_ = lean_uint8_dec_eq(v___x_1064_, v___x_1060_);
return v___x_1065_;
}
else
{
return v___x_1062_;
}
}
else
{
return v___x_1059_;
}
}
else
{
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableIsUTF8FirstByte___aux__1___boxed(lean_object* v_c_1066_){
_start:
{
uint8_t v_c_boxed_1067_; uint8_t v_res_1068_; lean_object* v_r_1069_; 
v_c_boxed_1067_ = lean_unbox(v_c_1066_);
v_res_1068_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v_c_boxed_1067_);
v_r_1069_ = lean_box(v_res_1068_);
return v_r_1069_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableIsUTF8FirstByte(uint8_t v___y_1070_){
_start:
{
uint8_t v___x_1071_; 
v___x_1071_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v___y_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableIsUTF8FirstByte___boxed(lean_object* v___y_1072_){
_start:
{
uint8_t v___y_4__boxed_1073_; uint8_t v_res_1074_; lean_object* v_r_1075_; 
v___y_4__boxed_1073_ = lean_unbox(v___y_1072_);
v_res_1074_ = l_UInt8_instDecidableIsUTF8FirstByte(v___y_4__boxed_1073_);
v_r_1075_ = lean_box(v_res_1074_);
return v_r_1075_;
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg(uint8_t v_c_1076_){
_start:
{
uint8_t v___x_1077_; uint8_t v___x_1078_; uint8_t v___x_1079_; uint8_t v___x_1080_; 
v___x_1077_ = 128;
v___x_1078_ = lean_uint8_land(v_c_1076_, v___x_1077_);
v___x_1079_ = 0;
v___x_1080_ = lean_uint8_dec_eq(v___x_1078_, v___x_1079_);
if (v___x_1080_ == 0)
{
uint8_t v___x_1081_; uint8_t v___x_1082_; uint8_t v___x_1083_; uint8_t v___x_1084_; 
v___x_1081_ = 224;
v___x_1082_ = lean_uint8_land(v_c_1076_, v___x_1081_);
v___x_1083_ = 192;
v___x_1084_ = lean_uint8_dec_eq(v___x_1082_, v___x_1083_);
if (v___x_1084_ == 0)
{
uint8_t v___x_1085_; uint8_t v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = 240;
v___x_1086_ = lean_uint8_land(v_c_1076_, v___x_1085_);
v___x_1087_ = lean_uint8_dec_eq(v___x_1086_, v___x_1081_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_unsigned_to_nat(4u);
return v___x_1088_;
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_unsigned_to_nat(3u);
return v___x_1089_;
}
}
else
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_unsigned_to_nat(2u);
return v___x_1090_;
}
}
else
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_unsigned_to_nat(1u);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg___boxed(lean_object* v_c_1092_){
_start:
{
uint8_t v_c_boxed_1093_; lean_object* v_res_1094_; 
v_c_boxed_1093_ = lean_unbox(v_c_1092_);
v_res_1094_ = l_UInt8_utf8ByteSize___redArg(v_c_boxed_1093_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize(uint8_t v_c_1095_, lean_object* v___h_1096_){
_start:
{
uint8_t v___x_1097_; uint8_t v___x_1098_; uint8_t v___x_1099_; uint8_t v___x_1100_; 
v___x_1097_ = 128;
v___x_1098_ = lean_uint8_land(v_c_1095_, v___x_1097_);
v___x_1099_ = 0;
v___x_1100_ = lean_uint8_dec_eq(v___x_1098_, v___x_1099_);
if (v___x_1100_ == 0)
{
uint8_t v___x_1101_; uint8_t v___x_1102_; uint8_t v___x_1103_; uint8_t v___x_1104_; 
v___x_1101_ = 224;
v___x_1102_ = lean_uint8_land(v_c_1095_, v___x_1101_);
v___x_1103_ = 192;
v___x_1104_ = lean_uint8_dec_eq(v___x_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
uint8_t v___x_1105_; uint8_t v___x_1106_; uint8_t v___x_1107_; 
v___x_1105_ = 240;
v___x_1106_ = lean_uint8_land(v_c_1095_, v___x_1105_);
v___x_1107_ = lean_uint8_dec_eq(v___x_1106_, v___x_1101_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_unsigned_to_nat(4u);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_unsigned_to_nat(3u);
return v___x_1109_;
}
}
else
{
lean_object* v___x_1110_; 
v___x_1110_ = lean_unsigned_to_nat(2u);
return v___x_1110_;
}
}
else
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_unsigned_to_nat(1u);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___boxed(lean_object* v_c_1112_, lean_object* v___h_1113_){
_start:
{
uint8_t v_c_boxed_1114_; lean_object* v_res_1115_; 
v_c_boxed_1114_ = lean_unbox(v_c_1112_);
v_res_1115_ = l_UInt8_utf8ByteSize(v_c_boxed_1114_, v___h_1113_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(uint8_t v_x_1116_){
_start:
{
switch(v_x_1116_)
{
case 0:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_unsigned_to_nat(0u);
return v___x_1117_;
}
case 1:
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_unsigned_to_nat(1u);
return v___x_1118_;
}
case 2:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_unsigned_to_nat(2u);
return v___x_1119_;
}
case 3:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_unsigned_to_nat(3u);
return v___x_1120_;
}
default: 
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_unsigned_to_nat(4u);
return v___x_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize___boxed(lean_object* v_x_1122_){
_start:
{
uint8_t v_x_54__boxed_1123_; lean_object* v_res_1124_; 
v_x_54__boxed_1123_ = lean_unbox(v_x_1122_);
v_res_1124_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(v_x_54__boxed_1123_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(uint8_t v_x_1125_, lean_object* v_h__1_1126_, lean_object* v_h__2_1127_, lean_object* v_h__3_1128_, lean_object* v_h__4_1129_, lean_object* v_h__5_1130_){
_start:
{
switch(v_x_1125_)
{
case 0:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec(v_h__5_1130_);
lean_dec(v_h__4_1129_);
lean_dec(v_h__3_1128_);
lean_dec(v_h__2_1127_);
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_apply_1(v_h__1_1126_, v___x_1131_);
return v___x_1132_;
}
case 1:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v_h__5_1130_);
lean_dec(v_h__4_1129_);
lean_dec(v_h__3_1128_);
lean_dec(v_h__1_1126_);
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_apply_1(v_h__2_1127_, v___x_1133_);
return v___x_1134_;
}
case 2:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec(v_h__5_1130_);
lean_dec(v_h__4_1129_);
lean_dec(v_h__2_1127_);
lean_dec(v_h__1_1126_);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_apply_1(v_h__3_1128_, v___x_1135_);
return v___x_1136_;
}
case 3:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec(v_h__5_1130_);
lean_dec(v_h__3_1128_);
lean_dec(v_h__2_1127_);
lean_dec(v_h__1_1126_);
v___x_1137_ = lean_box(0);
v___x_1138_ = lean_apply_1(v_h__4_1129_, v___x_1137_);
return v___x_1138_;
}
default: 
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec(v_h__4_1129_);
lean_dec(v_h__3_1128_);
lean_dec(v_h__2_1127_);
lean_dec(v_h__1_1126_);
v___x_1139_ = lean_box(0);
v___x_1140_ = lean_apply_1(v_h__5_1130_, v___x_1139_);
return v___x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg___boxed(lean_object* v_x_1141_, lean_object* v_h__1_1142_, lean_object* v_h__2_1143_, lean_object* v_h__3_1144_, lean_object* v_h__4_1145_, lean_object* v_h__5_1146_){
_start:
{
uint8_t v_x_51__boxed_1147_; lean_object* v_res_1148_; 
v_x_51__boxed_1147_ = lean_unbox(v_x_1141_);
v_res_1148_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(v_x_51__boxed_1147_, v_h__1_1142_, v_h__2_1143_, v_h__3_1144_, v_h__4_1145_, v_h__5_1146_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(lean_object* v_motive_1149_, uint8_t v_x_1150_, lean_object* v_h__1_1151_, lean_object* v_h__2_1152_, lean_object* v_h__3_1153_, lean_object* v_h__4_1154_, lean_object* v_h__5_1155_){
_start:
{
switch(v_x_1150_)
{
case 0:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec(v_h__5_1155_);
lean_dec(v_h__4_1154_);
lean_dec(v_h__3_1153_);
lean_dec(v_h__2_1152_);
v___x_1156_ = lean_box(0);
v___x_1157_ = lean_apply_1(v_h__1_1151_, v___x_1156_);
return v___x_1157_;
}
case 1:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_dec(v_h__5_1155_);
lean_dec(v_h__4_1154_);
lean_dec(v_h__3_1153_);
lean_dec(v_h__1_1151_);
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_apply_1(v_h__2_1152_, v___x_1158_);
return v___x_1159_;
}
case 2:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v_h__5_1155_);
lean_dec(v_h__4_1154_);
lean_dec(v_h__2_1152_);
lean_dec(v_h__1_1151_);
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_apply_1(v_h__3_1153_, v___x_1160_);
return v___x_1161_;
}
case 3:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_dec(v_h__5_1155_);
lean_dec(v_h__3_1153_);
lean_dec(v_h__2_1152_);
lean_dec(v_h__1_1151_);
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_apply_1(v_h__4_1154_, v___x_1162_);
return v___x_1163_;
}
default: 
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec(v_h__4_1154_);
lean_dec(v_h__3_1153_);
lean_dec(v_h__2_1152_);
lean_dec(v_h__1_1151_);
v___x_1164_ = lean_box(0);
v___x_1165_ = lean_apply_1(v_h__5_1155_, v___x_1164_);
return v___x_1165_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___boxed(lean_object* v_motive_1166_, lean_object* v_x_1167_, lean_object* v_h__1_1168_, lean_object* v_h__2_1169_, lean_object* v_h__3_1170_, lean_object* v_h__4_1171_, lean_object* v_h__5_1172_){
_start:
{
uint8_t v_x_74__boxed_1173_; lean_object* v_res_1174_; 
v_x_74__boxed_1173_ = lean_unbox(v_x_1167_);
v_res_1174_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(v_motive_1166_, v_x_74__boxed_1173_, v_h__1_1168_, v_h__2_1169_, v_h__3_1170_, v_h__4_1171_, v_h__5_1172_);
return v_res_1174_;
}
}
lean_object* runtime_initialize_Init_Data_Char_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Bitwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Decode(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
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

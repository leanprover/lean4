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
uint8_t v___x_340_; uint8_t v_b_u2080_341_; uint8_t v___x_342_; uint8_t v_b_u2081_343_; uint8_t v_b_u2082_344_; uint32_t v___x_345_; uint32_t v___x_346_; uint32_t v___x_347_; uint32_t v___x_348_; uint32_t v___x_349_; uint32_t v___x_350_; uint32_t v___x_351_; uint32_t v___x_352_; uint32_t v_r_353_; uint8_t v___y_355_; uint32_t v___x_359_; uint8_t v___x_360_; 
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
v___x_359_ = 2048;
v___x_360_ = lean_uint32_dec_lt(v_r_353_, v___x_359_);
if (v___x_360_ == 0)
{
uint32_t v___x_361_; uint8_t v___x_362_; 
v___x_361_ = 55296;
v___x_362_ = lean_uint32_dec_le(v___x_361_, v_r_353_);
if (v___x_362_ == 0)
{
v___y_355_ = v___x_362_;
goto v___jp_354_;
}
else
{
uint32_t v___x_363_; uint8_t v___x_364_; 
v___x_363_ = 57343;
v___x_364_ = lean_uint32_dec_le(v_r_353_, v___x_363_);
v___y_355_ = v___x_364_;
goto v___jp_354_;
}
}
else
{
lean_object* v___x_365_; 
v___x_365_ = lean_box(0);
return v___x_365_;
}
v___jp_354_:
{
if (v___y_355_ == 0)
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_box_uint32(v_r_353_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; 
v___x_358_ = lean_box(0);
return v___x_358_;
}
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
uint8_t v___x_382_; uint8_t v_b_u2080_383_; uint8_t v___x_384_; uint8_t v_b_u2081_385_; uint8_t v_b_u2082_386_; uint32_t v___x_387_; uint32_t v___x_388_; uint32_t v___x_389_; uint32_t v___x_390_; uint32_t v___x_391_; uint32_t v___x_392_; uint32_t v___x_393_; uint32_t v___x_394_; uint32_t v_r_395_; uint32_t v___x_396_; uint8_t v___x_397_; uint32_t v___x_398_; uint8_t v___x_399_; 
v___x_382_ = 15;
v_b_u2080_383_ = lean_uint8_land(v_w_373_, v___x_382_);
v___x_384_ = 63;
v_b_u2081_385_ = lean_uint8_land(v_x_374_, v___x_384_);
v_b_u2082_386_ = lean_uint8_land(v_y_375_, v___x_384_);
v___x_387_ = lean_uint8_to_uint32(v_b_u2080_383_);
v___x_388_ = 12;
v___x_389_ = lean_uint32_shift_left(v___x_387_, v___x_388_);
v___x_390_ = lean_uint8_to_uint32(v_b_u2081_385_);
v___x_391_ = 6;
v___x_392_ = lean_uint32_shift_left(v___x_390_, v___x_391_);
v___x_393_ = lean_uint32_lor(v___x_389_, v___x_392_);
v___x_394_ = lean_uint8_to_uint32(v_b_u2082_386_);
v_r_395_ = lean_uint32_lor(v___x_393_, v___x_394_);
v___x_396_ = 2048;
v___x_397_ = lean_uint32_dec_le(v___x_396_, v_r_395_);
v___x_398_ = 55296;
v___x_399_ = lean_uint32_dec_lt(v_r_395_, v___x_398_);
if (v___x_399_ == 0)
{
if (v___x_397_ == 0)
{
return v___x_397_;
}
else
{
uint32_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 57343;
v___x_401_ = lean_uint32_dec_lt(v___x_400_, v_r_395_);
return v___x_401_;
}
}
else
{
if (v___x_397_ == 0)
{
return v___x_397_;
}
else
{
return v___x_399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2083___boxed(lean_object* v_w_402_, lean_object* v_x_403_, lean_object* v_y_404_){
_start:
{
uint8_t v_w_boxed_405_; uint8_t v_x_boxed_406_; uint8_t v_y_boxed_407_; uint8_t v_res_408_; lean_object* v_r_409_; 
v_w_boxed_405_ = lean_unbox(v_w_402_);
v_x_boxed_406_ = lean_unbox(v_x_403_);
v_y_boxed_407_ = lean_unbox(v_y_404_);
v_res_408_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2083(v_w_boxed_405_, v_x_boxed_406_, v_y_boxed_407_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(uint8_t v_w_410_, uint8_t v_x_411_, uint8_t v_y_412_, uint8_t v_z_413_){
_start:
{
uint8_t v___x_414_; uint8_t v_b_u2080_415_; uint8_t v___x_416_; uint8_t v_b_u2081_417_; uint8_t v_b_u2082_418_; uint8_t v_b_u2083_419_; uint32_t v___x_420_; uint32_t v___x_421_; uint32_t v___x_422_; uint32_t v___x_423_; uint32_t v___x_424_; uint32_t v___x_425_; uint32_t v___x_426_; uint32_t v___x_427_; uint32_t v___x_428_; uint32_t v___x_429_; uint32_t v___x_430_; uint32_t v___x_431_; uint32_t v___x_432_; 
v___x_414_ = 7;
v_b_u2080_415_ = lean_uint8_land(v_w_410_, v___x_414_);
v___x_416_ = 63;
v_b_u2081_417_ = lean_uint8_land(v_x_411_, v___x_416_);
v_b_u2082_418_ = lean_uint8_land(v_y_412_, v___x_416_);
v_b_u2083_419_ = lean_uint8_land(v_z_413_, v___x_416_);
v___x_420_ = lean_uint8_to_uint32(v_b_u2080_415_);
v___x_421_ = 18;
v___x_422_ = lean_uint32_shift_left(v___x_420_, v___x_421_);
v___x_423_ = lean_uint8_to_uint32(v_b_u2081_417_);
v___x_424_ = 12;
v___x_425_ = lean_uint32_shift_left(v___x_423_, v___x_424_);
v___x_426_ = lean_uint32_lor(v___x_422_, v___x_425_);
v___x_427_ = lean_uint8_to_uint32(v_b_u2082_418_);
v___x_428_ = 6;
v___x_429_ = lean_uint32_shift_left(v___x_427_, v___x_428_);
v___x_430_ = lean_uint32_lor(v___x_426_, v___x_429_);
v___x_431_ = lean_uint8_to_uint32(v_b_u2083_419_);
v___x_432_ = lean_uint32_lor(v___x_430_, v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked___boxed(lean_object* v_w_433_, lean_object* v_x_434_, lean_object* v_y_435_, lean_object* v_z_436_){
_start:
{
uint8_t v_w_boxed_437_; uint8_t v_x_boxed_438_; uint8_t v_y_boxed_439_; uint8_t v_z_boxed_440_; uint32_t v_res_441_; lean_object* v_r_442_; 
v_w_boxed_437_ = lean_unbox(v_w_433_);
v_x_boxed_438_ = lean_unbox(v_x_434_);
v_y_boxed_439_ = lean_unbox(v_y_435_);
v_z_boxed_440_ = lean_unbox(v_z_436_);
v_res_441_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(v_w_boxed_437_, v_x_boxed_438_, v_y_boxed_439_, v_z_boxed_440_);
v_r_442_ = lean_box_uint32(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(uint8_t v_w_443_, uint8_t v_x_444_, uint8_t v_y_445_, uint8_t v_z_446_){
_start:
{
uint8_t v___x_447_; uint8_t v___x_448_; uint8_t v___x_449_; uint8_t v___x_450_; 
v___x_447_ = 192;
v___x_448_ = lean_uint8_land(v_x_444_, v___x_447_);
v___x_449_ = 128;
v___x_450_ = lean_uint8_dec_eq(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
v___x_451_ = lean_box(0);
return v___x_451_;
}
else
{
uint8_t v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_uint8_land(v_y_445_, v___x_447_);
v___x_453_ = lean_uint8_dec_eq(v___x_452_, v___x_449_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
v___x_454_ = lean_box(0);
return v___x_454_;
}
else
{
uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_uint8_land(v_z_446_, v___x_447_);
v___x_456_ = lean_uint8_dec_eq(v___x_455_, v___x_449_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
v___x_457_ = lean_box(0);
return v___x_457_;
}
else
{
uint8_t v___x_458_; uint8_t v_b_u2080_459_; uint8_t v___x_460_; uint8_t v_b_u2081_461_; uint8_t v_b_u2082_462_; uint8_t v_b_u2083_463_; uint32_t v___x_464_; uint32_t v___x_465_; uint32_t v___x_466_; uint32_t v___x_467_; uint32_t v___x_468_; uint32_t v___x_469_; uint32_t v___x_470_; uint32_t v___x_471_; uint32_t v___x_472_; uint32_t v___x_473_; uint32_t v___x_474_; uint32_t v___x_475_; uint32_t v_r_476_; uint32_t v___x_477_; uint8_t v___x_478_; 
v___x_458_ = 7;
v_b_u2080_459_ = lean_uint8_land(v_w_443_, v___x_458_);
v___x_460_ = 63;
v_b_u2081_461_ = lean_uint8_land(v_x_444_, v___x_460_);
v_b_u2082_462_ = lean_uint8_land(v_y_445_, v___x_460_);
v_b_u2083_463_ = lean_uint8_land(v_z_446_, v___x_460_);
v___x_464_ = lean_uint8_to_uint32(v_b_u2080_459_);
v___x_465_ = 18;
v___x_466_ = lean_uint32_shift_left(v___x_464_, v___x_465_);
v___x_467_ = lean_uint8_to_uint32(v_b_u2081_461_);
v___x_468_ = 12;
v___x_469_ = lean_uint32_shift_left(v___x_467_, v___x_468_);
v___x_470_ = lean_uint32_lor(v___x_466_, v___x_469_);
v___x_471_ = lean_uint8_to_uint32(v_b_u2082_462_);
v___x_472_ = 6;
v___x_473_ = lean_uint32_shift_left(v___x_471_, v___x_472_);
v___x_474_ = lean_uint32_lor(v___x_470_, v___x_473_);
v___x_475_ = lean_uint8_to_uint32(v_b_u2083_463_);
v_r_476_ = lean_uint32_lor(v___x_474_, v___x_475_);
v___x_477_ = 65536;
v___x_478_ = lean_uint32_dec_lt(v_r_476_, v___x_477_);
if (v___x_478_ == 0)
{
uint32_t v___x_479_; uint8_t v___x_480_; 
v___x_479_ = 1114111;
v___x_480_ = lean_uint32_dec_lt(v___x_479_, v_r_476_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_box_uint32(v_r_476_);
v___x_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; 
v___x_483_ = lean_box(0);
return v___x_483_;
}
}
else
{
lean_object* v___x_484_; 
v___x_484_ = lean_box(0);
return v___x_484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084___boxed(lean_object* v_w_485_, lean_object* v_x_486_, lean_object* v_y_487_, lean_object* v_z_488_){
_start:
{
uint8_t v_w_boxed_489_; uint8_t v_x_boxed_490_; uint8_t v_y_boxed_491_; uint8_t v_z_boxed_492_; lean_object* v_res_493_; 
v_w_boxed_489_ = lean_unbox(v_w_485_);
v_x_boxed_490_ = lean_unbox(v_x_486_);
v_y_boxed_491_ = lean_unbox(v_y_487_);
v_z_boxed_492_ = lean_unbox(v_z_488_);
v_res_493_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(v_w_boxed_489_, v_x_boxed_490_, v_y_boxed_491_, v_z_boxed_492_);
return v_res_493_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2084(uint8_t v_w_494_, uint8_t v_x_495_, uint8_t v_y_496_, uint8_t v_z_497_){
_start:
{
uint8_t v___x_498_; uint8_t v___x_499_; uint8_t v___x_500_; uint8_t v___x_501_; 
v___x_498_ = 192;
v___x_499_ = lean_uint8_land(v_x_495_, v___x_498_);
v___x_500_ = 128;
v___x_501_ = lean_uint8_dec_eq(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
return v___x_501_;
}
else
{
uint8_t v___x_502_; uint8_t v___x_503_; uint8_t v___x_504_; 
v___x_502_ = 0;
v___x_503_ = lean_uint8_land(v_y_496_, v___x_498_);
v___x_504_ = lean_uint8_dec_eq(v___x_503_, v___x_500_);
if (v___x_504_ == 0)
{
return v___x_502_;
}
else
{
uint8_t v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_uint8_land(v_z_497_, v___x_498_);
v___x_506_ = lean_uint8_dec_eq(v___x_505_, v___x_500_);
if (v___x_506_ == 0)
{
return v___x_502_;
}
else
{
uint8_t v___x_507_; uint8_t v_b_u2080_508_; uint8_t v___x_509_; uint8_t v_b_u2081_510_; uint8_t v_b_u2082_511_; uint8_t v_b_u2083_512_; uint32_t v___x_513_; uint32_t v___x_514_; uint32_t v___x_515_; uint32_t v___x_516_; uint32_t v___x_517_; uint32_t v___x_518_; uint32_t v___x_519_; uint32_t v___x_520_; uint32_t v___x_521_; uint32_t v___x_522_; uint32_t v___x_523_; uint32_t v___x_524_; uint32_t v_r_525_; uint32_t v___x_526_; uint8_t v___x_527_; 
v___x_507_ = 7;
v_b_u2080_508_ = lean_uint8_land(v_w_494_, v___x_507_);
v___x_509_ = 63;
v_b_u2081_510_ = lean_uint8_land(v_x_495_, v___x_509_);
v_b_u2082_511_ = lean_uint8_land(v_y_496_, v___x_509_);
v_b_u2083_512_ = lean_uint8_land(v_z_497_, v___x_509_);
v___x_513_ = lean_uint8_to_uint32(v_b_u2080_508_);
v___x_514_ = 18;
v___x_515_ = lean_uint32_shift_left(v___x_513_, v___x_514_);
v___x_516_ = lean_uint8_to_uint32(v_b_u2081_510_);
v___x_517_ = 12;
v___x_518_ = lean_uint32_shift_left(v___x_516_, v___x_517_);
v___x_519_ = lean_uint32_lor(v___x_515_, v___x_518_);
v___x_520_ = lean_uint8_to_uint32(v_b_u2082_511_);
v___x_521_ = 6;
v___x_522_ = lean_uint32_shift_left(v___x_520_, v___x_521_);
v___x_523_ = lean_uint32_lor(v___x_519_, v___x_522_);
v___x_524_ = lean_uint8_to_uint32(v_b_u2083_512_);
v_r_525_ = lean_uint32_lor(v___x_523_, v___x_524_);
v___x_526_ = 65536;
v___x_527_ = lean_uint32_dec_le(v___x_526_, v_r_525_);
if (v___x_527_ == 0)
{
return v___x_527_;
}
else
{
uint32_t v___x_528_; uint8_t v___x_529_; 
v___x_528_ = 1114111;
v___x_529_ = lean_uint32_dec_le(v_r_525_, v___x_528_);
return v___x_529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2084___boxed(lean_object* v_w_530_, lean_object* v_x_531_, lean_object* v_y_532_, lean_object* v_z_533_){
_start:
{
uint8_t v_w_boxed_534_; uint8_t v_x_boxed_535_; uint8_t v_y_boxed_536_; uint8_t v_z_boxed_537_; uint8_t v_res_538_; lean_object* v_r_539_; 
v_w_boxed_534_ = lean_unbox(v_w_530_);
v_x_boxed_535_ = lean_unbox(v_x_531_);
v_y_boxed_536_ = lean_unbox(v_y_532_);
v_z_boxed_537_ = lean_unbox(v_z_533_);
v_res_538_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2084(v_w_boxed_534_, v_x_boxed_535_, v_y_boxed_536_, v_z_boxed_537_);
v_r_539_ = lean_box(v_res_538_);
return v_r_539_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f(lean_object* v_bytes_540_, lean_object* v_i_541_){
_start:
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = lean_byte_array_size(v_bytes_540_);
v___x_543_ = lean_nat_dec_lt(v_i_541_, v___x_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; 
v___x_544_ = lean_box(0);
return v___x_544_;
}
else
{
uint8_t v___x_545_; uint8_t v___x_546_; uint8_t v___x_547_; uint8_t v___x_548_; uint8_t v___x_549_; 
v___x_545_ = lean_byte_array_fget(v_bytes_540_, v_i_541_);
v___x_546_ = 128;
v___x_547_ = lean_uint8_land(v___x_545_, v___x_546_);
v___x_548_ = 0;
v___x_549_ = lean_uint8_dec_eq(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
uint8_t v___x_550_; uint8_t v___x_551_; uint8_t v___x_552_; uint8_t v___x_553_; 
v___x_550_ = 224;
v___x_551_ = lean_uint8_land(v___x_545_, v___x_550_);
v___x_552_ = 192;
v___x_553_ = lean_uint8_dec_eq(v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
uint8_t v___x_554_; uint8_t v___x_555_; uint8_t v___x_556_; 
v___x_554_ = 240;
v___x_555_ = lean_uint8_land(v___x_545_, v___x_554_);
v___x_556_ = lean_uint8_dec_eq(v___x_555_, v___x_550_);
if (v___x_556_ == 0)
{
uint8_t v___x_557_; uint8_t v___x_558_; uint8_t v___x_559_; 
v___x_557_ = 248;
v___x_558_ = lean_uint8_land(v___x_545_, v___x_557_);
v___x_559_ = lean_uint8_dec_eq(v___x_558_, v___x_554_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_box(0);
return v___x_560_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_561_ = lean_unsigned_to_nat(3u);
v___x_562_ = lean_nat_add(v_i_541_, v___x_561_);
v___x_563_ = lean_nat_dec_lt(v___x_562_, v___x_542_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
lean_dec(v___x_562_);
v___x_564_ = lean_box(0);
return v___x_564_;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; uint8_t v___x_568_; uint8_t v___x_569_; 
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = lean_nat_add(v_i_541_, v___x_565_);
v___x_567_ = lean_byte_array_fget(v_bytes_540_, v___x_566_);
lean_dec(v___x_566_);
v___x_568_ = lean_uint8_land(v___x_567_, v___x_552_);
v___x_569_ = lean_uint8_dec_eq(v___x_568_, v___x_546_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
lean_dec(v___x_562_);
v___x_570_ = lean_box(0);
return v___x_570_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; uint8_t v___x_574_; uint8_t v___x_575_; 
v___x_571_ = lean_unsigned_to_nat(2u);
v___x_572_ = lean_nat_add(v_i_541_, v___x_571_);
v___x_573_ = lean_byte_array_fget(v_bytes_540_, v___x_572_);
lean_dec(v___x_572_);
v___x_574_ = lean_uint8_land(v___x_573_, v___x_552_);
v___x_575_ = lean_uint8_dec_eq(v___x_574_, v___x_546_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
lean_dec(v___x_562_);
v___x_576_ = lean_box(0);
return v___x_576_;
}
else
{
uint8_t v___x_577_; uint8_t v___x_578_; uint8_t v___x_579_; 
v___x_577_ = lean_byte_array_fget(v_bytes_540_, v___x_562_);
lean_dec(v___x_562_);
v___x_578_ = lean_uint8_land(v___x_577_, v___x_552_);
v___x_579_ = lean_uint8_dec_eq(v___x_578_, v___x_546_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_box(0);
return v___x_580_;
}
else
{
uint8_t v___x_581_; uint8_t v_b_u2080_582_; uint8_t v___x_583_; uint8_t v_b_u2081_584_; uint8_t v_b_u2082_585_; uint8_t v_b_u2083_586_; uint32_t v___x_587_; uint32_t v___x_588_; uint32_t v___x_589_; uint32_t v___x_590_; uint32_t v___x_591_; uint32_t v___x_592_; uint32_t v___x_593_; uint32_t v___x_594_; uint32_t v___x_595_; uint32_t v___x_596_; uint32_t v___x_597_; uint32_t v___x_598_; uint32_t v_r_599_; uint32_t v___x_600_; uint8_t v___x_601_; 
v___x_581_ = 7;
v_b_u2080_582_ = lean_uint8_land(v___x_545_, v___x_581_);
v___x_583_ = 63;
v_b_u2081_584_ = lean_uint8_land(v___x_567_, v___x_583_);
v_b_u2082_585_ = lean_uint8_land(v___x_573_, v___x_583_);
v_b_u2083_586_ = lean_uint8_land(v___x_577_, v___x_583_);
v___x_587_ = lean_uint8_to_uint32(v_b_u2080_582_);
v___x_588_ = 18;
v___x_589_ = lean_uint32_shift_left(v___x_587_, v___x_588_);
v___x_590_ = lean_uint8_to_uint32(v_b_u2081_584_);
v___x_591_ = 12;
v___x_592_ = lean_uint32_shift_left(v___x_590_, v___x_591_);
v___x_593_ = lean_uint32_lor(v___x_589_, v___x_592_);
v___x_594_ = lean_uint8_to_uint32(v_b_u2082_585_);
v___x_595_ = 6;
v___x_596_ = lean_uint32_shift_left(v___x_594_, v___x_595_);
v___x_597_ = lean_uint32_lor(v___x_593_, v___x_596_);
v___x_598_ = lean_uint8_to_uint32(v_b_u2083_586_);
v_r_599_ = lean_uint32_lor(v___x_597_, v___x_598_);
v___x_600_ = 65536;
v___x_601_ = lean_uint32_dec_lt(v_r_599_, v___x_600_);
if (v___x_601_ == 0)
{
uint32_t v___x_602_; uint8_t v___x_603_; 
v___x_602_ = 1114111;
v___x_603_ = lean_uint32_dec_lt(v___x_602_, v_r_599_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_box_uint32(v_r_599_);
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
else
{
lean_object* v___x_606_; 
v___x_606_ = lean_box(0);
return v___x_606_;
}
}
else
{
lean_object* v___x_607_; 
v___x_607_ = lean_box(0);
return v___x_607_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_608_ = lean_unsigned_to_nat(2u);
v___x_609_ = lean_nat_add(v_i_541_, v___x_608_);
v___x_610_ = lean_nat_dec_lt(v___x_609_, v___x_542_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; 
lean_dec(v___x_609_);
v___x_611_ = lean_box(0);
return v___x_611_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; uint8_t v___x_615_; uint8_t v___x_616_; 
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = lean_nat_add(v_i_541_, v___x_612_);
v___x_614_ = lean_byte_array_fget(v_bytes_540_, v___x_613_);
lean_dec(v___x_613_);
v___x_615_ = lean_uint8_land(v___x_614_, v___x_552_);
v___x_616_ = lean_uint8_dec_eq(v___x_615_, v___x_546_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
lean_dec(v___x_609_);
v___x_617_ = lean_box(0);
return v___x_617_;
}
else
{
uint8_t v___x_618_; uint8_t v___x_619_; uint8_t v___x_620_; 
v___x_618_ = lean_byte_array_fget(v_bytes_540_, v___x_609_);
lean_dec(v___x_609_);
v___x_619_ = lean_uint8_land(v___x_618_, v___x_552_);
v___x_620_ = lean_uint8_dec_eq(v___x_619_, v___x_546_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
v___x_621_ = lean_box(0);
return v___x_621_;
}
else
{
uint8_t v___x_622_; uint8_t v_b_u2080_623_; uint8_t v___x_624_; uint8_t v_b_u2081_625_; uint8_t v_b_u2082_626_; uint32_t v___x_627_; uint32_t v___x_628_; uint32_t v___x_629_; uint32_t v___x_630_; uint32_t v___x_631_; uint32_t v___x_632_; uint32_t v___x_633_; uint32_t v___x_634_; uint32_t v_r_635_; uint8_t v___y_637_; uint32_t v___x_641_; uint8_t v___x_642_; 
v___x_622_ = 15;
v_b_u2080_623_ = lean_uint8_land(v___x_545_, v___x_622_);
v___x_624_ = 63;
v_b_u2081_625_ = lean_uint8_land(v___x_614_, v___x_624_);
v_b_u2082_626_ = lean_uint8_land(v___x_618_, v___x_624_);
v___x_627_ = lean_uint8_to_uint32(v_b_u2080_623_);
v___x_628_ = 12;
v___x_629_ = lean_uint32_shift_left(v___x_627_, v___x_628_);
v___x_630_ = lean_uint8_to_uint32(v_b_u2081_625_);
v___x_631_ = 6;
v___x_632_ = lean_uint32_shift_left(v___x_630_, v___x_631_);
v___x_633_ = lean_uint32_lor(v___x_629_, v___x_632_);
v___x_634_ = lean_uint8_to_uint32(v_b_u2082_626_);
v_r_635_ = lean_uint32_lor(v___x_633_, v___x_634_);
v___x_641_ = 2048;
v___x_642_ = lean_uint32_dec_lt(v_r_635_, v___x_641_);
if (v___x_642_ == 0)
{
uint32_t v___x_643_; uint8_t v___x_644_; 
v___x_643_ = 55296;
v___x_644_ = lean_uint32_dec_le(v___x_643_, v_r_635_);
if (v___x_644_ == 0)
{
v___y_637_ = v___x_644_;
goto v___jp_636_;
}
else
{
uint32_t v___x_645_; uint8_t v___x_646_; 
v___x_645_ = 57343;
v___x_646_ = lean_uint32_dec_le(v_r_635_, v___x_645_);
v___y_637_ = v___x_646_;
goto v___jp_636_;
}
}
else
{
lean_object* v___x_647_; 
v___x_647_ = lean_box(0);
return v___x_647_;
}
v___jp_636_:
{
if (v___y_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_box_uint32(v_r_635_);
v___x_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; 
v___x_640_ = lean_box(0);
return v___x_640_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_648_ = lean_unsigned_to_nat(1u);
v___x_649_ = lean_nat_add(v_i_541_, v___x_648_);
v___x_650_ = lean_nat_dec_lt(v___x_649_, v___x_542_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
lean_dec(v___x_649_);
v___x_651_ = lean_box(0);
return v___x_651_;
}
else
{
uint8_t v___x_652_; uint8_t v___x_653_; uint8_t v___x_654_; 
v___x_652_ = lean_byte_array_fget(v_bytes_540_, v___x_649_);
lean_dec(v___x_649_);
v___x_653_ = lean_uint8_land(v___x_652_, v___x_552_);
v___x_654_ = lean_uint8_dec_eq(v___x_653_, v___x_546_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_box(0);
return v___x_655_;
}
else
{
uint8_t v___x_656_; uint8_t v_b_u2080_657_; uint8_t v___x_658_; uint8_t v_b_u2081_659_; uint32_t v___x_660_; uint32_t v___x_661_; uint32_t v___x_662_; uint32_t v___x_663_; uint32_t v_r_664_; uint32_t v___x_665_; uint8_t v___x_666_; 
v___x_656_ = 31;
v_b_u2080_657_ = lean_uint8_land(v___x_545_, v___x_656_);
v___x_658_ = 63;
v_b_u2081_659_ = lean_uint8_land(v___x_652_, v___x_658_);
v___x_660_ = lean_uint8_to_uint32(v_b_u2080_657_);
v___x_661_ = 6;
v___x_662_ = lean_uint32_shift_left(v___x_660_, v___x_661_);
v___x_663_ = lean_uint8_to_uint32(v_b_u2081_659_);
v_r_664_ = lean_uint32_lor(v___x_662_, v___x_663_);
v___x_665_ = 128;
v___x_666_ = lean_uint32_dec_lt(v_r_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_box_uint32(v_r_664_);
v___x_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; 
v___x_669_ = lean_box(0);
return v___x_669_;
}
}
}
}
}
else
{
uint32_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = lean_uint8_to_uint32(v___x_545_);
v___x_671_ = lean_box_uint32(v___x_670_);
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f___boxed(lean_object* v_bytes_673_, lean_object* v_i_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_ByteArray_utf8DecodeChar_x3f(v_bytes_673_, v_i_674_);
lean_dec(v_i_674_);
lean_dec_ref(v_bytes_673_);
return v_res_675_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8At(lean_object* v_bytes_676_, lean_object* v_i_677_){
_start:
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = lean_byte_array_size(v_bytes_676_);
v___x_679_ = lean_nat_dec_lt(v_i_677_, v___x_678_);
if (v___x_679_ == 0)
{
return v___x_679_;
}
else
{
uint8_t v___x_680_; uint8_t v___x_681_; uint8_t v___x_682_; uint8_t v___x_683_; uint8_t v___x_684_; 
v___x_680_ = lean_byte_array_fget(v_bytes_676_, v_i_677_);
v___x_681_ = 128;
v___x_682_ = lean_uint8_land(v___x_680_, v___x_681_);
v___x_683_ = 0;
v___x_684_ = lean_uint8_dec_eq(v___x_682_, v___x_683_);
if (v___x_684_ == 0)
{
uint8_t v___x_685_; uint8_t v___x_686_; uint8_t v___x_687_; uint8_t v___x_688_; 
v___x_685_ = 224;
v___x_686_ = lean_uint8_land(v___x_680_, v___x_685_);
v___x_687_ = 192;
v___x_688_ = lean_uint8_dec_eq(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
uint8_t v___x_689_; uint8_t v___x_690_; uint8_t v___x_691_; 
v___x_689_ = 240;
v___x_690_ = lean_uint8_land(v___x_680_, v___x_689_);
v___x_691_ = lean_uint8_dec_eq(v___x_690_, v___x_685_);
if (v___x_691_ == 0)
{
uint8_t v___x_692_; uint8_t v___x_693_; uint8_t v___x_694_; 
v___x_692_ = 248;
v___x_693_ = lean_uint8_land(v___x_680_, v___x_692_);
v___x_694_ = lean_uint8_dec_eq(v___x_693_, v___x_689_);
if (v___x_694_ == 0)
{
return v___x_694_;
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_695_ = lean_unsigned_to_nat(3u);
v___x_696_ = lean_nat_add(v_i_677_, v___x_695_);
v___x_697_ = lean_nat_dec_lt(v___x_696_, v___x_678_);
if (v___x_697_ == 0)
{
lean_dec(v___x_696_);
return v___x_697_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; uint8_t v___x_701_; uint8_t v___x_702_; 
v___x_698_ = lean_unsigned_to_nat(1u);
v___x_699_ = lean_nat_add(v_i_677_, v___x_698_);
v___x_700_ = lean_byte_array_fget(v_bytes_676_, v___x_699_);
lean_dec(v___x_699_);
v___x_701_ = lean_uint8_land(v___x_700_, v___x_687_);
v___x_702_ = lean_uint8_dec_eq(v___x_701_, v___x_681_);
if (v___x_702_ == 0)
{
lean_dec(v___x_696_);
return v___x_702_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; uint8_t v___x_706_; uint8_t v___x_707_; 
v___x_703_ = lean_unsigned_to_nat(2u);
v___x_704_ = lean_nat_add(v_i_677_, v___x_703_);
v___x_705_ = lean_byte_array_fget(v_bytes_676_, v___x_704_);
lean_dec(v___x_704_);
v___x_706_ = lean_uint8_land(v___x_705_, v___x_687_);
v___x_707_ = lean_uint8_dec_eq(v___x_706_, v___x_681_);
if (v___x_707_ == 0)
{
lean_dec(v___x_696_);
return v___x_691_;
}
else
{
uint8_t v___x_708_; uint8_t v___x_709_; uint8_t v___x_710_; 
v___x_708_ = lean_byte_array_fget(v_bytes_676_, v___x_696_);
lean_dec(v___x_696_);
v___x_709_ = lean_uint8_land(v___x_708_, v___x_687_);
v___x_710_ = lean_uint8_dec_eq(v___x_709_, v___x_681_);
if (v___x_710_ == 0)
{
return v___x_691_;
}
else
{
uint8_t v___x_711_; uint8_t v_b_u2080_712_; uint8_t v___x_713_; uint8_t v_b_u2081_714_; uint8_t v_b_u2082_715_; uint8_t v_b_u2083_716_; uint32_t v___x_717_; uint32_t v___x_718_; uint32_t v___x_719_; uint32_t v___x_720_; uint32_t v___x_721_; uint32_t v___x_722_; uint32_t v___x_723_; uint32_t v___x_724_; uint32_t v___x_725_; uint32_t v___x_726_; uint32_t v___x_727_; uint32_t v___x_728_; uint32_t v_r_729_; uint32_t v___x_730_; uint8_t v___x_731_; 
v___x_711_ = 7;
v_b_u2080_712_ = lean_uint8_land(v___x_680_, v___x_711_);
v___x_713_ = 63;
v_b_u2081_714_ = lean_uint8_land(v___x_700_, v___x_713_);
v_b_u2082_715_ = lean_uint8_land(v___x_705_, v___x_713_);
v_b_u2083_716_ = lean_uint8_land(v___x_708_, v___x_713_);
v___x_717_ = lean_uint8_to_uint32(v_b_u2080_712_);
v___x_718_ = 18;
v___x_719_ = lean_uint32_shift_left(v___x_717_, v___x_718_);
v___x_720_ = lean_uint8_to_uint32(v_b_u2081_714_);
v___x_721_ = 12;
v___x_722_ = lean_uint32_shift_left(v___x_720_, v___x_721_);
v___x_723_ = lean_uint32_lor(v___x_719_, v___x_722_);
v___x_724_ = lean_uint8_to_uint32(v_b_u2082_715_);
v___x_725_ = 6;
v___x_726_ = lean_uint32_shift_left(v___x_724_, v___x_725_);
v___x_727_ = lean_uint32_lor(v___x_723_, v___x_726_);
v___x_728_ = lean_uint8_to_uint32(v_b_u2083_716_);
v_r_729_ = lean_uint32_lor(v___x_727_, v___x_728_);
v___x_730_ = 65536;
v___x_731_ = lean_uint32_dec_le(v___x_730_, v_r_729_);
if (v___x_731_ == 0)
{
return v___x_731_;
}
else
{
uint32_t v___x_732_; uint8_t v___x_733_; 
v___x_732_ = 1114111;
v___x_733_ = lean_uint32_dec_le(v_r_729_, v___x_732_);
return v___x_733_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_unsigned_to_nat(2u);
v___x_735_ = lean_nat_add(v_i_677_, v___x_734_);
v___x_736_ = lean_nat_dec_lt(v___x_735_, v___x_678_);
if (v___x_736_ == 0)
{
lean_dec(v___x_735_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; uint8_t v___x_740_; uint8_t v___x_741_; 
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_nat_add(v_i_677_, v___x_737_);
v___x_739_ = lean_byte_array_fget(v_bytes_676_, v___x_738_);
lean_dec(v___x_738_);
v___x_740_ = lean_uint8_land(v___x_739_, v___x_687_);
v___x_741_ = lean_uint8_dec_eq(v___x_740_, v___x_681_);
if (v___x_741_ == 0)
{
lean_dec(v___x_735_);
return v___x_741_;
}
else
{
uint8_t v___x_742_; uint8_t v___x_743_; uint8_t v___x_744_; 
v___x_742_ = lean_byte_array_fget(v_bytes_676_, v___x_735_);
lean_dec(v___x_735_);
v___x_743_ = lean_uint8_land(v___x_742_, v___x_687_);
v___x_744_ = lean_uint8_dec_eq(v___x_743_, v___x_681_);
if (v___x_744_ == 0)
{
return v___x_744_;
}
else
{
uint8_t v___x_745_; uint8_t v_b_u2080_746_; uint8_t v___x_747_; uint8_t v_b_u2081_748_; uint8_t v_b_u2082_749_; uint32_t v___x_750_; uint32_t v___x_751_; uint32_t v___x_752_; uint32_t v___x_753_; uint32_t v___x_754_; uint32_t v___x_755_; uint32_t v___x_756_; uint32_t v___x_757_; uint32_t v_r_758_; uint32_t v___x_759_; uint8_t v___x_760_; uint32_t v___x_761_; uint8_t v___x_762_; 
v___x_745_ = 15;
v_b_u2080_746_ = lean_uint8_land(v___x_680_, v___x_745_);
v___x_747_ = 63;
v_b_u2081_748_ = lean_uint8_land(v___x_739_, v___x_747_);
v_b_u2082_749_ = lean_uint8_land(v___x_742_, v___x_747_);
v___x_750_ = lean_uint8_to_uint32(v_b_u2080_746_);
v___x_751_ = 12;
v___x_752_ = lean_uint32_shift_left(v___x_750_, v___x_751_);
v___x_753_ = lean_uint8_to_uint32(v_b_u2081_748_);
v___x_754_ = 6;
v___x_755_ = lean_uint32_shift_left(v___x_753_, v___x_754_);
v___x_756_ = lean_uint32_lor(v___x_752_, v___x_755_);
v___x_757_ = lean_uint8_to_uint32(v_b_u2082_749_);
v_r_758_ = lean_uint32_lor(v___x_756_, v___x_757_);
v___x_759_ = 2048;
v___x_760_ = lean_uint32_dec_le(v___x_759_, v_r_758_);
v___x_761_ = 55296;
v___x_762_ = lean_uint32_dec_lt(v_r_758_, v___x_761_);
if (v___x_762_ == 0)
{
if (v___x_760_ == 0)
{
return v___x_760_;
}
else
{
uint32_t v___x_763_; uint8_t v___x_764_; 
v___x_763_ = 57343;
v___x_764_ = lean_uint32_dec_lt(v___x_763_, v_r_758_);
return v___x_764_;
}
}
else
{
if (v___x_760_ == 0)
{
return v___x_760_;
}
else
{
return v___x_762_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = lean_nat_add(v_i_677_, v___x_765_);
v___x_767_ = lean_nat_dec_lt(v___x_766_, v___x_678_);
if (v___x_767_ == 0)
{
lean_dec(v___x_766_);
return v___x_767_;
}
else
{
uint8_t v___x_768_; uint8_t v___x_769_; uint8_t v___x_770_; 
v___x_768_ = lean_byte_array_fget(v_bytes_676_, v___x_766_);
lean_dec(v___x_766_);
v___x_769_ = lean_uint8_land(v___x_768_, v___x_687_);
v___x_770_ = lean_uint8_dec_eq(v___x_769_, v___x_681_);
if (v___x_770_ == 0)
{
return v___x_770_;
}
else
{
uint8_t v___x_771_; uint8_t v_b_u2080_772_; uint8_t v___x_773_; uint8_t v_b_u2081_774_; uint32_t v___x_775_; uint32_t v___x_776_; uint32_t v___x_777_; uint32_t v___x_778_; uint32_t v_r_779_; uint32_t v___x_780_; uint8_t v___x_781_; 
v___x_771_ = 31;
v_b_u2080_772_ = lean_uint8_land(v___x_680_, v___x_771_);
v___x_773_ = 63;
v_b_u2081_774_ = lean_uint8_land(v___x_768_, v___x_773_);
v___x_775_ = lean_uint8_to_uint32(v_b_u2080_772_);
v___x_776_ = 6;
v___x_777_ = lean_uint32_shift_left(v___x_775_, v___x_776_);
v___x_778_ = lean_uint8_to_uint32(v_b_u2081_774_);
v_r_779_ = lean_uint32_lor(v___x_777_, v___x_778_);
v___x_780_ = 128;
v___x_781_ = lean_uint32_dec_le(v___x_780_, v_r_779_);
return v___x_781_;
}
}
}
}
else
{
return v___x_679_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8At___boxed(lean_object* v_bytes_782_, lean_object* v_i_783_){
_start:
{
uint8_t v_res_784_; lean_object* v_r_785_; 
v_res_784_ = l_ByteArray_validateUTF8At(v_bytes_782_, v_i_783_);
lean_dec(v_i_783_);
lean_dec_ref(v_bytes_782_);
v_r_785_ = lean_box(v_res_784_);
return v_r_785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t v_x_786_, lean_object* v_h__1_787_, lean_object* v_h__2_788_, lean_object* v_h__3_789_, lean_object* v_h__4_790_, lean_object* v_h__5_791_){
_start:
{
switch(v_x_786_)
{
case 0:
{
lean_object* v___x_792_; 
lean_dec(v_h__5_791_);
lean_dec(v_h__4_790_);
lean_dec(v_h__3_789_);
lean_dec(v_h__2_788_);
v___x_792_ = lean_apply_1(v_h__1_787_, lean_box(0));
return v___x_792_;
}
case 1:
{
lean_object* v___x_793_; 
lean_dec(v_h__5_791_);
lean_dec(v_h__4_790_);
lean_dec(v_h__3_789_);
lean_dec(v_h__1_787_);
v___x_793_ = lean_apply_1(v_h__2_788_, lean_box(0));
return v___x_793_;
}
case 2:
{
lean_object* v___x_794_; 
lean_dec(v_h__5_791_);
lean_dec(v_h__4_790_);
lean_dec(v_h__2_788_);
lean_dec(v_h__1_787_);
v___x_794_ = lean_apply_1(v_h__3_789_, lean_box(0));
return v___x_794_;
}
case 3:
{
lean_object* v___x_795_; 
lean_dec(v_h__5_791_);
lean_dec(v_h__3_789_);
lean_dec(v_h__2_788_);
lean_dec(v_h__1_787_);
v___x_795_ = lean_apply_1(v_h__4_790_, lean_box(0));
return v___x_795_;
}
default: 
{
lean_object* v___x_796_; 
lean_dec(v_h__4_790_);
lean_dec(v_h__3_789_);
lean_dec(v_h__2_788_);
lean_dec(v_h__1_787_);
v___x_796_ = lean_apply_1(v_h__5_791_, lean_box(0));
return v___x_796_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_797_, lean_object* v_h__1_798_, lean_object* v_h__2_799_, lean_object* v_h__3_800_, lean_object* v_h__4_801_, lean_object* v_h__5_802_){
_start:
{
uint8_t v_x_47__boxed_803_; lean_object* v_res_804_; 
v_x_47__boxed_803_ = lean_unbox(v_x_797_);
v_res_804_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(v_x_47__boxed_803_, v_h__1_798_, v_h__2_799_, v_h__3_800_, v_h__4_801_, v_h__5_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object* v_motive_805_, uint8_t v_x_806_, lean_object* v_h__1_807_, lean_object* v_h__2_808_, lean_object* v_h__3_809_, lean_object* v_h__4_810_, lean_object* v_h__5_811_){
_start:
{
switch(v_x_806_)
{
case 0:
{
lean_object* v___x_812_; 
lean_dec(v_h__5_811_);
lean_dec(v_h__4_810_);
lean_dec(v_h__3_809_);
lean_dec(v_h__2_808_);
v___x_812_ = lean_apply_1(v_h__1_807_, lean_box(0));
return v___x_812_;
}
case 1:
{
lean_object* v___x_813_; 
lean_dec(v_h__5_811_);
lean_dec(v_h__4_810_);
lean_dec(v_h__3_809_);
lean_dec(v_h__1_807_);
v___x_813_ = lean_apply_1(v_h__2_808_, lean_box(0));
return v___x_813_;
}
case 2:
{
lean_object* v___x_814_; 
lean_dec(v_h__5_811_);
lean_dec(v_h__4_810_);
lean_dec(v_h__2_808_);
lean_dec(v_h__1_807_);
v___x_814_ = lean_apply_1(v_h__3_809_, lean_box(0));
return v___x_814_;
}
case 3:
{
lean_object* v___x_815_; 
lean_dec(v_h__5_811_);
lean_dec(v_h__3_809_);
lean_dec(v_h__2_808_);
lean_dec(v_h__1_807_);
v___x_815_ = lean_apply_1(v_h__4_810_, lean_box(0));
return v___x_815_;
}
default: 
{
lean_object* v___x_816_; 
lean_dec(v_h__4_810_);
lean_dec(v_h__3_809_);
lean_dec(v_h__2_808_);
lean_dec(v_h__1_807_);
v___x_816_ = lean_apply_1(v_h__5_811_, lean_box(0));
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object* v_motive_817_, lean_object* v_x_818_, lean_object* v_h__1_819_, lean_object* v_h__2_820_, lean_object* v_h__3_821_, lean_object* v_h__4_822_, lean_object* v_h__5_823_){
_start:
{
uint8_t v_x_60__boxed_824_; lean_object* v_res_825_; 
v_x_60__boxed_824_ = lean_unbox(v_x_818_);
v_res_825_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(v_motive_817_, v_x_60__boxed_824_, v_h__1_819_, v_h__2_820_, v_h__3_821_, v_h__4_822_, v_h__5_823_);
return v_res_825_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar___redArg(lean_object* v_bytes_826_, lean_object* v_i_827_){
_start:
{
lean_object* v___x_828_; uint8_t v___x_829_; uint8_t v___x_830_; uint8_t v___x_831_; uint8_t v___x_832_; uint8_t v___x_833_; uint8_t v___x_834_; 
v___x_828_ = lean_byte_array_size(v_bytes_826_);
v___x_829_ = lean_nat_dec_lt(v_i_827_, v___x_828_);
v___x_830_ = lean_byte_array_fget(v_bytes_826_, v_i_827_);
v___x_831_ = 128;
v___x_832_ = lean_uint8_land(v___x_830_, v___x_831_);
v___x_833_ = 0;
v___x_834_ = lean_uint8_dec_eq(v___x_832_, v___x_833_);
if (v___x_834_ == 0)
{
uint8_t v___x_835_; uint8_t v___x_836_; uint8_t v___x_837_; uint8_t v___x_838_; 
v___x_835_ = 224;
v___x_836_ = lean_uint8_land(v___x_830_, v___x_835_);
v___x_837_ = 192;
v___x_838_ = lean_uint8_dec_eq(v___x_836_, v___x_837_);
if (v___x_838_ == 0)
{
uint8_t v___x_839_; uint8_t v___x_840_; uint8_t v___x_841_; 
v___x_839_ = 240;
v___x_840_ = lean_uint8_land(v___x_830_, v___x_839_);
v___x_841_ = lean_uint8_dec_eq(v___x_840_, v___x_835_);
if (v___x_841_ == 0)
{
uint8_t v___x_842_; uint8_t v___x_843_; uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; uint8_t v___x_851_; uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; uint8_t v___x_856_; uint8_t v___x_857_; uint8_t v___x_858_; uint8_t v___x_859_; uint8_t v___x_860_; uint8_t v___x_861_; uint8_t v_b_u2080_862_; uint8_t v___x_863_; uint8_t v_b_u2081_864_; uint8_t v_b_u2082_865_; uint8_t v_b_u2083_866_; uint32_t v___x_867_; uint32_t v___x_868_; uint32_t v___x_869_; uint32_t v___x_870_; uint32_t v___x_871_; uint32_t v___x_872_; uint32_t v___x_873_; uint32_t v___x_874_; uint32_t v___x_875_; uint32_t v___x_876_; uint32_t v___x_877_; uint32_t v___x_878_; uint32_t v_r_879_; uint32_t v___x_880_; uint8_t v___x_881_; uint32_t v___x_882_; uint8_t v___x_883_; 
v___x_842_ = 248;
v___x_843_ = lean_uint8_land(v___x_830_, v___x_842_);
v___x_844_ = lean_uint8_dec_eq(v___x_843_, v___x_839_);
v___x_845_ = lean_unsigned_to_nat(3u);
v___x_846_ = lean_nat_add(v_i_827_, v___x_845_);
v___x_847_ = lean_nat_dec_lt(v___x_846_, v___x_828_);
v___x_848_ = lean_unsigned_to_nat(1u);
v___x_849_ = lean_nat_add(v_i_827_, v___x_848_);
v___x_850_ = lean_byte_array_fget(v_bytes_826_, v___x_849_);
lean_dec(v___x_849_);
v___x_851_ = lean_uint8_land(v___x_850_, v___x_837_);
v___x_852_ = lean_uint8_dec_eq(v___x_851_, v___x_831_);
v___x_853_ = lean_unsigned_to_nat(2u);
v___x_854_ = lean_nat_add(v_i_827_, v___x_853_);
v___x_855_ = lean_byte_array_fget(v_bytes_826_, v___x_854_);
lean_dec(v___x_854_);
v___x_856_ = lean_uint8_land(v___x_855_, v___x_837_);
v___x_857_ = lean_uint8_dec_eq(v___x_856_, v___x_831_);
v___x_858_ = lean_byte_array_fget(v_bytes_826_, v___x_846_);
lean_dec(v___x_846_);
v___x_859_ = lean_uint8_land(v___x_858_, v___x_837_);
v___x_860_ = lean_uint8_dec_eq(v___x_859_, v___x_831_);
v___x_861_ = 7;
v_b_u2080_862_ = lean_uint8_land(v___x_830_, v___x_861_);
v___x_863_ = 63;
v_b_u2081_864_ = lean_uint8_land(v___x_850_, v___x_863_);
v_b_u2082_865_ = lean_uint8_land(v___x_855_, v___x_863_);
v_b_u2083_866_ = lean_uint8_land(v___x_858_, v___x_863_);
v___x_867_ = lean_uint8_to_uint32(v_b_u2080_862_);
v___x_868_ = 18;
v___x_869_ = lean_uint32_shift_left(v___x_867_, v___x_868_);
v___x_870_ = lean_uint8_to_uint32(v_b_u2081_864_);
v___x_871_ = 12;
v___x_872_ = lean_uint32_shift_left(v___x_870_, v___x_871_);
v___x_873_ = lean_uint32_lor(v___x_869_, v___x_872_);
v___x_874_ = lean_uint8_to_uint32(v_b_u2082_865_);
v___x_875_ = 6;
v___x_876_ = lean_uint32_shift_left(v___x_874_, v___x_875_);
v___x_877_ = lean_uint32_lor(v___x_873_, v___x_876_);
v___x_878_ = lean_uint8_to_uint32(v_b_u2083_866_);
v_r_879_ = lean_uint32_lor(v___x_877_, v___x_878_);
v___x_880_ = 65536;
v___x_881_ = lean_uint32_dec_lt(v_r_879_, v___x_880_);
v___x_882_ = 1114111;
v___x_883_ = lean_uint32_dec_lt(v___x_882_, v_r_879_);
return v_r_879_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; uint8_t v___x_890_; uint8_t v___x_891_; uint8_t v___x_892_; uint8_t v___x_893_; uint8_t v___x_894_; uint8_t v___x_895_; uint8_t v_b_u2080_896_; uint8_t v___x_897_; uint8_t v_b_u2081_898_; uint8_t v_b_u2082_899_; uint32_t v___x_900_; uint32_t v___x_901_; uint32_t v___x_902_; uint32_t v___x_903_; uint32_t v___x_904_; uint32_t v___x_905_; uint32_t v___x_906_; uint32_t v___x_907_; uint32_t v_r_908_; uint32_t v___x_909_; uint8_t v___x_910_; uint32_t v___x_911_; uint8_t v___x_912_; 
v___x_884_ = lean_unsigned_to_nat(2u);
v___x_885_ = lean_nat_add(v_i_827_, v___x_884_);
v___x_886_ = lean_nat_dec_lt(v___x_885_, v___x_828_);
v___x_887_ = lean_unsigned_to_nat(1u);
v___x_888_ = lean_nat_add(v_i_827_, v___x_887_);
v___x_889_ = lean_byte_array_fget(v_bytes_826_, v___x_888_);
lean_dec(v___x_888_);
v___x_890_ = lean_uint8_land(v___x_889_, v___x_837_);
v___x_891_ = lean_uint8_dec_eq(v___x_890_, v___x_831_);
v___x_892_ = lean_byte_array_fget(v_bytes_826_, v___x_885_);
lean_dec(v___x_885_);
v___x_893_ = lean_uint8_land(v___x_892_, v___x_837_);
v___x_894_ = lean_uint8_dec_eq(v___x_893_, v___x_831_);
v___x_895_ = 15;
v_b_u2080_896_ = lean_uint8_land(v___x_830_, v___x_895_);
v___x_897_ = 63;
v_b_u2081_898_ = lean_uint8_land(v___x_889_, v___x_897_);
v_b_u2082_899_ = lean_uint8_land(v___x_892_, v___x_897_);
v___x_900_ = lean_uint8_to_uint32(v_b_u2080_896_);
v___x_901_ = 12;
v___x_902_ = lean_uint32_shift_left(v___x_900_, v___x_901_);
v___x_903_ = lean_uint8_to_uint32(v_b_u2081_898_);
v___x_904_ = 6;
v___x_905_ = lean_uint32_shift_left(v___x_903_, v___x_904_);
v___x_906_ = lean_uint32_lor(v___x_902_, v___x_905_);
v___x_907_ = lean_uint8_to_uint32(v_b_u2082_899_);
v_r_908_ = lean_uint32_lor(v___x_906_, v___x_907_);
v___x_909_ = 2048;
v___x_910_ = lean_uint32_dec_lt(v_r_908_, v___x_909_);
v___x_911_ = 55296;
v___x_912_ = lean_uint32_dec_le(v___x_911_, v_r_908_);
if (v___x_912_ == 0)
{
return v_r_908_;
}
else
{
uint32_t v___x_913_; uint8_t v___x_914_; 
v___x_913_ = 57343;
v___x_914_ = lean_uint32_dec_le(v_r_908_, v___x_913_);
return v_r_908_;
}
}
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; uint8_t v___x_918_; uint8_t v___x_919_; uint8_t v___x_920_; uint8_t v___x_921_; uint8_t v_b_u2080_922_; uint8_t v___x_923_; uint8_t v_b_u2081_924_; uint32_t v___x_925_; uint32_t v___x_926_; uint32_t v___x_927_; uint32_t v___x_928_; uint32_t v_r_929_; uint32_t v___x_930_; uint8_t v___x_931_; 
v___x_915_ = lean_unsigned_to_nat(1u);
v___x_916_ = lean_nat_add(v_i_827_, v___x_915_);
v___x_917_ = lean_nat_dec_lt(v___x_916_, v___x_828_);
v___x_918_ = lean_byte_array_fget(v_bytes_826_, v___x_916_);
lean_dec(v___x_916_);
v___x_919_ = lean_uint8_land(v___x_918_, v___x_837_);
v___x_920_ = lean_uint8_dec_eq(v___x_919_, v___x_831_);
v___x_921_ = 31;
v_b_u2080_922_ = lean_uint8_land(v___x_830_, v___x_921_);
v___x_923_ = 63;
v_b_u2081_924_ = lean_uint8_land(v___x_918_, v___x_923_);
v___x_925_ = lean_uint8_to_uint32(v_b_u2080_922_);
v___x_926_ = 6;
v___x_927_ = lean_uint32_shift_left(v___x_925_, v___x_926_);
v___x_928_ = lean_uint8_to_uint32(v_b_u2081_924_);
v_r_929_ = lean_uint32_lor(v___x_927_, v___x_928_);
v___x_930_ = 128;
v___x_931_ = lean_uint32_dec_lt(v_r_929_, v___x_930_);
return v_r_929_;
}
}
else
{
uint32_t v___x_932_; 
v___x_932_ = lean_uint8_to_uint32(v___x_830_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___redArg___boxed(lean_object* v_bytes_933_, lean_object* v_i_934_){
_start:
{
uint32_t v_res_935_; lean_object* v_r_936_; 
v_res_935_ = l_ByteArray_utf8DecodeChar___redArg(v_bytes_933_, v_i_934_);
lean_dec(v_i_934_);
lean_dec_ref(v_bytes_933_);
v_r_936_ = lean_box_uint32(v_res_935_);
return v_r_936_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar(lean_object* v_bytes_937_, lean_object* v_i_938_, lean_object* v_h_939_){
_start:
{
lean_object* v___x_940_; uint8_t v___x_941_; uint8_t v___x_942_; uint8_t v___x_943_; uint8_t v___x_944_; uint8_t v___x_945_; uint8_t v___x_946_; 
v___x_940_ = lean_byte_array_size(v_bytes_937_);
v___x_941_ = lean_nat_dec_lt(v_i_938_, v___x_940_);
v___x_942_ = lean_byte_array_fget(v_bytes_937_, v_i_938_);
v___x_943_ = 128;
v___x_944_ = lean_uint8_land(v___x_942_, v___x_943_);
v___x_945_ = 0;
v___x_946_ = lean_uint8_dec_eq(v___x_944_, v___x_945_);
if (v___x_946_ == 0)
{
uint8_t v___x_947_; uint8_t v___x_948_; uint8_t v___x_949_; uint8_t v___x_950_; 
v___x_947_ = 224;
v___x_948_ = lean_uint8_land(v___x_942_, v___x_947_);
v___x_949_ = 192;
v___x_950_ = lean_uint8_dec_eq(v___x_948_, v___x_949_);
if (v___x_950_ == 0)
{
uint8_t v___x_951_; uint8_t v___x_952_; uint8_t v___x_953_; 
v___x_951_ = 240;
v___x_952_ = lean_uint8_land(v___x_942_, v___x_951_);
v___x_953_ = lean_uint8_dec_eq(v___x_952_, v___x_947_);
if (v___x_953_ == 0)
{
uint8_t v___x_954_; uint8_t v___x_955_; uint8_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; uint8_t v___x_963_; uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; uint8_t v___x_968_; uint8_t v___x_969_; uint8_t v___x_970_; uint8_t v___x_971_; uint8_t v___x_972_; uint8_t v___x_973_; uint8_t v_b_u2080_974_; uint8_t v___x_975_; uint8_t v_b_u2081_976_; uint8_t v_b_u2082_977_; uint8_t v_b_u2083_978_; uint32_t v___x_979_; uint32_t v___x_980_; uint32_t v___x_981_; uint32_t v___x_982_; uint32_t v___x_983_; uint32_t v___x_984_; uint32_t v___x_985_; uint32_t v___x_986_; uint32_t v___x_987_; uint32_t v___x_988_; uint32_t v___x_989_; uint32_t v___x_990_; uint32_t v_r_991_; uint32_t v___x_992_; uint8_t v___x_993_; uint32_t v___x_994_; uint8_t v___x_995_; 
v___x_954_ = 248;
v___x_955_ = lean_uint8_land(v___x_942_, v___x_954_);
v___x_956_ = lean_uint8_dec_eq(v___x_955_, v___x_951_);
v___x_957_ = lean_unsigned_to_nat(3u);
v___x_958_ = lean_nat_add(v_i_938_, v___x_957_);
v___x_959_ = lean_nat_dec_lt(v___x_958_, v___x_940_);
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_add(v_i_938_, v___x_960_);
v___x_962_ = lean_byte_array_fget(v_bytes_937_, v___x_961_);
lean_dec(v___x_961_);
v___x_963_ = lean_uint8_land(v___x_962_, v___x_949_);
v___x_964_ = lean_uint8_dec_eq(v___x_963_, v___x_943_);
v___x_965_ = lean_unsigned_to_nat(2u);
v___x_966_ = lean_nat_add(v_i_938_, v___x_965_);
v___x_967_ = lean_byte_array_fget(v_bytes_937_, v___x_966_);
lean_dec(v___x_966_);
v___x_968_ = lean_uint8_land(v___x_967_, v___x_949_);
v___x_969_ = lean_uint8_dec_eq(v___x_968_, v___x_943_);
v___x_970_ = lean_byte_array_fget(v_bytes_937_, v___x_958_);
lean_dec(v___x_958_);
v___x_971_ = lean_uint8_land(v___x_970_, v___x_949_);
v___x_972_ = lean_uint8_dec_eq(v___x_971_, v___x_943_);
v___x_973_ = 7;
v_b_u2080_974_ = lean_uint8_land(v___x_942_, v___x_973_);
v___x_975_ = 63;
v_b_u2081_976_ = lean_uint8_land(v___x_962_, v___x_975_);
v_b_u2082_977_ = lean_uint8_land(v___x_967_, v___x_975_);
v_b_u2083_978_ = lean_uint8_land(v___x_970_, v___x_975_);
v___x_979_ = lean_uint8_to_uint32(v_b_u2080_974_);
v___x_980_ = 18;
v___x_981_ = lean_uint32_shift_left(v___x_979_, v___x_980_);
v___x_982_ = lean_uint8_to_uint32(v_b_u2081_976_);
v___x_983_ = 12;
v___x_984_ = lean_uint32_shift_left(v___x_982_, v___x_983_);
v___x_985_ = lean_uint32_lor(v___x_981_, v___x_984_);
v___x_986_ = lean_uint8_to_uint32(v_b_u2082_977_);
v___x_987_ = 6;
v___x_988_ = lean_uint32_shift_left(v___x_986_, v___x_987_);
v___x_989_ = lean_uint32_lor(v___x_985_, v___x_988_);
v___x_990_ = lean_uint8_to_uint32(v_b_u2083_978_);
v_r_991_ = lean_uint32_lor(v___x_989_, v___x_990_);
v___x_992_ = 65536;
v___x_993_ = lean_uint32_dec_lt(v_r_991_, v___x_992_);
v___x_994_ = 1114111;
v___x_995_ = lean_uint32_dec_lt(v___x_994_, v_r_991_);
return v_r_991_;
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; uint8_t v___x_1002_; uint8_t v___x_1003_; uint8_t v___x_1004_; uint8_t v___x_1005_; uint8_t v___x_1006_; uint8_t v___x_1007_; uint8_t v_b_u2080_1008_; uint8_t v___x_1009_; uint8_t v_b_u2081_1010_; uint8_t v_b_u2082_1011_; uint32_t v___x_1012_; uint32_t v___x_1013_; uint32_t v___x_1014_; uint32_t v___x_1015_; uint32_t v___x_1016_; uint32_t v___x_1017_; uint32_t v___x_1018_; uint32_t v___x_1019_; uint32_t v_r_1020_; uint32_t v___x_1021_; uint8_t v___x_1022_; uint32_t v___x_1023_; uint8_t v___x_1024_; 
v___x_996_ = lean_unsigned_to_nat(2u);
v___x_997_ = lean_nat_add(v_i_938_, v___x_996_);
v___x_998_ = lean_nat_dec_lt(v___x_997_, v___x_940_);
v___x_999_ = lean_unsigned_to_nat(1u);
v___x_1000_ = lean_nat_add(v_i_938_, v___x_999_);
v___x_1001_ = lean_byte_array_fget(v_bytes_937_, v___x_1000_);
lean_dec(v___x_1000_);
v___x_1002_ = lean_uint8_land(v___x_1001_, v___x_949_);
v___x_1003_ = lean_uint8_dec_eq(v___x_1002_, v___x_943_);
v___x_1004_ = lean_byte_array_fget(v_bytes_937_, v___x_997_);
lean_dec(v___x_997_);
v___x_1005_ = lean_uint8_land(v___x_1004_, v___x_949_);
v___x_1006_ = lean_uint8_dec_eq(v___x_1005_, v___x_943_);
v___x_1007_ = 15;
v_b_u2080_1008_ = lean_uint8_land(v___x_942_, v___x_1007_);
v___x_1009_ = 63;
v_b_u2081_1010_ = lean_uint8_land(v___x_1001_, v___x_1009_);
v_b_u2082_1011_ = lean_uint8_land(v___x_1004_, v___x_1009_);
v___x_1012_ = lean_uint8_to_uint32(v_b_u2080_1008_);
v___x_1013_ = 12;
v___x_1014_ = lean_uint32_shift_left(v___x_1012_, v___x_1013_);
v___x_1015_ = lean_uint8_to_uint32(v_b_u2081_1010_);
v___x_1016_ = 6;
v___x_1017_ = lean_uint32_shift_left(v___x_1015_, v___x_1016_);
v___x_1018_ = lean_uint32_lor(v___x_1014_, v___x_1017_);
v___x_1019_ = lean_uint8_to_uint32(v_b_u2082_1011_);
v_r_1020_ = lean_uint32_lor(v___x_1018_, v___x_1019_);
v___x_1021_ = 2048;
v___x_1022_ = lean_uint32_dec_lt(v_r_1020_, v___x_1021_);
v___x_1023_ = 55296;
v___x_1024_ = lean_uint32_dec_le(v___x_1023_, v_r_1020_);
if (v___x_1024_ == 0)
{
return v_r_1020_;
}
else
{
uint32_t v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = 57343;
v___x_1026_ = lean_uint32_dec_le(v_r_1020_, v___x_1025_);
return v_r_1020_;
}
}
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; uint8_t v___x_1030_; uint8_t v___x_1031_; uint8_t v___x_1032_; uint8_t v___x_1033_; uint8_t v_b_u2080_1034_; uint8_t v___x_1035_; uint8_t v_b_u2081_1036_; uint32_t v___x_1037_; uint32_t v___x_1038_; uint32_t v___x_1039_; uint32_t v___x_1040_; uint32_t v_r_1041_; uint32_t v___x_1042_; uint8_t v___x_1043_; 
v___x_1027_ = lean_unsigned_to_nat(1u);
v___x_1028_ = lean_nat_add(v_i_938_, v___x_1027_);
v___x_1029_ = lean_nat_dec_lt(v___x_1028_, v___x_940_);
v___x_1030_ = lean_byte_array_fget(v_bytes_937_, v___x_1028_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_uint8_land(v___x_1030_, v___x_949_);
v___x_1032_ = lean_uint8_dec_eq(v___x_1031_, v___x_943_);
v___x_1033_ = 31;
v_b_u2080_1034_ = lean_uint8_land(v___x_942_, v___x_1033_);
v___x_1035_ = 63;
v_b_u2081_1036_ = lean_uint8_land(v___x_1030_, v___x_1035_);
v___x_1037_ = lean_uint8_to_uint32(v_b_u2080_1034_);
v___x_1038_ = 6;
v___x_1039_ = lean_uint32_shift_left(v___x_1037_, v___x_1038_);
v___x_1040_ = lean_uint8_to_uint32(v_b_u2081_1036_);
v_r_1041_ = lean_uint32_lor(v___x_1039_, v___x_1040_);
v___x_1042_ = 128;
v___x_1043_ = lean_uint32_dec_lt(v_r_1041_, v___x_1042_);
return v_r_1041_;
}
}
else
{
uint32_t v___x_1044_; 
v___x_1044_ = lean_uint8_to_uint32(v___x_942_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___boxed(lean_object* v_bytes_1045_, lean_object* v_i_1046_, lean_object* v_h_1047_){
_start:
{
uint32_t v_res_1048_; lean_object* v_r_1049_; 
v_res_1048_ = l_ByteArray_utf8DecodeChar(v_bytes_1045_, v_i_1046_, v_h_1047_);
lean_dec(v_i_1046_);
lean_dec_ref(v_bytes_1045_);
v_r_1049_ = lean_box_uint32(v_res_1048_);
return v_r_1049_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableIsUTF8FirstByte(uint8_t v_c_1050_){
_start:
{
uint8_t v___x_1051_; uint8_t v___x_1052_; uint8_t v___x_1053_; uint8_t v___x_1054_; 
v___x_1051_ = 128;
v___x_1052_ = lean_uint8_land(v_c_1050_, v___x_1051_);
v___x_1053_ = 0;
v___x_1054_ = lean_uint8_dec_eq(v___x_1052_, v___x_1053_);
if (v___x_1054_ == 0)
{
uint8_t v___x_1055_; uint8_t v___x_1056_; uint8_t v___x_1057_; uint8_t v___x_1058_; uint8_t v___x_1059_; uint8_t v___x_1060_; uint8_t v___x_1061_; 
v___x_1055_ = 224;
v___x_1056_ = lean_uint8_land(v_c_1050_, v___x_1055_);
v___x_1057_ = 192;
v___x_1058_ = lean_uint8_dec_eq(v___x_1056_, v___x_1057_);
v___x_1059_ = 240;
v___x_1060_ = lean_uint8_land(v_c_1050_, v___x_1059_);
v___x_1061_ = lean_uint8_dec_eq(v___x_1060_, v___x_1055_);
if (v___x_1061_ == 0)
{
if (v___x_1058_ == 0)
{
uint8_t v___x_1062_; uint8_t v___x_1063_; uint8_t v___x_1064_; 
v___x_1062_ = 248;
v___x_1063_ = lean_uint8_land(v_c_1050_, v___x_1062_);
v___x_1064_ = lean_uint8_dec_eq(v___x_1063_, v___x_1059_);
return v___x_1064_;
}
else
{
return v___x_1058_;
}
}
else
{
if (v___x_1058_ == 0)
{
return v___x_1061_;
}
else
{
return v___x_1058_;
}
}
}
else
{
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableIsUTF8FirstByte___boxed(lean_object* v_c_1065_){
_start:
{
uint8_t v_c_boxed_1066_; uint8_t v_res_1067_; lean_object* v_r_1068_; 
v_c_boxed_1066_ = lean_unbox(v_c_1065_);
v_res_1067_ = l_UInt8_instDecidableIsUTF8FirstByte(v_c_boxed_1066_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg(uint8_t v_c_1069_){
_start:
{
uint8_t v___x_1070_; uint8_t v___x_1071_; uint8_t v___x_1072_; uint8_t v___x_1073_; 
v___x_1070_ = 128;
v___x_1071_ = lean_uint8_land(v_c_1069_, v___x_1070_);
v___x_1072_ = 0;
v___x_1073_ = lean_uint8_dec_eq(v___x_1071_, v___x_1072_);
if (v___x_1073_ == 0)
{
uint8_t v___x_1074_; uint8_t v___x_1075_; uint8_t v___x_1076_; uint8_t v___x_1077_; 
v___x_1074_ = 224;
v___x_1075_ = lean_uint8_land(v_c_1069_, v___x_1074_);
v___x_1076_ = 192;
v___x_1077_ = lean_uint8_dec_eq(v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
uint8_t v___x_1078_; uint8_t v___x_1079_; uint8_t v___x_1080_; 
v___x_1078_ = 240;
v___x_1079_ = lean_uint8_land(v_c_1069_, v___x_1078_);
v___x_1080_ = lean_uint8_dec_eq(v___x_1079_, v___x_1074_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_unsigned_to_nat(4u);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_unsigned_to_nat(3u);
return v___x_1082_;
}
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_unsigned_to_nat(2u);
return v___x_1083_;
}
}
else
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_unsigned_to_nat(1u);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg___boxed(lean_object* v_c_1085_){
_start:
{
uint8_t v_c_boxed_1086_; lean_object* v_res_1087_; 
v_c_boxed_1086_ = lean_unbox(v_c_1085_);
v_res_1087_ = l_UInt8_utf8ByteSize___redArg(v_c_boxed_1086_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize(uint8_t v_c_1088_, lean_object* v___h_1089_){
_start:
{
uint8_t v___x_1090_; uint8_t v___x_1091_; uint8_t v___x_1092_; uint8_t v___x_1093_; 
v___x_1090_ = 128;
v___x_1091_ = lean_uint8_land(v_c_1088_, v___x_1090_);
v___x_1092_ = 0;
v___x_1093_ = lean_uint8_dec_eq(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
uint8_t v___x_1094_; uint8_t v___x_1095_; uint8_t v___x_1096_; uint8_t v___x_1097_; 
v___x_1094_ = 224;
v___x_1095_ = lean_uint8_land(v_c_1088_, v___x_1094_);
v___x_1096_ = 192;
v___x_1097_ = lean_uint8_dec_eq(v___x_1095_, v___x_1096_);
if (v___x_1097_ == 0)
{
uint8_t v___x_1098_; uint8_t v___x_1099_; uint8_t v___x_1100_; 
v___x_1098_ = 240;
v___x_1099_ = lean_uint8_land(v_c_1088_, v___x_1098_);
v___x_1100_ = lean_uint8_dec_eq(v___x_1099_, v___x_1094_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_unsigned_to_nat(4u);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_unsigned_to_nat(3u);
return v___x_1102_;
}
}
else
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_unsigned_to_nat(2u);
return v___x_1103_;
}
}
else
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_unsigned_to_nat(1u);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___boxed(lean_object* v_c_1105_, lean_object* v___h_1106_){
_start:
{
uint8_t v_c_boxed_1107_; lean_object* v_res_1108_; 
v_c_boxed_1107_ = lean_unbox(v_c_1105_);
v_res_1108_ = l_UInt8_utf8ByteSize(v_c_boxed_1107_, v___h_1106_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(uint8_t v_x_1109_){
_start:
{
switch(v_x_1109_)
{
case 0:
{
lean_object* v___x_1110_; 
v___x_1110_ = lean_unsigned_to_nat(0u);
return v___x_1110_;
}
case 1:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_unsigned_to_nat(1u);
return v___x_1111_;
}
case 2:
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_unsigned_to_nat(2u);
return v___x_1112_;
}
case 3:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_unsigned_to_nat(3u);
return v___x_1113_;
}
default: 
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_unsigned_to_nat(4u);
return v___x_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize___boxed(lean_object* v_x_1115_){
_start:
{
uint8_t v_x_54__boxed_1116_; lean_object* v_res_1117_; 
v_x_54__boxed_1116_ = lean_unbox(v_x_1115_);
v_res_1117_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(v_x_54__boxed_1116_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(uint8_t v_x_1118_, lean_object* v_h__1_1119_, lean_object* v_h__2_1120_, lean_object* v_h__3_1121_, lean_object* v_h__4_1122_, lean_object* v_h__5_1123_){
_start:
{
switch(v_x_1118_)
{
case 0:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_dec(v_h__5_1123_);
lean_dec(v_h__4_1122_);
lean_dec(v_h__3_1121_);
lean_dec(v_h__2_1120_);
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_apply_1(v_h__1_1119_, v___x_1124_);
return v___x_1125_;
}
case 1:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec(v_h__5_1123_);
lean_dec(v_h__4_1122_);
lean_dec(v_h__3_1121_);
lean_dec(v_h__1_1119_);
v___x_1126_ = lean_box(0);
v___x_1127_ = lean_apply_1(v_h__2_1120_, v___x_1126_);
return v___x_1127_;
}
case 2:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_dec(v_h__5_1123_);
lean_dec(v_h__4_1122_);
lean_dec(v_h__2_1120_);
lean_dec(v_h__1_1119_);
v___x_1128_ = lean_box(0);
v___x_1129_ = lean_apply_1(v_h__3_1121_, v___x_1128_);
return v___x_1129_;
}
case 3:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v_h__5_1123_);
lean_dec(v_h__3_1121_);
lean_dec(v_h__2_1120_);
lean_dec(v_h__1_1119_);
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_apply_1(v_h__4_1122_, v___x_1130_);
return v___x_1131_;
}
default: 
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_dec(v_h__4_1122_);
lean_dec(v_h__3_1121_);
lean_dec(v_h__2_1120_);
lean_dec(v_h__1_1119_);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_apply_1(v_h__5_1123_, v___x_1132_);
return v___x_1133_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg___boxed(lean_object* v_x_1134_, lean_object* v_h__1_1135_, lean_object* v_h__2_1136_, lean_object* v_h__3_1137_, lean_object* v_h__4_1138_, lean_object* v_h__5_1139_){
_start:
{
uint8_t v_x_51__boxed_1140_; lean_object* v_res_1141_; 
v_x_51__boxed_1140_ = lean_unbox(v_x_1134_);
v_res_1141_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(v_x_51__boxed_1140_, v_h__1_1135_, v_h__2_1136_, v_h__3_1137_, v_h__4_1138_, v_h__5_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(lean_object* v_motive_1142_, uint8_t v_x_1143_, lean_object* v_h__1_1144_, lean_object* v_h__2_1145_, lean_object* v_h__3_1146_, lean_object* v_h__4_1147_, lean_object* v_h__5_1148_){
_start:
{
switch(v_x_1143_)
{
case 0:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec(v_h__5_1148_);
lean_dec(v_h__4_1147_);
lean_dec(v_h__3_1146_);
lean_dec(v_h__2_1145_);
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_apply_1(v_h__1_1144_, v___x_1149_);
return v___x_1150_;
}
case 1:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec(v_h__5_1148_);
lean_dec(v_h__4_1147_);
lean_dec(v_h__3_1146_);
lean_dec(v_h__1_1144_);
v___x_1151_ = lean_box(0);
v___x_1152_ = lean_apply_1(v_h__2_1145_, v___x_1151_);
return v___x_1152_;
}
case 2:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec(v_h__5_1148_);
lean_dec(v_h__4_1147_);
lean_dec(v_h__2_1145_);
lean_dec(v_h__1_1144_);
v___x_1153_ = lean_box(0);
v___x_1154_ = lean_apply_1(v_h__3_1146_, v___x_1153_);
return v___x_1154_;
}
case 3:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec(v_h__5_1148_);
lean_dec(v_h__3_1146_);
lean_dec(v_h__2_1145_);
lean_dec(v_h__1_1144_);
v___x_1155_ = lean_box(0);
v___x_1156_ = lean_apply_1(v_h__4_1147_, v___x_1155_);
return v___x_1156_;
}
default: 
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v_h__4_1147_);
lean_dec(v_h__3_1146_);
lean_dec(v_h__2_1145_);
lean_dec(v_h__1_1144_);
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_apply_1(v_h__5_1148_, v___x_1157_);
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___boxed(lean_object* v_motive_1159_, lean_object* v_x_1160_, lean_object* v_h__1_1161_, lean_object* v_h__2_1162_, lean_object* v_h__3_1163_, lean_object* v_h__4_1164_, lean_object* v_h__5_1165_){
_start:
{
uint8_t v_x_74__boxed_1166_; lean_object* v_res_1167_; 
v_x_74__boxed_1166_ = lean_unbox(v_x_1160_);
v_res_1167_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(v_motive_1159_, v_x_74__boxed_1166_, v_h__1_1161_, v_h__2_1162_, v_h__3_1163_, v_h__4_1164_, v_h__5_1165_);
return v_res_1167_;
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

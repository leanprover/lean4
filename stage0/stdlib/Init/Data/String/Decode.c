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
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg();
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg(){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = 1;
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg___boxed(lean_object* v___dummy_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg();
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
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
uint8_t v___x_345_; uint8_t v_b_u2080_346_; uint8_t v___x_347_; uint8_t v_b_u2081_348_; uint8_t v_b_u2082_349_; uint32_t v___x_350_; uint32_t v___x_351_; uint32_t v___x_352_; uint32_t v___x_353_; uint32_t v___x_354_; uint32_t v___x_355_; uint32_t v___x_356_; uint32_t v___x_357_; uint32_t v_r_358_; uint8_t v___y_360_; uint32_t v___x_364_; uint8_t v___x_365_; 
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
v___x_364_ = 2048;
v___x_365_ = lean_uint32_dec_lt(v_r_358_, v___x_364_);
if (v___x_365_ == 0)
{
uint32_t v___x_366_; uint8_t v___x_367_; 
v___x_366_ = 55296;
v___x_367_ = lean_uint32_dec_le(v___x_366_, v_r_358_);
if (v___x_367_ == 0)
{
v___y_360_ = v___x_367_;
goto v___jp_359_;
}
else
{
uint32_t v___x_368_; uint8_t v___x_369_; 
v___x_368_ = 57343;
v___x_369_ = lean_uint32_dec_le(v_r_358_, v___x_368_);
v___y_360_ = v___x_369_;
goto v___jp_359_;
}
}
else
{
lean_object* v___x_370_; 
v___x_370_ = lean_box(0);
return v___x_370_;
}
v___jp_359_:
{
if (v___y_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_box_uint32(v_r_358_);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
else
{
lean_object* v___x_363_; 
v___x_363_ = lean_box(0);
return v___x_363_;
}
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
uint8_t v___x_387_; uint8_t v_b_u2080_388_; uint8_t v___x_389_; uint8_t v_b_u2081_390_; uint8_t v_b_u2082_391_; uint32_t v___x_392_; uint32_t v___x_393_; uint32_t v___x_394_; uint32_t v___x_395_; uint32_t v___x_396_; uint32_t v___x_397_; uint32_t v___x_398_; uint32_t v___x_399_; uint32_t v_r_400_; uint32_t v___x_401_; uint8_t v___x_402_; uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_387_ = 15;
v_b_u2080_388_ = lean_uint8_land(v_w_378_, v___x_387_);
v___x_389_ = 63;
v_b_u2081_390_ = lean_uint8_land(v_x_379_, v___x_389_);
v_b_u2082_391_ = lean_uint8_land(v_y_380_, v___x_389_);
v___x_392_ = lean_uint8_to_uint32(v_b_u2080_388_);
v___x_393_ = 12;
v___x_394_ = lean_uint32_shift_left(v___x_392_, v___x_393_);
v___x_395_ = lean_uint8_to_uint32(v_b_u2081_390_);
v___x_396_ = 6;
v___x_397_ = lean_uint32_shift_left(v___x_395_, v___x_396_);
v___x_398_ = lean_uint32_lor(v___x_394_, v___x_397_);
v___x_399_ = lean_uint8_to_uint32(v_b_u2082_391_);
v_r_400_ = lean_uint32_lor(v___x_398_, v___x_399_);
v___x_401_ = 2048;
v___x_402_ = lean_uint32_dec_le(v___x_401_, v_r_400_);
v___x_403_ = 55296;
v___x_404_ = lean_uint32_dec_lt(v_r_400_, v___x_403_);
if (v___x_404_ == 0)
{
if (v___x_402_ == 0)
{
return v___x_402_;
}
else
{
uint32_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 57343;
v___x_406_ = lean_uint32_dec_lt(v___x_405_, v_r_400_);
return v___x_406_;
}
}
else
{
if (v___x_402_ == 0)
{
return v___x_402_;
}
else
{
return v___x_404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2083___boxed(lean_object* v_w_407_, lean_object* v_x_408_, lean_object* v_y_409_){
_start:
{
uint8_t v_w_boxed_410_; uint8_t v_x_boxed_411_; uint8_t v_y_boxed_412_; uint8_t v_res_413_; lean_object* v_r_414_; 
v_w_boxed_410_ = lean_unbox(v_w_407_);
v_x_boxed_411_ = lean_unbox(v_x_408_);
v_y_boxed_412_ = lean_unbox(v_y_409_);
v_res_413_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2083(v_w_boxed_410_, v_x_boxed_411_, v_y_boxed_412_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(uint8_t v_w_415_, uint8_t v_x_416_, uint8_t v_y_417_, uint8_t v_z_418_){
_start:
{
uint8_t v___x_419_; uint8_t v_b_u2080_420_; uint8_t v___x_421_; uint8_t v_b_u2081_422_; uint8_t v_b_u2082_423_; uint8_t v_b_u2083_424_; uint32_t v___x_425_; uint32_t v___x_426_; uint32_t v___x_427_; uint32_t v___x_428_; uint32_t v___x_429_; uint32_t v___x_430_; uint32_t v___x_431_; uint32_t v___x_432_; uint32_t v___x_433_; uint32_t v___x_434_; uint32_t v___x_435_; uint32_t v___x_436_; uint32_t v___x_437_; 
v___x_419_ = 7;
v_b_u2080_420_ = lean_uint8_land(v_w_415_, v___x_419_);
v___x_421_ = 63;
v_b_u2081_422_ = lean_uint8_land(v_x_416_, v___x_421_);
v_b_u2082_423_ = lean_uint8_land(v_y_417_, v___x_421_);
v_b_u2083_424_ = lean_uint8_land(v_z_418_, v___x_421_);
v___x_425_ = lean_uint8_to_uint32(v_b_u2080_420_);
v___x_426_ = 18;
v___x_427_ = lean_uint32_shift_left(v___x_425_, v___x_426_);
v___x_428_ = lean_uint8_to_uint32(v_b_u2081_422_);
v___x_429_ = 12;
v___x_430_ = lean_uint32_shift_left(v___x_428_, v___x_429_);
v___x_431_ = lean_uint32_lor(v___x_427_, v___x_430_);
v___x_432_ = lean_uint8_to_uint32(v_b_u2082_423_);
v___x_433_ = 6;
v___x_434_ = lean_uint32_shift_left(v___x_432_, v___x_433_);
v___x_435_ = lean_uint32_lor(v___x_431_, v___x_434_);
v___x_436_ = lean_uint8_to_uint32(v_b_u2083_424_);
v___x_437_ = lean_uint32_lor(v___x_435_, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked___boxed(lean_object* v_w_438_, lean_object* v_x_439_, lean_object* v_y_440_, lean_object* v_z_441_){
_start:
{
uint8_t v_w_boxed_442_; uint8_t v_x_boxed_443_; uint8_t v_y_boxed_444_; uint8_t v_z_boxed_445_; uint32_t v_res_446_; lean_object* v_r_447_; 
v_w_boxed_442_ = lean_unbox(v_w_438_);
v_x_boxed_443_ = lean_unbox(v_x_439_);
v_y_boxed_444_ = lean_unbox(v_y_440_);
v_z_boxed_445_ = lean_unbox(v_z_441_);
v_res_446_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(v_w_boxed_442_, v_x_boxed_443_, v_y_boxed_444_, v_z_boxed_445_);
v_r_447_ = lean_box_uint32(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(uint8_t v_w_448_, uint8_t v_x_449_, uint8_t v_y_450_, uint8_t v_z_451_){
_start:
{
uint8_t v___x_452_; uint8_t v___x_453_; uint8_t v___x_454_; uint8_t v___x_455_; 
v___x_452_ = 192;
v___x_453_ = lean_uint8_land(v_x_449_, v___x_452_);
v___x_454_ = 128;
v___x_455_ = lean_uint8_dec_eq(v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
v___x_456_ = lean_box(0);
return v___x_456_;
}
else
{
uint8_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_uint8_land(v_y_450_, v___x_452_);
v___x_458_ = lean_uint8_dec_eq(v___x_457_, v___x_454_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
uint8_t v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_uint8_land(v_z_451_, v___x_452_);
v___x_461_ = lean_uint8_dec_eq(v___x_460_, v___x_454_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
v___x_462_ = lean_box(0);
return v___x_462_;
}
else
{
uint8_t v___x_463_; uint8_t v_b_u2080_464_; uint8_t v___x_465_; uint8_t v_b_u2081_466_; uint8_t v_b_u2082_467_; uint8_t v_b_u2083_468_; uint32_t v___x_469_; uint32_t v___x_470_; uint32_t v___x_471_; uint32_t v___x_472_; uint32_t v___x_473_; uint32_t v___x_474_; uint32_t v___x_475_; uint32_t v___x_476_; uint32_t v___x_477_; uint32_t v___x_478_; uint32_t v___x_479_; uint32_t v___x_480_; uint32_t v_r_481_; uint32_t v___x_482_; uint8_t v___x_483_; 
v___x_463_ = 7;
v_b_u2080_464_ = lean_uint8_land(v_w_448_, v___x_463_);
v___x_465_ = 63;
v_b_u2081_466_ = lean_uint8_land(v_x_449_, v___x_465_);
v_b_u2082_467_ = lean_uint8_land(v_y_450_, v___x_465_);
v_b_u2083_468_ = lean_uint8_land(v_z_451_, v___x_465_);
v___x_469_ = lean_uint8_to_uint32(v_b_u2080_464_);
v___x_470_ = 18;
v___x_471_ = lean_uint32_shift_left(v___x_469_, v___x_470_);
v___x_472_ = lean_uint8_to_uint32(v_b_u2081_466_);
v___x_473_ = 12;
v___x_474_ = lean_uint32_shift_left(v___x_472_, v___x_473_);
v___x_475_ = lean_uint32_lor(v___x_471_, v___x_474_);
v___x_476_ = lean_uint8_to_uint32(v_b_u2082_467_);
v___x_477_ = 6;
v___x_478_ = lean_uint32_shift_left(v___x_476_, v___x_477_);
v___x_479_ = lean_uint32_lor(v___x_475_, v___x_478_);
v___x_480_ = lean_uint8_to_uint32(v_b_u2083_468_);
v_r_481_ = lean_uint32_lor(v___x_479_, v___x_480_);
v___x_482_ = 65536;
v___x_483_ = lean_uint32_dec_lt(v_r_481_, v___x_482_);
if (v___x_483_ == 0)
{
uint32_t v___x_484_; uint8_t v___x_485_; 
v___x_484_ = 1114111;
v___x_485_ = lean_uint32_dec_lt(v___x_484_, v_r_481_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_box_uint32(v_r_481_);
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; 
v___x_488_ = lean_box(0);
return v___x_488_;
}
}
else
{
lean_object* v___x_489_; 
v___x_489_ = lean_box(0);
return v___x_489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084___boxed(lean_object* v_w_490_, lean_object* v_x_491_, lean_object* v_y_492_, lean_object* v_z_493_){
_start:
{
uint8_t v_w_boxed_494_; uint8_t v_x_boxed_495_; uint8_t v_y_boxed_496_; uint8_t v_z_boxed_497_; lean_object* v_res_498_; 
v_w_boxed_494_ = lean_unbox(v_w_490_);
v_x_boxed_495_ = lean_unbox(v_x_491_);
v_y_boxed_496_ = lean_unbox(v_y_492_);
v_z_boxed_497_ = lean_unbox(v_z_493_);
v_res_498_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(v_w_boxed_494_, v_x_boxed_495_, v_y_boxed_496_, v_z_boxed_497_);
return v_res_498_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2084(uint8_t v_w_499_, uint8_t v_x_500_, uint8_t v_y_501_, uint8_t v_z_502_){
_start:
{
uint8_t v___x_503_; uint8_t v___x_504_; uint8_t v___x_505_; uint8_t v___x_506_; 
v___x_503_ = 192;
v___x_504_ = lean_uint8_land(v_x_500_, v___x_503_);
v___x_505_ = 128;
v___x_506_ = lean_uint8_dec_eq(v___x_504_, v___x_505_);
if (v___x_506_ == 0)
{
return v___x_506_;
}
else
{
uint8_t v___x_507_; uint8_t v___x_508_; uint8_t v___x_509_; 
v___x_507_ = 0;
v___x_508_ = lean_uint8_land(v_y_501_, v___x_503_);
v___x_509_ = lean_uint8_dec_eq(v___x_508_, v___x_505_);
if (v___x_509_ == 0)
{
return v___x_507_;
}
else
{
uint8_t v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_uint8_land(v_z_502_, v___x_503_);
v___x_511_ = lean_uint8_dec_eq(v___x_510_, v___x_505_);
if (v___x_511_ == 0)
{
return v___x_507_;
}
else
{
uint8_t v___x_512_; uint8_t v_b_u2080_513_; uint8_t v___x_514_; uint8_t v_b_u2081_515_; uint8_t v_b_u2082_516_; uint8_t v_b_u2083_517_; uint32_t v___x_518_; uint32_t v___x_519_; uint32_t v___x_520_; uint32_t v___x_521_; uint32_t v___x_522_; uint32_t v___x_523_; uint32_t v___x_524_; uint32_t v___x_525_; uint32_t v___x_526_; uint32_t v___x_527_; uint32_t v___x_528_; uint32_t v___x_529_; uint32_t v_r_530_; uint32_t v___x_531_; uint8_t v___x_532_; 
v___x_512_ = 7;
v_b_u2080_513_ = lean_uint8_land(v_w_499_, v___x_512_);
v___x_514_ = 63;
v_b_u2081_515_ = lean_uint8_land(v_x_500_, v___x_514_);
v_b_u2082_516_ = lean_uint8_land(v_y_501_, v___x_514_);
v_b_u2083_517_ = lean_uint8_land(v_z_502_, v___x_514_);
v___x_518_ = lean_uint8_to_uint32(v_b_u2080_513_);
v___x_519_ = 18;
v___x_520_ = lean_uint32_shift_left(v___x_518_, v___x_519_);
v___x_521_ = lean_uint8_to_uint32(v_b_u2081_515_);
v___x_522_ = 12;
v___x_523_ = lean_uint32_shift_left(v___x_521_, v___x_522_);
v___x_524_ = lean_uint32_lor(v___x_520_, v___x_523_);
v___x_525_ = lean_uint8_to_uint32(v_b_u2082_516_);
v___x_526_ = 6;
v___x_527_ = lean_uint32_shift_left(v___x_525_, v___x_526_);
v___x_528_ = lean_uint32_lor(v___x_524_, v___x_527_);
v___x_529_ = lean_uint8_to_uint32(v_b_u2083_517_);
v_r_530_ = lean_uint32_lor(v___x_528_, v___x_529_);
v___x_531_ = 65536;
v___x_532_ = lean_uint32_dec_le(v___x_531_, v_r_530_);
if (v___x_532_ == 0)
{
return v___x_532_;
}
else
{
uint32_t v___x_533_; uint8_t v___x_534_; 
v___x_533_ = 1114111;
v___x_534_ = lean_uint32_dec_le(v_r_530_, v___x_533_);
return v___x_534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2084___boxed(lean_object* v_w_535_, lean_object* v_x_536_, lean_object* v_y_537_, lean_object* v_z_538_){
_start:
{
uint8_t v_w_boxed_539_; uint8_t v_x_boxed_540_; uint8_t v_y_boxed_541_; uint8_t v_z_boxed_542_; uint8_t v_res_543_; lean_object* v_r_544_; 
v_w_boxed_539_ = lean_unbox(v_w_535_);
v_x_boxed_540_ = lean_unbox(v_x_536_);
v_y_boxed_541_ = lean_unbox(v_y_537_);
v_z_boxed_542_ = lean_unbox(v_z_538_);
v_res_543_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2084(v_w_boxed_539_, v_x_boxed_540_, v_y_boxed_541_, v_z_boxed_542_);
v_r_544_ = lean_box(v_res_543_);
return v_r_544_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f(lean_object* v_bytes_545_, lean_object* v_i_546_){
_start:
{
lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_547_ = lean_byte_array_size(v_bytes_545_);
v___x_548_ = lean_nat_dec_lt(v_i_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; 
v___x_549_ = lean_box(0);
return v___x_549_;
}
else
{
uint8_t v___x_550_; uint8_t v___x_551_; uint8_t v___x_552_; uint8_t v___x_553_; uint8_t v___x_554_; 
v___x_550_ = lean_byte_array_fget(v_bytes_545_, v_i_546_);
v___x_551_ = 128;
v___x_552_ = lean_uint8_land(v___x_550_, v___x_551_);
v___x_553_ = 0;
v___x_554_ = lean_uint8_dec_eq(v___x_552_, v___x_553_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; uint8_t v___x_556_; uint8_t v___x_557_; uint8_t v___x_558_; 
v___x_555_ = 224;
v___x_556_ = lean_uint8_land(v___x_550_, v___x_555_);
v___x_557_ = 192;
v___x_558_ = lean_uint8_dec_eq(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
uint8_t v___x_559_; uint8_t v___x_560_; uint8_t v___x_561_; 
v___x_559_ = 240;
v___x_560_ = lean_uint8_land(v___x_550_, v___x_559_);
v___x_561_ = lean_uint8_dec_eq(v___x_560_, v___x_555_);
if (v___x_561_ == 0)
{
uint8_t v___x_562_; uint8_t v___x_563_; uint8_t v___x_564_; 
v___x_562_ = 248;
v___x_563_ = lean_uint8_land(v___x_550_, v___x_562_);
v___x_564_ = lean_uint8_dec_eq(v___x_563_, v___x_559_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
v___x_565_ = lean_box(0);
return v___x_565_;
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_566_ = lean_unsigned_to_nat(3u);
v___x_567_ = lean_nat_add(v_i_546_, v___x_566_);
v___x_568_ = lean_nat_dec_lt(v___x_567_, v___x_547_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
lean_dec(v___x_567_);
v___x_569_ = lean_box(0);
return v___x_569_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; uint8_t v___x_573_; uint8_t v___x_574_; 
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_nat_add(v_i_546_, v___x_570_);
v___x_572_ = lean_byte_array_fget(v_bytes_545_, v___x_571_);
lean_dec(v___x_571_);
v___x_573_ = lean_uint8_land(v___x_572_, v___x_557_);
v___x_574_ = lean_uint8_dec_eq(v___x_573_, v___x_551_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
lean_dec(v___x_567_);
v___x_575_ = lean_box(0);
return v___x_575_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; uint8_t v___x_579_; uint8_t v___x_580_; 
v___x_576_ = lean_unsigned_to_nat(2u);
v___x_577_ = lean_nat_add(v_i_546_, v___x_576_);
v___x_578_ = lean_byte_array_fget(v_bytes_545_, v___x_577_);
lean_dec(v___x_577_);
v___x_579_ = lean_uint8_land(v___x_578_, v___x_557_);
v___x_580_ = lean_uint8_dec_eq(v___x_579_, v___x_551_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
lean_dec(v___x_567_);
v___x_581_ = lean_box(0);
return v___x_581_;
}
else
{
uint8_t v___x_582_; uint8_t v___x_583_; uint8_t v___x_584_; 
v___x_582_ = lean_byte_array_fget(v_bytes_545_, v___x_567_);
lean_dec(v___x_567_);
v___x_583_ = lean_uint8_land(v___x_582_, v___x_557_);
v___x_584_ = lean_uint8_dec_eq(v___x_583_, v___x_551_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
v___x_585_ = lean_box(0);
return v___x_585_;
}
else
{
uint8_t v___x_586_; uint8_t v_b_u2080_587_; uint8_t v___x_588_; uint8_t v_b_u2081_589_; uint8_t v_b_u2082_590_; uint8_t v_b_u2083_591_; uint32_t v___x_592_; uint32_t v___x_593_; uint32_t v___x_594_; uint32_t v___x_595_; uint32_t v___x_596_; uint32_t v___x_597_; uint32_t v___x_598_; uint32_t v___x_599_; uint32_t v___x_600_; uint32_t v___x_601_; uint32_t v___x_602_; uint32_t v___x_603_; uint32_t v_r_604_; uint32_t v___x_605_; uint8_t v___x_606_; 
v___x_586_ = 7;
v_b_u2080_587_ = lean_uint8_land(v___x_550_, v___x_586_);
v___x_588_ = 63;
v_b_u2081_589_ = lean_uint8_land(v___x_572_, v___x_588_);
v_b_u2082_590_ = lean_uint8_land(v___x_578_, v___x_588_);
v_b_u2083_591_ = lean_uint8_land(v___x_582_, v___x_588_);
v___x_592_ = lean_uint8_to_uint32(v_b_u2080_587_);
v___x_593_ = 18;
v___x_594_ = lean_uint32_shift_left(v___x_592_, v___x_593_);
v___x_595_ = lean_uint8_to_uint32(v_b_u2081_589_);
v___x_596_ = 12;
v___x_597_ = lean_uint32_shift_left(v___x_595_, v___x_596_);
v___x_598_ = lean_uint32_lor(v___x_594_, v___x_597_);
v___x_599_ = lean_uint8_to_uint32(v_b_u2082_590_);
v___x_600_ = 6;
v___x_601_ = lean_uint32_shift_left(v___x_599_, v___x_600_);
v___x_602_ = lean_uint32_lor(v___x_598_, v___x_601_);
v___x_603_ = lean_uint8_to_uint32(v_b_u2083_591_);
v_r_604_ = lean_uint32_lor(v___x_602_, v___x_603_);
v___x_605_ = 65536;
v___x_606_ = lean_uint32_dec_lt(v_r_604_, v___x_605_);
if (v___x_606_ == 0)
{
uint32_t v___x_607_; uint8_t v___x_608_; 
v___x_607_ = 1114111;
v___x_608_ = lean_uint32_dec_lt(v___x_607_, v_r_604_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_box_uint32(v_r_604_);
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
else
{
lean_object* v___x_611_; 
v___x_611_ = lean_box(0);
return v___x_611_;
}
}
else
{
lean_object* v___x_612_; 
v___x_612_ = lean_box(0);
return v___x_612_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_613_ = lean_unsigned_to_nat(2u);
v___x_614_ = lean_nat_add(v_i_546_, v___x_613_);
v___x_615_ = lean_nat_dec_lt(v___x_614_, v___x_547_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
lean_dec(v___x_614_);
v___x_616_ = lean_box(0);
return v___x_616_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; uint8_t v___x_620_; uint8_t v___x_621_; 
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = lean_nat_add(v_i_546_, v___x_617_);
v___x_619_ = lean_byte_array_fget(v_bytes_545_, v___x_618_);
lean_dec(v___x_618_);
v___x_620_ = lean_uint8_land(v___x_619_, v___x_557_);
v___x_621_ = lean_uint8_dec_eq(v___x_620_, v___x_551_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
lean_dec(v___x_614_);
v___x_622_ = lean_box(0);
return v___x_622_;
}
else
{
uint8_t v___x_623_; uint8_t v___x_624_; uint8_t v___x_625_; 
v___x_623_ = lean_byte_array_fget(v_bytes_545_, v___x_614_);
lean_dec(v___x_614_);
v___x_624_ = lean_uint8_land(v___x_623_, v___x_557_);
v___x_625_ = lean_uint8_dec_eq(v___x_624_, v___x_551_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
v___x_626_ = lean_box(0);
return v___x_626_;
}
else
{
uint8_t v___x_627_; uint8_t v_b_u2080_628_; uint8_t v___x_629_; uint8_t v_b_u2081_630_; uint8_t v_b_u2082_631_; uint32_t v___x_632_; uint32_t v___x_633_; uint32_t v___x_634_; uint32_t v___x_635_; uint32_t v___x_636_; uint32_t v___x_637_; uint32_t v___x_638_; uint32_t v___x_639_; uint32_t v_r_640_; uint8_t v___y_642_; uint32_t v___x_646_; uint8_t v___x_647_; 
v___x_627_ = 15;
v_b_u2080_628_ = lean_uint8_land(v___x_550_, v___x_627_);
v___x_629_ = 63;
v_b_u2081_630_ = lean_uint8_land(v___x_619_, v___x_629_);
v_b_u2082_631_ = lean_uint8_land(v___x_623_, v___x_629_);
v___x_632_ = lean_uint8_to_uint32(v_b_u2080_628_);
v___x_633_ = 12;
v___x_634_ = lean_uint32_shift_left(v___x_632_, v___x_633_);
v___x_635_ = lean_uint8_to_uint32(v_b_u2081_630_);
v___x_636_ = 6;
v___x_637_ = lean_uint32_shift_left(v___x_635_, v___x_636_);
v___x_638_ = lean_uint32_lor(v___x_634_, v___x_637_);
v___x_639_ = lean_uint8_to_uint32(v_b_u2082_631_);
v_r_640_ = lean_uint32_lor(v___x_638_, v___x_639_);
v___x_646_ = 2048;
v___x_647_ = lean_uint32_dec_lt(v_r_640_, v___x_646_);
if (v___x_647_ == 0)
{
uint32_t v___x_648_; uint8_t v___x_649_; 
v___x_648_ = 55296;
v___x_649_ = lean_uint32_dec_le(v___x_648_, v_r_640_);
if (v___x_649_ == 0)
{
v___y_642_ = v___x_649_;
goto v___jp_641_;
}
else
{
uint32_t v___x_650_; uint8_t v___x_651_; 
v___x_650_ = 57343;
v___x_651_ = lean_uint32_dec_le(v_r_640_, v___x_650_);
v___y_642_ = v___x_651_;
goto v___jp_641_;
}
}
else
{
lean_object* v___x_652_; 
v___x_652_ = lean_box(0);
return v___x_652_;
}
v___jp_641_:
{
if (v___y_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_box_uint32(v_r_640_);
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
else
{
lean_object* v___x_645_; 
v___x_645_ = lean_box(0);
return v___x_645_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_nat_add(v_i_546_, v___x_653_);
v___x_655_ = lean_nat_dec_lt(v___x_654_, v___x_547_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec(v___x_654_);
v___x_656_ = lean_box(0);
return v___x_656_;
}
else
{
uint8_t v___x_657_; uint8_t v___x_658_; uint8_t v___x_659_; 
v___x_657_ = lean_byte_array_fget(v_bytes_545_, v___x_654_);
lean_dec(v___x_654_);
v___x_658_ = lean_uint8_land(v___x_657_, v___x_557_);
v___x_659_ = lean_uint8_dec_eq(v___x_658_, v___x_551_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
v___x_660_ = lean_box(0);
return v___x_660_;
}
else
{
uint8_t v___x_661_; uint8_t v_b_u2080_662_; uint8_t v___x_663_; uint8_t v_b_u2081_664_; uint32_t v___x_665_; uint32_t v___x_666_; uint32_t v___x_667_; uint32_t v___x_668_; uint32_t v_r_669_; uint32_t v___x_670_; uint8_t v___x_671_; 
v___x_661_ = 31;
v_b_u2080_662_ = lean_uint8_land(v___x_550_, v___x_661_);
v___x_663_ = 63;
v_b_u2081_664_ = lean_uint8_land(v___x_657_, v___x_663_);
v___x_665_ = lean_uint8_to_uint32(v_b_u2080_662_);
v___x_666_ = 6;
v___x_667_ = lean_uint32_shift_left(v___x_665_, v___x_666_);
v___x_668_ = lean_uint8_to_uint32(v_b_u2081_664_);
v_r_669_ = lean_uint32_lor(v___x_667_, v___x_668_);
v___x_670_ = 128;
v___x_671_ = lean_uint32_dec_lt(v_r_669_, v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_box_uint32(v_r_669_);
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = lean_box(0);
return v___x_674_;
}
}
}
}
}
else
{
uint32_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_uint8_to_uint32(v___x_550_);
v___x_676_ = lean_box_uint32(v___x_675_);
v___x_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f___boxed(lean_object* v_bytes_678_, lean_object* v_i_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_ByteArray_utf8DecodeChar_x3f(v_bytes_678_, v_i_679_);
lean_dec(v_i_679_);
lean_dec_ref(v_bytes_678_);
return v_res_680_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8At(lean_object* v_bytes_681_, lean_object* v_i_682_){
_start:
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_byte_array_size(v_bytes_681_);
v___x_684_ = lean_nat_dec_lt(v_i_682_, v___x_683_);
if (v___x_684_ == 0)
{
return v___x_684_;
}
else
{
uint8_t v___x_685_; uint8_t v___x_686_; uint8_t v___x_687_; uint8_t v___x_688_; uint8_t v___x_689_; 
v___x_685_ = lean_byte_array_fget(v_bytes_681_, v_i_682_);
v___x_686_ = 128;
v___x_687_ = lean_uint8_land(v___x_685_, v___x_686_);
v___x_688_ = 0;
v___x_689_ = lean_uint8_dec_eq(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
uint8_t v___x_690_; uint8_t v___x_691_; uint8_t v___x_692_; uint8_t v___x_693_; 
v___x_690_ = 224;
v___x_691_ = lean_uint8_land(v___x_685_, v___x_690_);
v___x_692_ = 192;
v___x_693_ = lean_uint8_dec_eq(v___x_691_, v___x_692_);
if (v___x_693_ == 0)
{
uint8_t v___x_694_; uint8_t v___x_695_; uint8_t v___x_696_; 
v___x_694_ = 240;
v___x_695_ = lean_uint8_land(v___x_685_, v___x_694_);
v___x_696_ = lean_uint8_dec_eq(v___x_695_, v___x_690_);
if (v___x_696_ == 0)
{
uint8_t v___x_697_; uint8_t v___x_698_; uint8_t v___x_699_; 
v___x_697_ = 248;
v___x_698_ = lean_uint8_land(v___x_685_, v___x_697_);
v___x_699_ = lean_uint8_dec_eq(v___x_698_, v___x_694_);
if (v___x_699_ == 0)
{
return v___x_699_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_700_ = lean_unsigned_to_nat(3u);
v___x_701_ = lean_nat_add(v_i_682_, v___x_700_);
v___x_702_ = lean_nat_dec_lt(v___x_701_, v___x_683_);
if (v___x_702_ == 0)
{
lean_dec(v___x_701_);
return v___x_702_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; uint8_t v___x_706_; uint8_t v___x_707_; 
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = lean_nat_add(v_i_682_, v___x_703_);
v___x_705_ = lean_byte_array_fget(v_bytes_681_, v___x_704_);
lean_dec(v___x_704_);
v___x_706_ = lean_uint8_land(v___x_705_, v___x_692_);
v___x_707_ = lean_uint8_dec_eq(v___x_706_, v___x_686_);
if (v___x_707_ == 0)
{
lean_dec(v___x_701_);
return v___x_707_;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; uint8_t v___x_711_; uint8_t v___x_712_; 
v___x_708_ = lean_unsigned_to_nat(2u);
v___x_709_ = lean_nat_add(v_i_682_, v___x_708_);
v___x_710_ = lean_byte_array_fget(v_bytes_681_, v___x_709_);
lean_dec(v___x_709_);
v___x_711_ = lean_uint8_land(v___x_710_, v___x_692_);
v___x_712_ = lean_uint8_dec_eq(v___x_711_, v___x_686_);
if (v___x_712_ == 0)
{
lean_dec(v___x_701_);
return v___x_696_;
}
else
{
uint8_t v___x_713_; uint8_t v___x_714_; uint8_t v___x_715_; 
v___x_713_ = lean_byte_array_fget(v_bytes_681_, v___x_701_);
lean_dec(v___x_701_);
v___x_714_ = lean_uint8_land(v___x_713_, v___x_692_);
v___x_715_ = lean_uint8_dec_eq(v___x_714_, v___x_686_);
if (v___x_715_ == 0)
{
return v___x_696_;
}
else
{
uint8_t v___x_716_; uint8_t v_b_u2080_717_; uint8_t v___x_718_; uint8_t v_b_u2081_719_; uint8_t v_b_u2082_720_; uint8_t v_b_u2083_721_; uint32_t v___x_722_; uint32_t v___x_723_; uint32_t v___x_724_; uint32_t v___x_725_; uint32_t v___x_726_; uint32_t v___x_727_; uint32_t v___x_728_; uint32_t v___x_729_; uint32_t v___x_730_; uint32_t v___x_731_; uint32_t v___x_732_; uint32_t v___x_733_; uint32_t v_r_734_; uint32_t v___x_735_; uint8_t v___x_736_; 
v___x_716_ = 7;
v_b_u2080_717_ = lean_uint8_land(v___x_685_, v___x_716_);
v___x_718_ = 63;
v_b_u2081_719_ = lean_uint8_land(v___x_705_, v___x_718_);
v_b_u2082_720_ = lean_uint8_land(v___x_710_, v___x_718_);
v_b_u2083_721_ = lean_uint8_land(v___x_713_, v___x_718_);
v___x_722_ = lean_uint8_to_uint32(v_b_u2080_717_);
v___x_723_ = 18;
v___x_724_ = lean_uint32_shift_left(v___x_722_, v___x_723_);
v___x_725_ = lean_uint8_to_uint32(v_b_u2081_719_);
v___x_726_ = 12;
v___x_727_ = lean_uint32_shift_left(v___x_725_, v___x_726_);
v___x_728_ = lean_uint32_lor(v___x_724_, v___x_727_);
v___x_729_ = lean_uint8_to_uint32(v_b_u2082_720_);
v___x_730_ = 6;
v___x_731_ = lean_uint32_shift_left(v___x_729_, v___x_730_);
v___x_732_ = lean_uint32_lor(v___x_728_, v___x_731_);
v___x_733_ = lean_uint8_to_uint32(v_b_u2083_721_);
v_r_734_ = lean_uint32_lor(v___x_732_, v___x_733_);
v___x_735_ = 65536;
v___x_736_ = lean_uint32_dec_le(v___x_735_, v_r_734_);
if (v___x_736_ == 0)
{
return v___x_736_;
}
else
{
uint32_t v___x_737_; uint8_t v___x_738_; 
v___x_737_ = 1114111;
v___x_738_ = lean_uint32_dec_le(v_r_734_, v___x_737_);
return v___x_738_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_739_ = lean_unsigned_to_nat(2u);
v___x_740_ = lean_nat_add(v_i_682_, v___x_739_);
v___x_741_ = lean_nat_dec_lt(v___x_740_, v___x_683_);
if (v___x_741_ == 0)
{
lean_dec(v___x_740_);
return v___x_741_;
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; uint8_t v___x_745_; uint8_t v___x_746_; 
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = lean_nat_add(v_i_682_, v___x_742_);
v___x_744_ = lean_byte_array_fget(v_bytes_681_, v___x_743_);
lean_dec(v___x_743_);
v___x_745_ = lean_uint8_land(v___x_744_, v___x_692_);
v___x_746_ = lean_uint8_dec_eq(v___x_745_, v___x_686_);
if (v___x_746_ == 0)
{
lean_dec(v___x_740_);
return v___x_746_;
}
else
{
uint8_t v___x_747_; uint8_t v___x_748_; uint8_t v___x_749_; 
v___x_747_ = lean_byte_array_fget(v_bytes_681_, v___x_740_);
lean_dec(v___x_740_);
v___x_748_ = lean_uint8_land(v___x_747_, v___x_692_);
v___x_749_ = lean_uint8_dec_eq(v___x_748_, v___x_686_);
if (v___x_749_ == 0)
{
return v___x_749_;
}
else
{
uint8_t v___x_750_; uint8_t v_b_u2080_751_; uint8_t v___x_752_; uint8_t v_b_u2081_753_; uint8_t v_b_u2082_754_; uint32_t v___x_755_; uint32_t v___x_756_; uint32_t v___x_757_; uint32_t v___x_758_; uint32_t v___x_759_; uint32_t v___x_760_; uint32_t v___x_761_; uint32_t v___x_762_; uint32_t v_r_763_; uint32_t v___x_764_; uint8_t v___x_765_; uint32_t v___x_766_; uint8_t v___x_767_; 
v___x_750_ = 15;
v_b_u2080_751_ = lean_uint8_land(v___x_685_, v___x_750_);
v___x_752_ = 63;
v_b_u2081_753_ = lean_uint8_land(v___x_744_, v___x_752_);
v_b_u2082_754_ = lean_uint8_land(v___x_747_, v___x_752_);
v___x_755_ = lean_uint8_to_uint32(v_b_u2080_751_);
v___x_756_ = 12;
v___x_757_ = lean_uint32_shift_left(v___x_755_, v___x_756_);
v___x_758_ = lean_uint8_to_uint32(v_b_u2081_753_);
v___x_759_ = 6;
v___x_760_ = lean_uint32_shift_left(v___x_758_, v___x_759_);
v___x_761_ = lean_uint32_lor(v___x_757_, v___x_760_);
v___x_762_ = lean_uint8_to_uint32(v_b_u2082_754_);
v_r_763_ = lean_uint32_lor(v___x_761_, v___x_762_);
v___x_764_ = 2048;
v___x_765_ = lean_uint32_dec_le(v___x_764_, v_r_763_);
v___x_766_ = 55296;
v___x_767_ = lean_uint32_dec_lt(v_r_763_, v___x_766_);
if (v___x_767_ == 0)
{
if (v___x_765_ == 0)
{
return v___x_765_;
}
else
{
uint32_t v___x_768_; uint8_t v___x_769_; 
v___x_768_ = 57343;
v___x_769_ = lean_uint32_dec_lt(v___x_768_, v_r_763_);
return v___x_769_;
}
}
else
{
if (v___x_765_ == 0)
{
return v___x_765_;
}
else
{
return v___x_767_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_770_ = lean_unsigned_to_nat(1u);
v___x_771_ = lean_nat_add(v_i_682_, v___x_770_);
v___x_772_ = lean_nat_dec_lt(v___x_771_, v___x_683_);
if (v___x_772_ == 0)
{
lean_dec(v___x_771_);
return v___x_772_;
}
else
{
uint8_t v___x_773_; uint8_t v___x_774_; uint8_t v___x_775_; 
v___x_773_ = lean_byte_array_fget(v_bytes_681_, v___x_771_);
lean_dec(v___x_771_);
v___x_774_ = lean_uint8_land(v___x_773_, v___x_692_);
v___x_775_ = lean_uint8_dec_eq(v___x_774_, v___x_686_);
if (v___x_775_ == 0)
{
return v___x_775_;
}
else
{
uint8_t v___x_776_; uint8_t v_b_u2080_777_; uint8_t v___x_778_; uint8_t v_b_u2081_779_; uint32_t v___x_780_; uint32_t v___x_781_; uint32_t v___x_782_; uint32_t v___x_783_; uint32_t v_r_784_; uint32_t v___x_785_; uint8_t v___x_786_; 
v___x_776_ = 31;
v_b_u2080_777_ = lean_uint8_land(v___x_685_, v___x_776_);
v___x_778_ = 63;
v_b_u2081_779_ = lean_uint8_land(v___x_773_, v___x_778_);
v___x_780_ = lean_uint8_to_uint32(v_b_u2080_777_);
v___x_781_ = 6;
v___x_782_ = lean_uint32_shift_left(v___x_780_, v___x_781_);
v___x_783_ = lean_uint8_to_uint32(v_b_u2081_779_);
v_r_784_ = lean_uint32_lor(v___x_782_, v___x_783_);
v___x_785_ = 128;
v___x_786_ = lean_uint32_dec_le(v___x_785_, v_r_784_);
return v___x_786_;
}
}
}
}
else
{
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8At___boxed(lean_object* v_bytes_787_, lean_object* v_i_788_){
_start:
{
uint8_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l_ByteArray_validateUTF8At(v_bytes_787_, v_i_788_);
lean_dec(v_i_788_);
lean_dec_ref(v_bytes_787_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t v_x_791_, lean_object* v_h__1_792_, lean_object* v_h__2_793_, lean_object* v_h__3_794_, lean_object* v_h__4_795_, lean_object* v_h__5_796_){
_start:
{
switch(v_x_791_)
{
case 0:
{
lean_object* v___x_797_; 
lean_dec(v_h__5_796_);
lean_dec(v_h__4_795_);
lean_dec(v_h__3_794_);
lean_dec(v_h__2_793_);
v___x_797_ = lean_apply_1(v_h__1_792_, lean_box(0));
return v___x_797_;
}
case 1:
{
lean_object* v___x_798_; 
lean_dec(v_h__5_796_);
lean_dec(v_h__4_795_);
lean_dec(v_h__3_794_);
lean_dec(v_h__1_792_);
v___x_798_ = lean_apply_1(v_h__2_793_, lean_box(0));
return v___x_798_;
}
case 2:
{
lean_object* v___x_799_; 
lean_dec(v_h__5_796_);
lean_dec(v_h__4_795_);
lean_dec(v_h__2_793_);
lean_dec(v_h__1_792_);
v___x_799_ = lean_apply_1(v_h__3_794_, lean_box(0));
return v___x_799_;
}
case 3:
{
lean_object* v___x_800_; 
lean_dec(v_h__5_796_);
lean_dec(v_h__3_794_);
lean_dec(v_h__2_793_);
lean_dec(v_h__1_792_);
v___x_800_ = lean_apply_1(v_h__4_795_, lean_box(0));
return v___x_800_;
}
default: 
{
lean_object* v___x_801_; 
lean_dec(v_h__4_795_);
lean_dec(v_h__3_794_);
lean_dec(v_h__2_793_);
lean_dec(v_h__1_792_);
v___x_801_ = lean_apply_1(v_h__5_796_, lean_box(0));
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_802_, lean_object* v_h__1_803_, lean_object* v_h__2_804_, lean_object* v_h__3_805_, lean_object* v_h__4_806_, lean_object* v_h__5_807_){
_start:
{
uint8_t v_x_47__boxed_808_; lean_object* v_res_809_; 
v_x_47__boxed_808_ = lean_unbox(v_x_802_);
v_res_809_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(v_x_47__boxed_808_, v_h__1_803_, v_h__2_804_, v_h__3_805_, v_h__4_806_, v_h__5_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object* v_motive_810_, uint8_t v_x_811_, lean_object* v_h__1_812_, lean_object* v_h__2_813_, lean_object* v_h__3_814_, lean_object* v_h__4_815_, lean_object* v_h__5_816_){
_start:
{
switch(v_x_811_)
{
case 0:
{
lean_object* v___x_817_; 
lean_dec(v_h__5_816_);
lean_dec(v_h__4_815_);
lean_dec(v_h__3_814_);
lean_dec(v_h__2_813_);
v___x_817_ = lean_apply_1(v_h__1_812_, lean_box(0));
return v___x_817_;
}
case 1:
{
lean_object* v___x_818_; 
lean_dec(v_h__5_816_);
lean_dec(v_h__4_815_);
lean_dec(v_h__3_814_);
lean_dec(v_h__1_812_);
v___x_818_ = lean_apply_1(v_h__2_813_, lean_box(0));
return v___x_818_;
}
case 2:
{
lean_object* v___x_819_; 
lean_dec(v_h__5_816_);
lean_dec(v_h__4_815_);
lean_dec(v_h__2_813_);
lean_dec(v_h__1_812_);
v___x_819_ = lean_apply_1(v_h__3_814_, lean_box(0));
return v___x_819_;
}
case 3:
{
lean_object* v___x_820_; 
lean_dec(v_h__5_816_);
lean_dec(v_h__3_814_);
lean_dec(v_h__2_813_);
lean_dec(v_h__1_812_);
v___x_820_ = lean_apply_1(v_h__4_815_, lean_box(0));
return v___x_820_;
}
default: 
{
lean_object* v___x_821_; 
lean_dec(v_h__4_815_);
lean_dec(v_h__3_814_);
lean_dec(v_h__2_813_);
lean_dec(v_h__1_812_);
v___x_821_ = lean_apply_1(v_h__5_816_, lean_box(0));
return v___x_821_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object* v_motive_822_, lean_object* v_x_823_, lean_object* v_h__1_824_, lean_object* v_h__2_825_, lean_object* v_h__3_826_, lean_object* v_h__4_827_, lean_object* v_h__5_828_){
_start:
{
uint8_t v_x_60__boxed_829_; lean_object* v_res_830_; 
v_x_60__boxed_829_ = lean_unbox(v_x_823_);
v_res_830_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(v_motive_822_, v_x_60__boxed_829_, v_h__1_824_, v_h__2_825_, v_h__3_826_, v_h__4_827_, v_h__5_828_);
return v_res_830_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar___redArg(lean_object* v_bytes_831_, lean_object* v_i_832_){
_start:
{
lean_object* v___x_833_; uint8_t v___x_834_; uint8_t v___x_835_; uint8_t v___x_836_; uint8_t v___x_837_; uint8_t v___x_838_; uint8_t v___x_839_; 
v___x_833_ = lean_byte_array_size(v_bytes_831_);
v___x_834_ = lean_nat_dec_lt(v_i_832_, v___x_833_);
v___x_835_ = lean_byte_array_fget(v_bytes_831_, v_i_832_);
v___x_836_ = 128;
v___x_837_ = lean_uint8_land(v___x_835_, v___x_836_);
v___x_838_ = 0;
v___x_839_ = lean_uint8_dec_eq(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
uint8_t v___x_840_; uint8_t v___x_841_; uint8_t v___x_842_; uint8_t v___x_843_; 
v___x_840_ = 224;
v___x_841_ = lean_uint8_land(v___x_835_, v___x_840_);
v___x_842_ = 192;
v___x_843_ = lean_uint8_dec_eq(v___x_841_, v___x_842_);
if (v___x_843_ == 0)
{
uint8_t v___x_844_; uint8_t v___x_845_; uint8_t v___x_846_; 
v___x_844_ = 240;
v___x_845_ = lean_uint8_land(v___x_835_, v___x_844_);
v___x_846_ = lean_uint8_dec_eq(v___x_845_, v___x_840_);
if (v___x_846_ == 0)
{
uint8_t v___x_847_; uint8_t v___x_848_; uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; uint8_t v___x_856_; uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; uint8_t v___x_861_; uint8_t v___x_862_; uint8_t v___x_863_; uint8_t v___x_864_; uint8_t v___x_865_; uint8_t v___x_866_; uint8_t v_b_u2080_867_; uint8_t v___x_868_; uint8_t v_b_u2081_869_; uint8_t v_b_u2082_870_; uint8_t v_b_u2083_871_; uint32_t v___x_872_; uint32_t v___x_873_; uint32_t v___x_874_; uint32_t v___x_875_; uint32_t v___x_876_; uint32_t v___x_877_; uint32_t v___x_878_; uint32_t v___x_879_; uint32_t v___x_880_; uint32_t v___x_881_; uint32_t v___x_882_; uint32_t v___x_883_; uint32_t v_r_884_; uint32_t v___x_885_; uint8_t v___x_886_; uint32_t v___x_887_; uint8_t v___x_888_; 
v___x_847_ = 248;
v___x_848_ = lean_uint8_land(v___x_835_, v___x_847_);
v___x_849_ = lean_uint8_dec_eq(v___x_848_, v___x_844_);
v___x_850_ = lean_unsigned_to_nat(3u);
v___x_851_ = lean_nat_add(v_i_832_, v___x_850_);
v___x_852_ = lean_nat_dec_lt(v___x_851_, v___x_833_);
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = lean_nat_add(v_i_832_, v___x_853_);
v___x_855_ = lean_byte_array_fget(v_bytes_831_, v___x_854_);
lean_dec(v___x_854_);
v___x_856_ = lean_uint8_land(v___x_855_, v___x_842_);
v___x_857_ = lean_uint8_dec_eq(v___x_856_, v___x_836_);
v___x_858_ = lean_unsigned_to_nat(2u);
v___x_859_ = lean_nat_add(v_i_832_, v___x_858_);
v___x_860_ = lean_byte_array_fget(v_bytes_831_, v___x_859_);
lean_dec(v___x_859_);
v___x_861_ = lean_uint8_land(v___x_860_, v___x_842_);
v___x_862_ = lean_uint8_dec_eq(v___x_861_, v___x_836_);
v___x_863_ = lean_byte_array_fget(v_bytes_831_, v___x_851_);
lean_dec(v___x_851_);
v___x_864_ = lean_uint8_land(v___x_863_, v___x_842_);
v___x_865_ = lean_uint8_dec_eq(v___x_864_, v___x_836_);
v___x_866_ = 7;
v_b_u2080_867_ = lean_uint8_land(v___x_835_, v___x_866_);
v___x_868_ = 63;
v_b_u2081_869_ = lean_uint8_land(v___x_855_, v___x_868_);
v_b_u2082_870_ = lean_uint8_land(v___x_860_, v___x_868_);
v_b_u2083_871_ = lean_uint8_land(v___x_863_, v___x_868_);
v___x_872_ = lean_uint8_to_uint32(v_b_u2080_867_);
v___x_873_ = 18;
v___x_874_ = lean_uint32_shift_left(v___x_872_, v___x_873_);
v___x_875_ = lean_uint8_to_uint32(v_b_u2081_869_);
v___x_876_ = 12;
v___x_877_ = lean_uint32_shift_left(v___x_875_, v___x_876_);
v___x_878_ = lean_uint32_lor(v___x_874_, v___x_877_);
v___x_879_ = lean_uint8_to_uint32(v_b_u2082_870_);
v___x_880_ = 6;
v___x_881_ = lean_uint32_shift_left(v___x_879_, v___x_880_);
v___x_882_ = lean_uint32_lor(v___x_878_, v___x_881_);
v___x_883_ = lean_uint8_to_uint32(v_b_u2083_871_);
v_r_884_ = lean_uint32_lor(v___x_882_, v___x_883_);
v___x_885_ = 65536;
v___x_886_ = lean_uint32_dec_lt(v_r_884_, v___x_885_);
v___x_887_ = 1114111;
v___x_888_ = lean_uint32_dec_lt(v___x_887_, v_r_884_);
return v_r_884_;
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; uint8_t v___x_895_; uint8_t v___x_896_; uint8_t v___x_897_; uint8_t v___x_898_; uint8_t v___x_899_; uint8_t v___x_900_; uint8_t v_b_u2080_901_; uint8_t v___x_902_; uint8_t v_b_u2081_903_; uint8_t v_b_u2082_904_; uint32_t v___x_905_; uint32_t v___x_906_; uint32_t v___x_907_; uint32_t v___x_908_; uint32_t v___x_909_; uint32_t v___x_910_; uint32_t v___x_911_; uint32_t v___x_912_; uint32_t v_r_913_; uint32_t v___x_914_; uint8_t v___x_915_; uint32_t v___x_916_; uint8_t v___x_917_; 
v___x_889_ = lean_unsigned_to_nat(2u);
v___x_890_ = lean_nat_add(v_i_832_, v___x_889_);
v___x_891_ = lean_nat_dec_lt(v___x_890_, v___x_833_);
v___x_892_ = lean_unsigned_to_nat(1u);
v___x_893_ = lean_nat_add(v_i_832_, v___x_892_);
v___x_894_ = lean_byte_array_fget(v_bytes_831_, v___x_893_);
lean_dec(v___x_893_);
v___x_895_ = lean_uint8_land(v___x_894_, v___x_842_);
v___x_896_ = lean_uint8_dec_eq(v___x_895_, v___x_836_);
v___x_897_ = lean_byte_array_fget(v_bytes_831_, v___x_890_);
lean_dec(v___x_890_);
v___x_898_ = lean_uint8_land(v___x_897_, v___x_842_);
v___x_899_ = lean_uint8_dec_eq(v___x_898_, v___x_836_);
v___x_900_ = 15;
v_b_u2080_901_ = lean_uint8_land(v___x_835_, v___x_900_);
v___x_902_ = 63;
v_b_u2081_903_ = lean_uint8_land(v___x_894_, v___x_902_);
v_b_u2082_904_ = lean_uint8_land(v___x_897_, v___x_902_);
v___x_905_ = lean_uint8_to_uint32(v_b_u2080_901_);
v___x_906_ = 12;
v___x_907_ = lean_uint32_shift_left(v___x_905_, v___x_906_);
v___x_908_ = lean_uint8_to_uint32(v_b_u2081_903_);
v___x_909_ = 6;
v___x_910_ = lean_uint32_shift_left(v___x_908_, v___x_909_);
v___x_911_ = lean_uint32_lor(v___x_907_, v___x_910_);
v___x_912_ = lean_uint8_to_uint32(v_b_u2082_904_);
v_r_913_ = lean_uint32_lor(v___x_911_, v___x_912_);
v___x_914_ = 2048;
v___x_915_ = lean_uint32_dec_lt(v_r_913_, v___x_914_);
v___x_916_ = 55296;
v___x_917_ = lean_uint32_dec_le(v___x_916_, v_r_913_);
if (v___x_917_ == 0)
{
return v_r_913_;
}
else
{
uint32_t v___x_918_; uint8_t v___x_919_; 
v___x_918_ = 57343;
v___x_919_ = lean_uint32_dec_le(v_r_913_, v___x_918_);
return v_r_913_;
}
}
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; uint8_t v___x_923_; uint8_t v___x_924_; uint8_t v___x_925_; uint8_t v___x_926_; uint8_t v_b_u2080_927_; uint8_t v___x_928_; uint8_t v_b_u2081_929_; uint32_t v___x_930_; uint32_t v___x_931_; uint32_t v___x_932_; uint32_t v___x_933_; uint32_t v_r_934_; uint32_t v___x_935_; uint8_t v___x_936_; 
v___x_920_ = lean_unsigned_to_nat(1u);
v___x_921_ = lean_nat_add(v_i_832_, v___x_920_);
v___x_922_ = lean_nat_dec_lt(v___x_921_, v___x_833_);
v___x_923_ = lean_byte_array_fget(v_bytes_831_, v___x_921_);
lean_dec(v___x_921_);
v___x_924_ = lean_uint8_land(v___x_923_, v___x_842_);
v___x_925_ = lean_uint8_dec_eq(v___x_924_, v___x_836_);
v___x_926_ = 31;
v_b_u2080_927_ = lean_uint8_land(v___x_835_, v___x_926_);
v___x_928_ = 63;
v_b_u2081_929_ = lean_uint8_land(v___x_923_, v___x_928_);
v___x_930_ = lean_uint8_to_uint32(v_b_u2080_927_);
v___x_931_ = 6;
v___x_932_ = lean_uint32_shift_left(v___x_930_, v___x_931_);
v___x_933_ = lean_uint8_to_uint32(v_b_u2081_929_);
v_r_934_ = lean_uint32_lor(v___x_932_, v___x_933_);
v___x_935_ = 128;
v___x_936_ = lean_uint32_dec_lt(v_r_934_, v___x_935_);
return v_r_934_;
}
}
else
{
uint32_t v___x_937_; 
v___x_937_ = lean_uint8_to_uint32(v___x_835_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___redArg___boxed(lean_object* v_bytes_938_, lean_object* v_i_939_){
_start:
{
uint32_t v_res_940_; lean_object* v_r_941_; 
v_res_940_ = l_ByteArray_utf8DecodeChar___redArg(v_bytes_938_, v_i_939_);
lean_dec(v_i_939_);
lean_dec_ref(v_bytes_938_);
v_r_941_ = lean_box_uint32(v_res_940_);
return v_r_941_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar(lean_object* v_bytes_942_, lean_object* v_i_943_, lean_object* v_h_944_){
_start:
{
lean_object* v___x_945_; uint8_t v___x_946_; uint8_t v___x_947_; uint8_t v___x_948_; uint8_t v___x_949_; uint8_t v___x_950_; uint8_t v___x_951_; 
v___x_945_ = lean_byte_array_size(v_bytes_942_);
v___x_946_ = lean_nat_dec_lt(v_i_943_, v___x_945_);
v___x_947_ = lean_byte_array_fget(v_bytes_942_, v_i_943_);
v___x_948_ = 128;
v___x_949_ = lean_uint8_land(v___x_947_, v___x_948_);
v___x_950_ = 0;
v___x_951_ = lean_uint8_dec_eq(v___x_949_, v___x_950_);
if (v___x_951_ == 0)
{
uint8_t v___x_952_; uint8_t v___x_953_; uint8_t v___x_954_; uint8_t v___x_955_; 
v___x_952_ = 224;
v___x_953_ = lean_uint8_land(v___x_947_, v___x_952_);
v___x_954_ = 192;
v___x_955_ = lean_uint8_dec_eq(v___x_953_, v___x_954_);
if (v___x_955_ == 0)
{
uint8_t v___x_956_; uint8_t v___x_957_; uint8_t v___x_958_; 
v___x_956_ = 240;
v___x_957_ = lean_uint8_land(v___x_947_, v___x_956_);
v___x_958_ = lean_uint8_dec_eq(v___x_957_, v___x_952_);
if (v___x_958_ == 0)
{
uint8_t v___x_959_; uint8_t v___x_960_; uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; uint8_t v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; uint8_t v___x_973_; uint8_t v___x_974_; uint8_t v___x_975_; uint8_t v___x_976_; uint8_t v___x_977_; uint8_t v___x_978_; uint8_t v_b_u2080_979_; uint8_t v___x_980_; uint8_t v_b_u2081_981_; uint8_t v_b_u2082_982_; uint8_t v_b_u2083_983_; uint32_t v___x_984_; uint32_t v___x_985_; uint32_t v___x_986_; uint32_t v___x_987_; uint32_t v___x_988_; uint32_t v___x_989_; uint32_t v___x_990_; uint32_t v___x_991_; uint32_t v___x_992_; uint32_t v___x_993_; uint32_t v___x_994_; uint32_t v___x_995_; uint32_t v_r_996_; uint32_t v___x_997_; uint8_t v___x_998_; uint32_t v___x_999_; uint8_t v___x_1000_; 
v___x_959_ = 248;
v___x_960_ = lean_uint8_land(v___x_947_, v___x_959_);
v___x_961_ = lean_uint8_dec_eq(v___x_960_, v___x_956_);
v___x_962_ = lean_unsigned_to_nat(3u);
v___x_963_ = lean_nat_add(v_i_943_, v___x_962_);
v___x_964_ = lean_nat_dec_lt(v___x_963_, v___x_945_);
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = lean_nat_add(v_i_943_, v___x_965_);
v___x_967_ = lean_byte_array_fget(v_bytes_942_, v___x_966_);
lean_dec(v___x_966_);
v___x_968_ = lean_uint8_land(v___x_967_, v___x_954_);
v___x_969_ = lean_uint8_dec_eq(v___x_968_, v___x_948_);
v___x_970_ = lean_unsigned_to_nat(2u);
v___x_971_ = lean_nat_add(v_i_943_, v___x_970_);
v___x_972_ = lean_byte_array_fget(v_bytes_942_, v___x_971_);
lean_dec(v___x_971_);
v___x_973_ = lean_uint8_land(v___x_972_, v___x_954_);
v___x_974_ = lean_uint8_dec_eq(v___x_973_, v___x_948_);
v___x_975_ = lean_byte_array_fget(v_bytes_942_, v___x_963_);
lean_dec(v___x_963_);
v___x_976_ = lean_uint8_land(v___x_975_, v___x_954_);
v___x_977_ = lean_uint8_dec_eq(v___x_976_, v___x_948_);
v___x_978_ = 7;
v_b_u2080_979_ = lean_uint8_land(v___x_947_, v___x_978_);
v___x_980_ = 63;
v_b_u2081_981_ = lean_uint8_land(v___x_967_, v___x_980_);
v_b_u2082_982_ = lean_uint8_land(v___x_972_, v___x_980_);
v_b_u2083_983_ = lean_uint8_land(v___x_975_, v___x_980_);
v___x_984_ = lean_uint8_to_uint32(v_b_u2080_979_);
v___x_985_ = 18;
v___x_986_ = lean_uint32_shift_left(v___x_984_, v___x_985_);
v___x_987_ = lean_uint8_to_uint32(v_b_u2081_981_);
v___x_988_ = 12;
v___x_989_ = lean_uint32_shift_left(v___x_987_, v___x_988_);
v___x_990_ = lean_uint32_lor(v___x_986_, v___x_989_);
v___x_991_ = lean_uint8_to_uint32(v_b_u2082_982_);
v___x_992_ = 6;
v___x_993_ = lean_uint32_shift_left(v___x_991_, v___x_992_);
v___x_994_ = lean_uint32_lor(v___x_990_, v___x_993_);
v___x_995_ = lean_uint8_to_uint32(v_b_u2083_983_);
v_r_996_ = lean_uint32_lor(v___x_994_, v___x_995_);
v___x_997_ = 65536;
v___x_998_ = lean_uint32_dec_lt(v_r_996_, v___x_997_);
v___x_999_ = 1114111;
v___x_1000_ = lean_uint32_dec_lt(v___x_999_, v_r_996_);
return v_r_996_;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; uint8_t v___x_1007_; uint8_t v___x_1008_; uint8_t v___x_1009_; uint8_t v___x_1010_; uint8_t v___x_1011_; uint8_t v___x_1012_; uint8_t v_b_u2080_1013_; uint8_t v___x_1014_; uint8_t v_b_u2081_1015_; uint8_t v_b_u2082_1016_; uint32_t v___x_1017_; uint32_t v___x_1018_; uint32_t v___x_1019_; uint32_t v___x_1020_; uint32_t v___x_1021_; uint32_t v___x_1022_; uint32_t v___x_1023_; uint32_t v___x_1024_; uint32_t v_r_1025_; uint32_t v___x_1026_; uint8_t v___x_1027_; uint32_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1001_ = lean_unsigned_to_nat(2u);
v___x_1002_ = lean_nat_add(v_i_943_, v___x_1001_);
v___x_1003_ = lean_nat_dec_lt(v___x_1002_, v___x_945_);
v___x_1004_ = lean_unsigned_to_nat(1u);
v___x_1005_ = lean_nat_add(v_i_943_, v___x_1004_);
v___x_1006_ = lean_byte_array_fget(v_bytes_942_, v___x_1005_);
lean_dec(v___x_1005_);
v___x_1007_ = lean_uint8_land(v___x_1006_, v___x_954_);
v___x_1008_ = lean_uint8_dec_eq(v___x_1007_, v___x_948_);
v___x_1009_ = lean_byte_array_fget(v_bytes_942_, v___x_1002_);
lean_dec(v___x_1002_);
v___x_1010_ = lean_uint8_land(v___x_1009_, v___x_954_);
v___x_1011_ = lean_uint8_dec_eq(v___x_1010_, v___x_948_);
v___x_1012_ = 15;
v_b_u2080_1013_ = lean_uint8_land(v___x_947_, v___x_1012_);
v___x_1014_ = 63;
v_b_u2081_1015_ = lean_uint8_land(v___x_1006_, v___x_1014_);
v_b_u2082_1016_ = lean_uint8_land(v___x_1009_, v___x_1014_);
v___x_1017_ = lean_uint8_to_uint32(v_b_u2080_1013_);
v___x_1018_ = 12;
v___x_1019_ = lean_uint32_shift_left(v___x_1017_, v___x_1018_);
v___x_1020_ = lean_uint8_to_uint32(v_b_u2081_1015_);
v___x_1021_ = 6;
v___x_1022_ = lean_uint32_shift_left(v___x_1020_, v___x_1021_);
v___x_1023_ = lean_uint32_lor(v___x_1019_, v___x_1022_);
v___x_1024_ = lean_uint8_to_uint32(v_b_u2082_1016_);
v_r_1025_ = lean_uint32_lor(v___x_1023_, v___x_1024_);
v___x_1026_ = 2048;
v___x_1027_ = lean_uint32_dec_lt(v_r_1025_, v___x_1026_);
v___x_1028_ = 55296;
v___x_1029_ = lean_uint32_dec_le(v___x_1028_, v_r_1025_);
if (v___x_1029_ == 0)
{
return v_r_1025_;
}
else
{
uint32_t v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = 57343;
v___x_1031_ = lean_uint32_dec_le(v_r_1025_, v___x_1030_);
return v_r_1025_;
}
}
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; uint8_t v___x_1035_; uint8_t v___x_1036_; uint8_t v___x_1037_; uint8_t v___x_1038_; uint8_t v_b_u2080_1039_; uint8_t v___x_1040_; uint8_t v_b_u2081_1041_; uint32_t v___x_1042_; uint32_t v___x_1043_; uint32_t v___x_1044_; uint32_t v___x_1045_; uint32_t v_r_1046_; uint32_t v___x_1047_; uint8_t v___x_1048_; 
v___x_1032_ = lean_unsigned_to_nat(1u);
v___x_1033_ = lean_nat_add(v_i_943_, v___x_1032_);
v___x_1034_ = lean_nat_dec_lt(v___x_1033_, v___x_945_);
v___x_1035_ = lean_byte_array_fget(v_bytes_942_, v___x_1033_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_uint8_land(v___x_1035_, v___x_954_);
v___x_1037_ = lean_uint8_dec_eq(v___x_1036_, v___x_948_);
v___x_1038_ = 31;
v_b_u2080_1039_ = lean_uint8_land(v___x_947_, v___x_1038_);
v___x_1040_ = 63;
v_b_u2081_1041_ = lean_uint8_land(v___x_1035_, v___x_1040_);
v___x_1042_ = lean_uint8_to_uint32(v_b_u2080_1039_);
v___x_1043_ = 6;
v___x_1044_ = lean_uint32_shift_left(v___x_1042_, v___x_1043_);
v___x_1045_ = lean_uint8_to_uint32(v_b_u2081_1041_);
v_r_1046_ = lean_uint32_lor(v___x_1044_, v___x_1045_);
v___x_1047_ = 128;
v___x_1048_ = lean_uint32_dec_lt(v_r_1046_, v___x_1047_);
return v_r_1046_;
}
}
else
{
uint32_t v___x_1049_; 
v___x_1049_ = lean_uint8_to_uint32(v___x_947_);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___boxed(lean_object* v_bytes_1050_, lean_object* v_i_1051_, lean_object* v_h_1052_){
_start:
{
uint32_t v_res_1053_; lean_object* v_r_1054_; 
v_res_1053_ = l_ByteArray_utf8DecodeChar(v_bytes_1050_, v_i_1051_, v_h_1052_);
lean_dec(v_i_1051_);
lean_dec_ref(v_bytes_1050_);
v_r_1054_ = lean_box_uint32(v_res_1053_);
return v_r_1054_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableIsUTF8FirstByte(uint8_t v_c_1055_){
_start:
{
uint8_t v___x_1056_; uint8_t v___x_1057_; uint8_t v___x_1058_; uint8_t v___x_1059_; 
v___x_1056_ = 128;
v___x_1057_ = lean_uint8_land(v_c_1055_, v___x_1056_);
v___x_1058_ = 0;
v___x_1059_ = lean_uint8_dec_eq(v___x_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
uint8_t v___x_1060_; uint8_t v___x_1061_; uint8_t v___x_1062_; uint8_t v___x_1063_; uint8_t v___x_1064_; uint8_t v___x_1065_; uint8_t v___x_1066_; 
v___x_1060_ = 224;
v___x_1061_ = lean_uint8_land(v_c_1055_, v___x_1060_);
v___x_1062_ = 192;
v___x_1063_ = lean_uint8_dec_eq(v___x_1061_, v___x_1062_);
v___x_1064_ = 240;
v___x_1065_ = lean_uint8_land(v_c_1055_, v___x_1064_);
v___x_1066_ = lean_uint8_dec_eq(v___x_1065_, v___x_1060_);
if (v___x_1066_ == 0)
{
if (v___x_1063_ == 0)
{
uint8_t v___x_1067_; uint8_t v___x_1068_; uint8_t v___x_1069_; 
v___x_1067_ = 248;
v___x_1068_ = lean_uint8_land(v_c_1055_, v___x_1067_);
v___x_1069_ = lean_uint8_dec_eq(v___x_1068_, v___x_1064_);
return v___x_1069_;
}
else
{
return v___x_1063_;
}
}
else
{
if (v___x_1063_ == 0)
{
return v___x_1066_;
}
else
{
return v___x_1063_;
}
}
}
else
{
return v___x_1059_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableIsUTF8FirstByte___boxed(lean_object* v_c_1070_){
_start:
{
uint8_t v_c_boxed_1071_; uint8_t v_res_1072_; lean_object* v_r_1073_; 
v_c_boxed_1071_ = lean_unbox(v_c_1070_);
v_res_1072_ = l_UInt8_instDecidableIsUTF8FirstByte(v_c_boxed_1071_);
v_r_1073_ = lean_box(v_res_1072_);
return v_r_1073_;
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg(uint8_t v_c_1074_){
_start:
{
uint8_t v___x_1075_; uint8_t v___x_1076_; uint8_t v___x_1077_; uint8_t v___x_1078_; 
v___x_1075_ = 128;
v___x_1076_ = lean_uint8_land(v_c_1074_, v___x_1075_);
v___x_1077_ = 0;
v___x_1078_ = lean_uint8_dec_eq(v___x_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
uint8_t v___x_1079_; uint8_t v___x_1080_; uint8_t v___x_1081_; uint8_t v___x_1082_; 
v___x_1079_ = 224;
v___x_1080_ = lean_uint8_land(v_c_1074_, v___x_1079_);
v___x_1081_ = 192;
v___x_1082_ = lean_uint8_dec_eq(v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
uint8_t v___x_1083_; uint8_t v___x_1084_; uint8_t v___x_1085_; 
v___x_1083_ = 240;
v___x_1084_ = lean_uint8_land(v_c_1074_, v___x_1083_);
v___x_1085_ = lean_uint8_dec_eq(v___x_1084_, v___x_1079_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_unsigned_to_nat(4u);
return v___x_1086_;
}
else
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_unsigned_to_nat(3u);
return v___x_1087_;
}
}
else
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_unsigned_to_nat(2u);
return v___x_1088_;
}
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_unsigned_to_nat(1u);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg___boxed(lean_object* v_c_1090_){
_start:
{
uint8_t v_c_boxed_1091_; lean_object* v_res_1092_; 
v_c_boxed_1091_ = lean_unbox(v_c_1090_);
v_res_1092_ = l_UInt8_utf8ByteSize___redArg(v_c_boxed_1091_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize(uint8_t v_c_1093_, lean_object* v___h_1094_){
_start:
{
uint8_t v___x_1095_; uint8_t v___x_1096_; uint8_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1095_ = 128;
v___x_1096_ = lean_uint8_land(v_c_1093_, v___x_1095_);
v___x_1097_ = 0;
v___x_1098_ = lean_uint8_dec_eq(v___x_1096_, v___x_1097_);
if (v___x_1098_ == 0)
{
uint8_t v___x_1099_; uint8_t v___x_1100_; uint8_t v___x_1101_; uint8_t v___x_1102_; 
v___x_1099_ = 224;
v___x_1100_ = lean_uint8_land(v_c_1093_, v___x_1099_);
v___x_1101_ = 192;
v___x_1102_ = lean_uint8_dec_eq(v___x_1100_, v___x_1101_);
if (v___x_1102_ == 0)
{
uint8_t v___x_1103_; uint8_t v___x_1104_; uint8_t v___x_1105_; 
v___x_1103_ = 240;
v___x_1104_ = lean_uint8_land(v_c_1093_, v___x_1103_);
v___x_1105_ = lean_uint8_dec_eq(v___x_1104_, v___x_1099_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_unsigned_to_nat(4u);
return v___x_1106_;
}
else
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_unsigned_to_nat(3u);
return v___x_1107_;
}
}
else
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_unsigned_to_nat(2u);
return v___x_1108_;
}
}
else
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_unsigned_to_nat(1u);
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___boxed(lean_object* v_c_1110_, lean_object* v___h_1111_){
_start:
{
uint8_t v_c_boxed_1112_; lean_object* v_res_1113_; 
v_c_boxed_1112_ = lean_unbox(v_c_1110_);
v_res_1113_ = l_UInt8_utf8ByteSize(v_c_boxed_1112_, v___h_1111_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(uint8_t v_x_1114_){
_start:
{
switch(v_x_1114_)
{
case 0:
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_unsigned_to_nat(0u);
return v___x_1115_;
}
case 1:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_unsigned_to_nat(1u);
return v___x_1116_;
}
case 2:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_unsigned_to_nat(2u);
return v___x_1117_;
}
case 3:
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_unsigned_to_nat(3u);
return v___x_1118_;
}
default: 
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_unsigned_to_nat(4u);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize___boxed(lean_object* v_x_1120_){
_start:
{
uint8_t v_x_54__boxed_1121_; lean_object* v_res_1122_; 
v_x_54__boxed_1121_ = lean_unbox(v_x_1120_);
v_res_1122_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(v_x_54__boxed_1121_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(uint8_t v_x_1123_, lean_object* v_h__1_1124_, lean_object* v_h__2_1125_, lean_object* v_h__3_1126_, lean_object* v_h__4_1127_, lean_object* v_h__5_1128_){
_start:
{
switch(v_x_1123_)
{
case 0:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec(v_h__5_1128_);
lean_dec(v_h__4_1127_);
lean_dec(v_h__3_1126_);
lean_dec(v_h__2_1125_);
v___x_1129_ = lean_box(0);
v___x_1130_ = lean_apply_1(v_h__1_1124_, v___x_1129_);
return v___x_1130_;
}
case 1:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec(v_h__5_1128_);
lean_dec(v_h__4_1127_);
lean_dec(v_h__3_1126_);
lean_dec(v_h__1_1124_);
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_apply_1(v_h__2_1125_, v___x_1131_);
return v___x_1132_;
}
case 2:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v_h__5_1128_);
lean_dec(v_h__4_1127_);
lean_dec(v_h__2_1125_);
lean_dec(v_h__1_1124_);
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_apply_1(v_h__3_1126_, v___x_1133_);
return v___x_1134_;
}
case 3:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec(v_h__5_1128_);
lean_dec(v_h__3_1126_);
lean_dec(v_h__2_1125_);
lean_dec(v_h__1_1124_);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_apply_1(v_h__4_1127_, v___x_1135_);
return v___x_1136_;
}
default: 
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec(v_h__4_1127_);
lean_dec(v_h__3_1126_);
lean_dec(v_h__2_1125_);
lean_dec(v_h__1_1124_);
v___x_1137_ = lean_box(0);
v___x_1138_ = lean_apply_1(v_h__5_1128_, v___x_1137_);
return v___x_1138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg___boxed(lean_object* v_x_1139_, lean_object* v_h__1_1140_, lean_object* v_h__2_1141_, lean_object* v_h__3_1142_, lean_object* v_h__4_1143_, lean_object* v_h__5_1144_){
_start:
{
uint8_t v_x_51__boxed_1145_; lean_object* v_res_1146_; 
v_x_51__boxed_1145_ = lean_unbox(v_x_1139_);
v_res_1146_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(v_x_51__boxed_1145_, v_h__1_1140_, v_h__2_1141_, v_h__3_1142_, v_h__4_1143_, v_h__5_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(lean_object* v_motive_1147_, uint8_t v_x_1148_, lean_object* v_h__1_1149_, lean_object* v_h__2_1150_, lean_object* v_h__3_1151_, lean_object* v_h__4_1152_, lean_object* v_h__5_1153_){
_start:
{
switch(v_x_1148_)
{
case 0:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec(v_h__5_1153_);
lean_dec(v_h__4_1152_);
lean_dec(v_h__3_1151_);
lean_dec(v_h__2_1150_);
v___x_1154_ = lean_box(0);
v___x_1155_ = lean_apply_1(v_h__1_1149_, v___x_1154_);
return v___x_1155_;
}
case 1:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec(v_h__5_1153_);
lean_dec(v_h__4_1152_);
lean_dec(v_h__3_1151_);
lean_dec(v_h__1_1149_);
v___x_1156_ = lean_box(0);
v___x_1157_ = lean_apply_1(v_h__2_1150_, v___x_1156_);
return v___x_1157_;
}
case 2:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_dec(v_h__5_1153_);
lean_dec(v_h__4_1152_);
lean_dec(v_h__2_1150_);
lean_dec(v_h__1_1149_);
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_apply_1(v_h__3_1151_, v___x_1158_);
return v___x_1159_;
}
case 3:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v_h__5_1153_);
lean_dec(v_h__3_1151_);
lean_dec(v_h__2_1150_);
lean_dec(v_h__1_1149_);
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_apply_1(v_h__4_1152_, v___x_1160_);
return v___x_1161_;
}
default: 
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_dec(v_h__4_1152_);
lean_dec(v_h__3_1151_);
lean_dec(v_h__2_1150_);
lean_dec(v_h__1_1149_);
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_apply_1(v_h__5_1153_, v___x_1162_);
return v___x_1163_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___boxed(lean_object* v_motive_1164_, lean_object* v_x_1165_, lean_object* v_h__1_1166_, lean_object* v_h__2_1167_, lean_object* v_h__3_1168_, lean_object* v_h__4_1169_, lean_object* v_h__5_1170_){
_start:
{
uint8_t v_x_74__boxed_1171_; lean_object* v_res_1172_; 
v_x_74__boxed_1171_ = lean_unbox(v_x_1165_);
v_res_1172_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(v_motive_1164_, v_x_74__boxed_1171_, v_h__1_1166_, v_h__2_1167_, v_h__3_1168_, v_h__4_1169_, v_h__5_1170_);
return v_res_1172_;
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

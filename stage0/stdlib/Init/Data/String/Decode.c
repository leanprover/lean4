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
uint8_t lean_bool_not(uint8_t);
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
uint8_t v___x_206_; uint8_t v___x_207_; uint8_t v___x_208_; uint8_t v___x_209_; uint8_t v___x_210_; 
v___x_206_ = 192;
v___x_207_ = lean_uint8_land(v_b_205_, v___x_206_);
v___x_208_ = 128;
v___x_209_ = lean_uint8_dec_eq(v___x_207_, v___x_208_);
v___x_210_ = lean_bool_not(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte___boxed(lean_object* v_b_211_){
_start:
{
uint8_t v_b_boxed_212_; uint8_t v_res_213_; lean_object* v_r_214_; 
v_b_boxed_212_ = lean_unbox(v_b_211_);
v_res_213_ = l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(v_b_boxed_212_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(uint8_t v_w_215_){
_start:
{
uint32_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_uint8_to_uint32(v_w_215_);
v___x_217_ = lean_box_uint32(v___x_216_);
v___x_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg___boxed(lean_object* v_w_219_){
_start:
{
uint8_t v_w_boxed_220_; lean_object* v_res_221_; 
v_w_boxed_220_ = lean_unbox(v_w_219_);
v_res_221_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(v_w_boxed_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(uint8_t v_w_222_, lean_object* v_h_223_){
_start:
{
uint32_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_uint8_to_uint32(v_w_222_);
v___x_225_ = lean_box_uint32(v___x_224_);
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___boxed(lean_object* v_w_227_, lean_object* v_h_228_){
_start:
{
uint8_t v_w_boxed_229_; lean_object* v_res_230_; 
v_w_boxed_229_ = lean_unbox(v_w_227_);
v_res_230_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(v_w_boxed_229_, v_h_228_);
return v_res_230_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2081(uint8_t v_w_231_, uint8_t v___w_232_, lean_object* v___h_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = 1;
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2081___boxed(lean_object* v_w_235_, lean_object* v___w_236_, lean_object* v___h_237_){
_start:
{
uint8_t v_w_boxed_238_; uint8_t v___w_boxed_239_; uint8_t v_res_240_; lean_object* v_r_241_; 
v_w_boxed_238_ = lean_unbox(v_w_235_);
v___w_boxed_239_ = lean_unbox(v___w_236_);
v_res_240_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2081(v_w_boxed_238_, v___w_boxed_239_, v___h_237_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(uint8_t v_w_242_, uint8_t v_x_243_){
_start:
{
uint8_t v___x_244_; uint8_t v_b_u2080_245_; uint8_t v___x_246_; uint8_t v_b_u2081_247_; uint32_t v___x_248_; uint32_t v___x_249_; uint32_t v___x_250_; uint32_t v___x_251_; uint32_t v___x_252_; 
v___x_244_ = 31;
v_b_u2080_245_ = lean_uint8_land(v_w_242_, v___x_244_);
v___x_246_ = 63;
v_b_u2081_247_ = lean_uint8_land(v_x_243_, v___x_246_);
v___x_248_ = lean_uint8_to_uint32(v_b_u2080_245_);
v___x_249_ = 6;
v___x_250_ = lean_uint32_shift_left(v___x_248_, v___x_249_);
v___x_251_ = lean_uint8_to_uint32(v_b_u2081_247_);
v___x_252_ = lean_uint32_lor(v___x_250_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked___boxed(lean_object* v_w_253_, lean_object* v_x_254_){
_start:
{
uint8_t v_w_boxed_255_; uint8_t v_x_boxed_256_; uint32_t v_res_257_; lean_object* v_r_258_; 
v_w_boxed_255_ = lean_unbox(v_w_253_);
v_x_boxed_256_ = lean_unbox(v_x_254_);
v_res_257_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(v_w_boxed_255_, v_x_boxed_256_);
v_r_258_ = lean_box_uint32(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(uint8_t v_w_259_, uint8_t v_x_260_){
_start:
{
uint8_t v___x_261_; uint8_t v___x_262_; uint8_t v___x_263_; uint8_t v___x_264_; uint8_t v___x_265_; 
v___x_261_ = 192;
v___x_262_ = lean_uint8_land(v_x_260_, v___x_261_);
v___x_263_ = 128;
v___x_264_ = lean_uint8_dec_eq(v___x_262_, v___x_263_);
v___x_265_ = lean_bool_not(v___x_264_);
if (v___x_265_ == 0)
{
uint8_t v___x_266_; uint8_t v_b_u2080_267_; uint8_t v___x_268_; uint8_t v_b_u2081_269_; uint32_t v___x_270_; uint32_t v___x_271_; uint32_t v___x_272_; uint32_t v___x_273_; uint32_t v_r_274_; uint32_t v___x_275_; uint8_t v___x_276_; 
v___x_266_ = 31;
v_b_u2080_267_ = lean_uint8_land(v_w_259_, v___x_266_);
v___x_268_ = 63;
v_b_u2081_269_ = lean_uint8_land(v_x_260_, v___x_268_);
v___x_270_ = lean_uint8_to_uint32(v_b_u2080_267_);
v___x_271_ = 6;
v___x_272_ = lean_uint32_shift_left(v___x_270_, v___x_271_);
v___x_273_ = lean_uint8_to_uint32(v_b_u2081_269_);
v_r_274_ = lean_uint32_lor(v___x_272_, v___x_273_);
v___x_275_ = 128;
v___x_276_ = lean_uint32_dec_lt(v_r_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_box_uint32(v_r_274_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; 
v___x_279_ = lean_box(0);
return v___x_279_;
}
}
else
{
lean_object* v___x_280_; 
v___x_280_ = lean_box(0);
return v___x_280_;
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
uint8_t v___x_288_; uint8_t v___x_289_; uint8_t v___x_290_; uint8_t v___x_291_; uint8_t v___x_292_; 
v___x_288_ = 192;
v___x_289_ = lean_uint8_land(v_x_287_, v___x_288_);
v___x_290_ = 128;
v___x_291_ = lean_uint8_dec_eq(v___x_289_, v___x_290_);
v___x_292_ = lean_bool_not(v___x_291_);
if (v___x_292_ == 0)
{
uint8_t v___x_293_; uint8_t v_b_u2080_294_; uint8_t v___x_295_; uint8_t v_b_u2081_296_; uint32_t v___x_297_; uint32_t v___x_298_; uint32_t v___x_299_; uint32_t v___x_300_; uint32_t v_r_301_; uint32_t v___x_302_; uint8_t v___x_303_; 
v___x_293_ = 31;
v_b_u2080_294_ = lean_uint8_land(v_w_286_, v___x_293_);
v___x_295_ = 63;
v_b_u2081_296_ = lean_uint8_land(v_x_287_, v___x_295_);
v___x_297_ = lean_uint8_to_uint32(v_b_u2080_294_);
v___x_298_ = 6;
v___x_299_ = lean_uint32_shift_left(v___x_297_, v___x_298_);
v___x_300_ = lean_uint8_to_uint32(v_b_u2081_296_);
v_r_301_ = lean_uint32_lor(v___x_299_, v___x_300_);
v___x_302_ = 128;
v___x_303_ = lean_uint32_dec_le(v___x_302_, v_r_301_);
return v___x_303_;
}
else
{
uint8_t v___x_304_; 
v___x_304_ = 0;
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2082___boxed(lean_object* v_w_305_, lean_object* v_x_306_){
_start:
{
uint8_t v_w_boxed_307_; uint8_t v_x_boxed_308_; uint8_t v_res_309_; lean_object* v_r_310_; 
v_w_boxed_307_ = lean_unbox(v_w_305_);
v_x_boxed_308_ = lean_unbox(v_x_306_);
v_res_309_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2082(v_w_boxed_307_, v_x_boxed_308_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(uint8_t v_w_311_, uint8_t v_x_312_, uint8_t v_y_313_){
_start:
{
uint8_t v___x_314_; uint8_t v_b_u2080_315_; uint8_t v___x_316_; uint8_t v_b_u2081_317_; uint8_t v_b_u2082_318_; uint32_t v___x_319_; uint32_t v___x_320_; uint32_t v___x_321_; uint32_t v___x_322_; uint32_t v___x_323_; uint32_t v___x_324_; uint32_t v___x_325_; uint32_t v___x_326_; uint32_t v___x_327_; 
v___x_314_ = 15;
v_b_u2080_315_ = lean_uint8_land(v_w_311_, v___x_314_);
v___x_316_ = 63;
v_b_u2081_317_ = lean_uint8_land(v_x_312_, v___x_316_);
v_b_u2082_318_ = lean_uint8_land(v_y_313_, v___x_316_);
v___x_319_ = lean_uint8_to_uint32(v_b_u2080_315_);
v___x_320_ = 12;
v___x_321_ = lean_uint32_shift_left(v___x_319_, v___x_320_);
v___x_322_ = lean_uint8_to_uint32(v_b_u2081_317_);
v___x_323_ = 6;
v___x_324_ = lean_uint32_shift_left(v___x_322_, v___x_323_);
v___x_325_ = lean_uint32_lor(v___x_321_, v___x_324_);
v___x_326_ = lean_uint8_to_uint32(v_b_u2082_318_);
v___x_327_ = lean_uint32_lor(v___x_325_, v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked___boxed(lean_object* v_w_328_, lean_object* v_x_329_, lean_object* v_y_330_){
_start:
{
uint8_t v_w_boxed_331_; uint8_t v_x_boxed_332_; uint8_t v_y_boxed_333_; uint32_t v_res_334_; lean_object* v_r_335_; 
v_w_boxed_331_ = lean_unbox(v_w_328_);
v_x_boxed_332_ = lean_unbox(v_x_329_);
v_y_boxed_333_ = lean_unbox(v_y_330_);
v_res_334_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(v_w_boxed_331_, v_x_boxed_332_, v_y_boxed_333_);
v_r_335_ = lean_box_uint32(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(uint8_t v_w_336_, uint8_t v_x_337_, uint8_t v_y_338_){
_start:
{
uint8_t v___y_340_; uint8_t v___x_368_; uint8_t v___x_369_; uint8_t v___x_370_; uint8_t v___x_371_; uint8_t v___x_372_; 
v___x_368_ = 192;
v___x_369_ = lean_uint8_land(v_x_337_, v___x_368_);
v___x_370_ = 128;
v___x_371_ = lean_uint8_dec_eq(v___x_369_, v___x_370_);
v___x_372_ = lean_bool_not(v___x_371_);
if (v___x_372_ == 0)
{
uint8_t v___x_373_; uint8_t v___x_374_; uint8_t v___x_375_; 
v___x_373_ = lean_uint8_land(v_y_338_, v___x_368_);
v___x_374_ = lean_uint8_dec_eq(v___x_373_, v___x_370_);
v___x_375_ = lean_bool_not(v___x_374_);
v___y_340_ = v___x_375_;
goto v___jp_339_;
}
else
{
v___y_340_ = v___x_372_;
goto v___jp_339_;
}
v___jp_339_:
{
if (v___y_340_ == 0)
{
uint8_t v___x_341_; uint8_t v_b_u2080_342_; uint8_t v___x_343_; uint8_t v_b_u2081_344_; uint8_t v_b_u2082_345_; uint32_t v___x_346_; uint32_t v___x_347_; uint32_t v___x_348_; uint32_t v___x_349_; uint32_t v___x_350_; uint32_t v___x_351_; uint32_t v___x_352_; uint32_t v___x_353_; uint32_t v_r_354_; uint32_t v___x_355_; uint8_t v___x_356_; 
v___x_341_ = 15;
v_b_u2080_342_ = lean_uint8_land(v_w_336_, v___x_341_);
v___x_343_ = 63;
v_b_u2081_344_ = lean_uint8_land(v_x_337_, v___x_343_);
v_b_u2082_345_ = lean_uint8_land(v_y_338_, v___x_343_);
v___x_346_ = lean_uint8_to_uint32(v_b_u2080_342_);
v___x_347_ = 12;
v___x_348_ = lean_uint32_shift_left(v___x_346_, v___x_347_);
v___x_349_ = lean_uint8_to_uint32(v_b_u2081_344_);
v___x_350_ = 6;
v___x_351_ = lean_uint32_shift_left(v___x_349_, v___x_350_);
v___x_352_ = lean_uint32_lor(v___x_348_, v___x_351_);
v___x_353_ = lean_uint8_to_uint32(v_b_u2082_345_);
v_r_354_ = lean_uint32_lor(v___x_352_, v___x_353_);
v___x_355_ = 2048;
v___x_356_ = lean_uint32_dec_lt(v_r_354_, v___x_355_);
if (v___x_356_ == 0)
{
uint32_t v___x_357_; uint8_t v___x_358_; 
v___x_357_ = 55296;
v___x_358_ = lean_uint32_dec_le(v___x_357_, v_r_354_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_box_uint32(v_r_354_);
v___x_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
else
{
uint32_t v___x_361_; uint8_t v___x_362_; 
v___x_361_ = 57343;
v___x_362_ = lean_uint32_dec_le(v_r_354_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_box_uint32(v_r_354_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v___x_365_; 
v___x_365_ = lean_box(0);
return v___x_365_;
}
}
}
else
{
lean_object* v___x_366_; 
v___x_366_ = lean_box(0);
return v___x_366_;
}
}
else
{
lean_object* v___x_367_; 
v___x_367_ = lean_box(0);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083___boxed(lean_object* v_w_376_, lean_object* v_x_377_, lean_object* v_y_378_){
_start:
{
uint8_t v_w_boxed_379_; uint8_t v_x_boxed_380_; uint8_t v_y_boxed_381_; lean_object* v_res_382_; 
v_w_boxed_379_ = lean_unbox(v_w_376_);
v_x_boxed_380_ = lean_unbox(v_x_377_);
v_y_boxed_381_ = lean_unbox(v_y_378_);
v_res_382_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(v_w_boxed_379_, v_x_boxed_380_, v_y_boxed_381_);
return v_res_382_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2083(uint8_t v_w_383_, uint8_t v_x_384_, uint8_t v_y_385_){
_start:
{
uint8_t v___y_387_; uint8_t v___x_409_; uint8_t v___x_410_; uint8_t v___x_411_; uint8_t v___x_412_; uint8_t v___x_413_; 
v___x_409_ = 192;
v___x_410_ = lean_uint8_land(v_x_384_, v___x_409_);
v___x_411_ = 128;
v___x_412_ = lean_uint8_dec_eq(v___x_410_, v___x_411_);
v___x_413_ = lean_bool_not(v___x_412_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; uint8_t v___x_415_; uint8_t v___x_416_; 
v___x_414_ = lean_uint8_land(v_y_385_, v___x_409_);
v___x_415_ = lean_uint8_dec_eq(v___x_414_, v___x_411_);
v___x_416_ = lean_bool_not(v___x_415_);
v___y_387_ = v___x_416_;
goto v___jp_386_;
}
else
{
v___y_387_ = v___x_413_;
goto v___jp_386_;
}
v___jp_386_:
{
if (v___y_387_ == 0)
{
uint8_t v___x_388_; uint8_t v_b_u2080_389_; uint8_t v___x_390_; uint8_t v_b_u2081_391_; uint8_t v_b_u2082_392_; uint32_t v___x_393_; uint32_t v___x_394_; uint32_t v___x_395_; uint32_t v___x_396_; uint32_t v___x_397_; uint32_t v___x_398_; uint32_t v___x_399_; uint32_t v___x_400_; uint32_t v_r_401_; uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_388_ = 15;
v_b_u2080_389_ = lean_uint8_land(v_w_383_, v___x_388_);
v___x_390_ = 63;
v_b_u2081_391_ = lean_uint8_land(v_x_384_, v___x_390_);
v_b_u2082_392_ = lean_uint8_land(v_y_385_, v___x_390_);
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
return v___y_387_;
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
return v___y_387_;
}
else
{
return v___x_407_;
}
}
else
{
return v___x_405_;
}
}
}
else
{
uint8_t v___x_408_; 
v___x_408_ = 0;
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2083___boxed(lean_object* v_w_417_, lean_object* v_x_418_, lean_object* v_y_419_){
_start:
{
uint8_t v_w_boxed_420_; uint8_t v_x_boxed_421_; uint8_t v_y_boxed_422_; uint8_t v_res_423_; lean_object* v_r_424_; 
v_w_boxed_420_ = lean_unbox(v_w_417_);
v_x_boxed_421_ = lean_unbox(v_x_418_);
v_y_boxed_422_ = lean_unbox(v_y_419_);
v_res_423_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2083(v_w_boxed_420_, v_x_boxed_421_, v_y_boxed_422_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(uint8_t v_w_425_, uint8_t v_x_426_, uint8_t v_y_427_, uint8_t v_z_428_){
_start:
{
uint8_t v___x_429_; uint8_t v_b_u2080_430_; uint8_t v___x_431_; uint8_t v_b_u2081_432_; uint8_t v_b_u2082_433_; uint8_t v_b_u2083_434_; uint32_t v___x_435_; uint32_t v___x_436_; uint32_t v___x_437_; uint32_t v___x_438_; uint32_t v___x_439_; uint32_t v___x_440_; uint32_t v___x_441_; uint32_t v___x_442_; uint32_t v___x_443_; uint32_t v___x_444_; uint32_t v___x_445_; uint32_t v___x_446_; uint32_t v___x_447_; 
v___x_429_ = 7;
v_b_u2080_430_ = lean_uint8_land(v_w_425_, v___x_429_);
v___x_431_ = 63;
v_b_u2081_432_ = lean_uint8_land(v_x_426_, v___x_431_);
v_b_u2082_433_ = lean_uint8_land(v_y_427_, v___x_431_);
v_b_u2083_434_ = lean_uint8_land(v_z_428_, v___x_431_);
v___x_435_ = lean_uint8_to_uint32(v_b_u2080_430_);
v___x_436_ = 18;
v___x_437_ = lean_uint32_shift_left(v___x_435_, v___x_436_);
v___x_438_ = lean_uint8_to_uint32(v_b_u2081_432_);
v___x_439_ = 12;
v___x_440_ = lean_uint32_shift_left(v___x_438_, v___x_439_);
v___x_441_ = lean_uint32_lor(v___x_437_, v___x_440_);
v___x_442_ = lean_uint8_to_uint32(v_b_u2082_433_);
v___x_443_ = 6;
v___x_444_ = lean_uint32_shift_left(v___x_442_, v___x_443_);
v___x_445_ = lean_uint32_lor(v___x_441_, v___x_444_);
v___x_446_ = lean_uint8_to_uint32(v_b_u2083_434_);
v___x_447_ = lean_uint32_lor(v___x_445_, v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked___boxed(lean_object* v_w_448_, lean_object* v_x_449_, lean_object* v_y_450_, lean_object* v_z_451_){
_start:
{
uint8_t v_w_boxed_452_; uint8_t v_x_boxed_453_; uint8_t v_y_boxed_454_; uint8_t v_z_boxed_455_; uint32_t v_res_456_; lean_object* v_r_457_; 
v_w_boxed_452_ = lean_unbox(v_w_448_);
v_x_boxed_453_ = lean_unbox(v_x_449_);
v_y_boxed_454_ = lean_unbox(v_y_450_);
v_z_boxed_455_ = lean_unbox(v_z_451_);
v_res_456_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(v_w_boxed_452_, v_x_boxed_453_, v_y_boxed_454_, v_z_boxed_455_);
v_r_457_ = lean_box_uint32(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(uint8_t v_w_458_, uint8_t v_x_459_, uint8_t v_y_460_, uint8_t v_z_461_){
_start:
{
uint8_t v___y_463_; uint8_t v___x_498_; uint8_t v___x_499_; uint8_t v___x_500_; uint8_t v___x_501_; uint8_t v___x_502_; 
v___x_498_ = 192;
v___x_499_ = lean_uint8_land(v_x_459_, v___x_498_);
v___x_500_ = 128;
v___x_501_ = lean_uint8_dec_eq(v___x_499_, v___x_500_);
v___x_502_ = lean_bool_not(v___x_501_);
if (v___x_502_ == 0)
{
uint8_t v___x_503_; uint8_t v___x_504_; uint8_t v___x_505_; 
v___x_503_ = lean_uint8_land(v_y_460_, v___x_498_);
v___x_504_ = lean_uint8_dec_eq(v___x_503_, v___x_500_);
v___x_505_ = lean_bool_not(v___x_504_);
v___y_463_ = v___x_505_;
goto v___jp_462_;
}
else
{
v___y_463_ = v___x_502_;
goto v___jp_462_;
}
v___jp_462_:
{
if (v___y_463_ == 0)
{
uint8_t v___x_464_; uint8_t v___x_465_; uint8_t v___x_466_; uint8_t v___x_467_; uint8_t v___x_468_; 
v___x_464_ = 192;
v___x_465_ = lean_uint8_land(v_z_461_, v___x_464_);
v___x_466_ = 128;
v___x_467_ = lean_uint8_dec_eq(v___x_465_, v___x_466_);
v___x_468_ = lean_bool_not(v___x_467_);
if (v___x_468_ == 0)
{
uint8_t v___x_469_; uint8_t v_b_u2080_470_; uint8_t v___x_471_; uint8_t v_b_u2081_472_; uint8_t v_b_u2082_473_; uint8_t v_b_u2083_474_; uint32_t v___x_475_; uint32_t v___x_476_; uint32_t v___x_477_; uint32_t v___x_478_; uint32_t v___x_479_; uint32_t v___x_480_; uint32_t v___x_481_; uint32_t v___x_482_; uint32_t v___x_483_; uint32_t v___x_484_; uint32_t v___x_485_; uint32_t v___x_486_; uint32_t v_r_487_; uint32_t v___x_488_; uint8_t v___x_489_; 
v___x_469_ = 7;
v_b_u2080_470_ = lean_uint8_land(v_w_458_, v___x_469_);
v___x_471_ = 63;
v_b_u2081_472_ = lean_uint8_land(v_x_459_, v___x_471_);
v_b_u2082_473_ = lean_uint8_land(v_y_460_, v___x_471_);
v_b_u2083_474_ = lean_uint8_land(v_z_461_, v___x_471_);
v___x_475_ = lean_uint8_to_uint32(v_b_u2080_470_);
v___x_476_ = 18;
v___x_477_ = lean_uint32_shift_left(v___x_475_, v___x_476_);
v___x_478_ = lean_uint8_to_uint32(v_b_u2081_472_);
v___x_479_ = 12;
v___x_480_ = lean_uint32_shift_left(v___x_478_, v___x_479_);
v___x_481_ = lean_uint32_lor(v___x_477_, v___x_480_);
v___x_482_ = lean_uint8_to_uint32(v_b_u2082_473_);
v___x_483_ = 6;
v___x_484_ = lean_uint32_shift_left(v___x_482_, v___x_483_);
v___x_485_ = lean_uint32_lor(v___x_481_, v___x_484_);
v___x_486_ = lean_uint8_to_uint32(v_b_u2083_474_);
v_r_487_ = lean_uint32_lor(v___x_485_, v___x_486_);
v___x_488_ = 65536;
v___x_489_ = lean_uint32_dec_lt(v_r_487_, v___x_488_);
if (v___x_489_ == 0)
{
uint32_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = 1114111;
v___x_491_ = lean_uint32_dec_lt(v___x_490_, v_r_487_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_box_uint32(v_r_487_);
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; 
v___x_494_ = lean_box(0);
return v___x_494_;
}
}
else
{
lean_object* v___x_495_; 
v___x_495_ = lean_box(0);
return v___x_495_;
}
}
else
{
lean_object* v___x_496_; 
v___x_496_ = lean_box(0);
return v___x_496_;
}
}
else
{
lean_object* v___x_497_; 
v___x_497_ = lean_box(0);
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084___boxed(lean_object* v_w_506_, lean_object* v_x_507_, lean_object* v_y_508_, lean_object* v_z_509_){
_start:
{
uint8_t v_w_boxed_510_; uint8_t v_x_boxed_511_; uint8_t v_y_boxed_512_; uint8_t v_z_boxed_513_; lean_object* v_res_514_; 
v_w_boxed_510_ = lean_unbox(v_w_506_);
v_x_boxed_511_ = lean_unbox(v_x_507_);
v_y_boxed_512_ = lean_unbox(v_y_508_);
v_z_boxed_513_ = lean_unbox(v_z_509_);
v_res_514_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(v_w_boxed_510_, v_x_boxed_511_, v_y_boxed_512_, v_z_boxed_513_);
return v_res_514_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2084(uint8_t v_w_515_, uint8_t v_x_516_, uint8_t v_y_517_, uint8_t v_z_518_){
_start:
{
uint8_t v___y_520_; uint8_t v___x_550_; uint8_t v___x_551_; uint8_t v___x_552_; uint8_t v___x_553_; uint8_t v___x_554_; 
v___x_550_ = 192;
v___x_551_ = lean_uint8_land(v_x_516_, v___x_550_);
v___x_552_ = 128;
v___x_553_ = lean_uint8_dec_eq(v___x_551_, v___x_552_);
v___x_554_ = lean_bool_not(v___x_553_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; uint8_t v___x_556_; uint8_t v___x_557_; 
v___x_555_ = lean_uint8_land(v_y_517_, v___x_550_);
v___x_556_ = lean_uint8_dec_eq(v___x_555_, v___x_552_);
v___x_557_ = lean_bool_not(v___x_556_);
v___y_520_ = v___x_557_;
goto v___jp_519_;
}
else
{
v___y_520_ = v___x_554_;
goto v___jp_519_;
}
v___jp_519_:
{
if (v___y_520_ == 0)
{
uint8_t v___x_521_; uint8_t v___x_522_; uint8_t v___x_523_; uint8_t v___x_524_; uint8_t v___x_525_; 
v___x_521_ = 192;
v___x_522_ = lean_uint8_land(v_z_518_, v___x_521_);
v___x_523_ = 128;
v___x_524_ = lean_uint8_dec_eq(v___x_522_, v___x_523_);
v___x_525_ = lean_bool_not(v___x_524_);
if (v___x_525_ == 0)
{
uint8_t v___x_526_; uint8_t v_b_u2080_527_; uint8_t v___x_528_; uint8_t v_b_u2081_529_; uint8_t v_b_u2082_530_; uint8_t v_b_u2083_531_; uint32_t v___x_532_; uint32_t v___x_533_; uint32_t v___x_534_; uint32_t v___x_535_; uint32_t v___x_536_; uint32_t v___x_537_; uint32_t v___x_538_; uint32_t v___x_539_; uint32_t v___x_540_; uint32_t v___x_541_; uint32_t v___x_542_; uint32_t v___x_543_; uint32_t v_r_544_; uint32_t v___x_545_; uint8_t v___x_546_; 
v___x_526_ = 7;
v_b_u2080_527_ = lean_uint8_land(v_w_515_, v___x_526_);
v___x_528_ = 63;
v_b_u2081_529_ = lean_uint8_land(v_x_516_, v___x_528_);
v_b_u2082_530_ = lean_uint8_land(v_y_517_, v___x_528_);
v_b_u2083_531_ = lean_uint8_land(v_z_518_, v___x_528_);
v___x_532_ = lean_uint8_to_uint32(v_b_u2080_527_);
v___x_533_ = 18;
v___x_534_ = lean_uint32_shift_left(v___x_532_, v___x_533_);
v___x_535_ = lean_uint8_to_uint32(v_b_u2081_529_);
v___x_536_ = 12;
v___x_537_ = lean_uint32_shift_left(v___x_535_, v___x_536_);
v___x_538_ = lean_uint32_lor(v___x_534_, v___x_537_);
v___x_539_ = lean_uint8_to_uint32(v_b_u2082_530_);
v___x_540_ = 6;
v___x_541_ = lean_uint32_shift_left(v___x_539_, v___x_540_);
v___x_542_ = lean_uint32_lor(v___x_538_, v___x_541_);
v___x_543_ = lean_uint8_to_uint32(v_b_u2083_531_);
v_r_544_ = lean_uint32_lor(v___x_542_, v___x_543_);
v___x_545_ = 65536;
v___x_546_ = lean_uint32_dec_le(v___x_545_, v_r_544_);
if (v___x_546_ == 0)
{
return v___x_525_;
}
else
{
uint32_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = 1114111;
v___x_548_ = lean_uint32_dec_le(v_r_544_, v___x_547_);
if (v___x_548_ == 0)
{
return v___x_525_;
}
else
{
return v___x_548_;
}
}
}
else
{
return v___y_520_;
}
}
else
{
uint8_t v___x_549_; 
v___x_549_ = 0;
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2084___boxed(lean_object* v_w_558_, lean_object* v_x_559_, lean_object* v_y_560_, lean_object* v_z_561_){
_start:
{
uint8_t v_w_boxed_562_; uint8_t v_x_boxed_563_; uint8_t v_y_boxed_564_; uint8_t v_z_boxed_565_; uint8_t v_res_566_; lean_object* v_r_567_; 
v_w_boxed_562_ = lean_unbox(v_w_558_);
v_x_boxed_563_ = lean_unbox(v_x_559_);
v_y_boxed_564_ = lean_unbox(v_y_560_);
v_z_boxed_565_ = lean_unbox(v_z_561_);
v_res_566_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2084(v_w_boxed_562_, v_x_boxed_563_, v_y_boxed_564_, v_z_boxed_565_);
v_r_567_ = lean_box(v_res_566_);
return v_r_567_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f(lean_object* v_bytes_568_, lean_object* v_i_569_){
_start:
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_byte_array_size(v_bytes_568_);
v___x_571_ = lean_nat_dec_lt(v_i_569_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
v___x_572_ = lean_box(0);
return v___x_572_;
}
else
{
uint8_t v___x_573_; uint8_t v___x_574_; uint8_t v___x_575_; uint8_t v___x_576_; uint8_t v___x_577_; 
v___x_573_ = lean_byte_array_fget(v_bytes_568_, v_i_569_);
v___x_574_ = 128;
v___x_575_ = lean_uint8_land(v___x_573_, v___x_574_);
v___x_576_ = 0;
v___x_577_ = lean_uint8_dec_eq(v___x_575_, v___x_576_);
if (v___x_577_ == 0)
{
uint8_t v___x_578_; uint8_t v___x_579_; uint8_t v___x_580_; uint8_t v___x_581_; 
v___x_578_ = 224;
v___x_579_ = lean_uint8_land(v___x_573_, v___x_578_);
v___x_580_ = 192;
v___x_581_ = lean_uint8_dec_eq(v___x_579_, v___x_580_);
if (v___x_581_ == 0)
{
uint8_t v___x_582_; uint8_t v___x_583_; uint8_t v___x_584_; 
v___x_582_ = 240;
v___x_583_ = lean_uint8_land(v___x_573_, v___x_582_);
v___x_584_ = lean_uint8_dec_eq(v___x_583_, v___x_578_);
if (v___x_584_ == 0)
{
uint8_t v___x_585_; uint8_t v___x_586_; uint8_t v___x_587_; 
v___x_585_ = 248;
v___x_586_ = lean_uint8_land(v___x_573_, v___x_585_);
v___x_587_ = lean_uint8_dec_eq(v___x_586_, v___x_582_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
v___x_588_ = lean_box(0);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_589_ = lean_unsigned_to_nat(3u);
v___x_590_ = lean_nat_add(v_i_569_, v___x_589_);
v___x_591_ = lean_nat_dec_lt(v___x_590_, v___x_570_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
lean_dec(v___x_590_);
v___x_592_ = lean_box(0);
return v___x_592_;
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; uint8_t v___x_599_; uint8_t v___y_601_; uint8_t v___x_634_; uint8_t v___x_635_; uint8_t v___x_636_; 
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = lean_nat_add(v_i_569_, v___x_593_);
v___x_595_ = lean_byte_array_fget(v_bytes_568_, v___x_594_);
lean_dec(v___x_594_);
v___x_596_ = lean_unsigned_to_nat(2u);
v___x_597_ = lean_nat_add(v_i_569_, v___x_596_);
v___x_598_ = lean_byte_array_fget(v_bytes_568_, v___x_597_);
lean_dec(v___x_597_);
v___x_599_ = lean_byte_array_fget(v_bytes_568_, v___x_590_);
lean_dec(v___x_590_);
v___x_634_ = lean_uint8_land(v___x_595_, v___x_580_);
v___x_635_ = lean_uint8_dec_eq(v___x_634_, v___x_574_);
v___x_636_ = lean_bool_not(v___x_635_);
if (v___x_636_ == 0)
{
uint8_t v___x_637_; uint8_t v___x_638_; uint8_t v___x_639_; 
v___x_637_ = lean_uint8_land(v___x_598_, v___x_580_);
v___x_638_ = lean_uint8_dec_eq(v___x_637_, v___x_574_);
v___x_639_ = lean_bool_not(v___x_638_);
v___y_601_ = v___x_639_;
goto v___jp_600_;
}
else
{
v___y_601_ = v___x_636_;
goto v___jp_600_;
}
v___jp_600_:
{
if (v___y_601_ == 0)
{
uint8_t v___x_602_; uint8_t v___x_603_; uint8_t v___x_604_; 
v___x_602_ = lean_uint8_land(v___x_599_, v___x_580_);
v___x_603_ = lean_uint8_dec_eq(v___x_602_, v___x_574_);
v___x_604_ = lean_bool_not(v___x_603_);
if (v___x_604_ == 0)
{
uint8_t v___x_605_; uint8_t v_b_u2080_606_; uint8_t v___x_607_; uint8_t v_b_u2081_608_; uint8_t v_b_u2082_609_; uint8_t v_b_u2083_610_; uint32_t v___x_611_; uint32_t v___x_612_; uint32_t v___x_613_; uint32_t v___x_614_; uint32_t v___x_615_; uint32_t v___x_616_; uint32_t v___x_617_; uint32_t v___x_618_; uint32_t v___x_619_; uint32_t v___x_620_; uint32_t v___x_621_; uint32_t v___x_622_; uint32_t v_r_623_; uint32_t v___x_624_; uint8_t v___x_625_; 
v___x_605_ = 7;
v_b_u2080_606_ = lean_uint8_land(v___x_573_, v___x_605_);
v___x_607_ = 63;
v_b_u2081_608_ = lean_uint8_land(v___x_595_, v___x_607_);
v_b_u2082_609_ = lean_uint8_land(v___x_598_, v___x_607_);
v_b_u2083_610_ = lean_uint8_land(v___x_599_, v___x_607_);
v___x_611_ = lean_uint8_to_uint32(v_b_u2080_606_);
v___x_612_ = 18;
v___x_613_ = lean_uint32_shift_left(v___x_611_, v___x_612_);
v___x_614_ = lean_uint8_to_uint32(v_b_u2081_608_);
v___x_615_ = 12;
v___x_616_ = lean_uint32_shift_left(v___x_614_, v___x_615_);
v___x_617_ = lean_uint32_lor(v___x_613_, v___x_616_);
v___x_618_ = lean_uint8_to_uint32(v_b_u2082_609_);
v___x_619_ = 6;
v___x_620_ = lean_uint32_shift_left(v___x_618_, v___x_619_);
v___x_621_ = lean_uint32_lor(v___x_617_, v___x_620_);
v___x_622_ = lean_uint8_to_uint32(v_b_u2083_610_);
v_r_623_ = lean_uint32_lor(v___x_621_, v___x_622_);
v___x_624_ = 65536;
v___x_625_ = lean_uint32_dec_lt(v_r_623_, v___x_624_);
if (v___x_625_ == 0)
{
uint32_t v___x_626_; uint8_t v___x_627_; 
v___x_626_ = 1114111;
v___x_627_ = lean_uint32_dec_lt(v___x_626_, v_r_623_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_box_uint32(v_r_623_);
v___x_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; 
v___x_630_ = lean_box(0);
return v___x_630_;
}
}
else
{
lean_object* v___x_631_; 
v___x_631_ = lean_box(0);
return v___x_631_;
}
}
else
{
lean_object* v___x_632_; 
v___x_632_ = lean_box(0);
return v___x_632_;
}
}
else
{
lean_object* v___x_633_; 
v___x_633_ = lean_box(0);
return v___x_633_;
}
}
}
}
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_640_ = lean_unsigned_to_nat(2u);
v___x_641_ = lean_nat_add(v_i_569_, v___x_640_);
v___x_642_ = lean_nat_dec_lt(v___x_641_, v___x_570_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
lean_dec(v___x_641_);
v___x_643_ = lean_box(0);
return v___x_643_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; uint8_t v___x_647_; uint8_t v___y_649_; uint8_t v___x_677_; uint8_t v___x_678_; uint8_t v___x_679_; 
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_add(v_i_569_, v___x_644_);
v___x_646_ = lean_byte_array_fget(v_bytes_568_, v___x_645_);
lean_dec(v___x_645_);
v___x_647_ = lean_byte_array_fget(v_bytes_568_, v___x_641_);
lean_dec(v___x_641_);
v___x_677_ = lean_uint8_land(v___x_646_, v___x_580_);
v___x_678_ = lean_uint8_dec_eq(v___x_677_, v___x_574_);
v___x_679_ = lean_bool_not(v___x_678_);
if (v___x_679_ == 0)
{
uint8_t v___x_680_; uint8_t v___x_681_; uint8_t v___x_682_; 
v___x_680_ = lean_uint8_land(v___x_647_, v___x_580_);
v___x_681_ = lean_uint8_dec_eq(v___x_680_, v___x_574_);
v___x_682_ = lean_bool_not(v___x_681_);
v___y_649_ = v___x_682_;
goto v___jp_648_;
}
else
{
v___y_649_ = v___x_679_;
goto v___jp_648_;
}
v___jp_648_:
{
if (v___y_649_ == 0)
{
uint8_t v___x_650_; uint8_t v_b_u2080_651_; uint8_t v___x_652_; uint8_t v_b_u2081_653_; uint8_t v_b_u2082_654_; uint32_t v___x_655_; uint32_t v___x_656_; uint32_t v___x_657_; uint32_t v___x_658_; uint32_t v___x_659_; uint32_t v___x_660_; uint32_t v___x_661_; uint32_t v___x_662_; uint32_t v_r_663_; uint32_t v___x_664_; uint8_t v___x_665_; 
v___x_650_ = 15;
v_b_u2080_651_ = lean_uint8_land(v___x_573_, v___x_650_);
v___x_652_ = 63;
v_b_u2081_653_ = lean_uint8_land(v___x_646_, v___x_652_);
v_b_u2082_654_ = lean_uint8_land(v___x_647_, v___x_652_);
v___x_655_ = lean_uint8_to_uint32(v_b_u2080_651_);
v___x_656_ = 12;
v___x_657_ = lean_uint32_shift_left(v___x_655_, v___x_656_);
v___x_658_ = lean_uint8_to_uint32(v_b_u2081_653_);
v___x_659_ = 6;
v___x_660_ = lean_uint32_shift_left(v___x_658_, v___x_659_);
v___x_661_ = lean_uint32_lor(v___x_657_, v___x_660_);
v___x_662_ = lean_uint8_to_uint32(v_b_u2082_654_);
v_r_663_ = lean_uint32_lor(v___x_661_, v___x_662_);
v___x_664_ = 2048;
v___x_665_ = lean_uint32_dec_lt(v_r_663_, v___x_664_);
if (v___x_665_ == 0)
{
uint32_t v___x_666_; uint8_t v___x_667_; 
v___x_666_ = 55296;
v___x_667_ = lean_uint32_dec_le(v___x_666_, v_r_663_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_box_uint32(v_r_663_);
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
else
{
uint32_t v___x_670_; uint8_t v___x_671_; 
v___x_670_ = 57343;
v___x_671_ = lean_uint32_dec_le(v_r_663_, v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_box_uint32(v_r_663_);
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
else
{
lean_object* v___x_675_; 
v___x_675_ = lean_box(0);
return v___x_675_;
}
}
else
{
lean_object* v___x_676_; 
v___x_676_ = lean_box(0);
return v___x_676_;
}
}
}
}
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_nat_add(v_i_569_, v___x_683_);
v___x_685_ = lean_nat_dec_lt(v___x_684_, v___x_570_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
lean_dec(v___x_684_);
v___x_686_ = lean_box(0);
return v___x_686_;
}
else
{
uint8_t v___x_687_; uint8_t v___x_688_; uint8_t v___x_689_; uint8_t v___x_690_; 
v___x_687_ = lean_byte_array_fget(v_bytes_568_, v___x_684_);
lean_dec(v___x_684_);
v___x_688_ = lean_uint8_land(v___x_687_, v___x_580_);
v___x_689_ = lean_uint8_dec_eq(v___x_688_, v___x_574_);
v___x_690_ = lean_bool_not(v___x_689_);
if (v___x_690_ == 0)
{
uint8_t v___x_691_; uint8_t v_b_u2080_692_; uint8_t v___x_693_; uint8_t v_b_u2081_694_; uint32_t v___x_695_; uint32_t v___x_696_; uint32_t v___x_697_; uint32_t v___x_698_; uint32_t v_r_699_; uint32_t v___x_700_; uint8_t v___x_701_; 
v___x_691_ = 31;
v_b_u2080_692_ = lean_uint8_land(v___x_573_, v___x_691_);
v___x_693_ = 63;
v_b_u2081_694_ = lean_uint8_land(v___x_687_, v___x_693_);
v___x_695_ = lean_uint8_to_uint32(v_b_u2080_692_);
v___x_696_ = 6;
v___x_697_ = lean_uint32_shift_left(v___x_695_, v___x_696_);
v___x_698_ = lean_uint8_to_uint32(v_b_u2081_694_);
v_r_699_ = lean_uint32_lor(v___x_697_, v___x_698_);
v___x_700_ = 128;
v___x_701_ = lean_uint32_dec_lt(v_r_699_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_box_uint32(v_r_699_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; 
v___x_704_ = lean_box(0);
return v___x_704_;
}
}
else
{
lean_object* v___x_705_; 
v___x_705_ = lean_box(0);
return v___x_705_;
}
}
}
}
else
{
uint32_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_uint8_to_uint32(v___x_573_);
v___x_707_ = lean_box_uint32(v___x_706_);
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f___boxed(lean_object* v_bytes_709_, lean_object* v_i_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_ByteArray_utf8DecodeChar_x3f(v_bytes_709_, v_i_710_);
lean_dec(v_i_710_);
lean_dec_ref(v_bytes_709_);
return v_res_711_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8At(lean_object* v_bytes_712_, lean_object* v_i_713_){
_start:
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_byte_array_size(v_bytes_712_);
v___x_715_ = lean_nat_dec_lt(v_i_713_, v___x_714_);
if (v___x_715_ == 0)
{
return v___x_715_;
}
else
{
uint8_t v___x_716_; uint8_t v___x_717_; uint8_t v___x_718_; uint8_t v___x_719_; uint8_t v___x_720_; 
v___x_716_ = lean_byte_array_fget(v_bytes_712_, v_i_713_);
v___x_717_ = 128;
v___x_718_ = lean_uint8_land(v___x_716_, v___x_717_);
v___x_719_ = 0;
v___x_720_ = lean_uint8_dec_eq(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; uint8_t v___x_722_; uint8_t v___x_723_; uint8_t v___x_724_; 
v___x_721_ = 224;
v___x_722_ = lean_uint8_land(v___x_716_, v___x_721_);
v___x_723_ = 192;
v___x_724_ = lean_uint8_dec_eq(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
uint8_t v___x_725_; uint8_t v___x_726_; uint8_t v___x_727_; 
v___x_725_ = 240;
v___x_726_ = lean_uint8_land(v___x_716_, v___x_725_);
v___x_727_ = lean_uint8_dec_eq(v___x_726_, v___x_721_);
if (v___x_727_ == 0)
{
uint8_t v___x_728_; uint8_t v___x_729_; uint8_t v___x_730_; 
v___x_728_ = 248;
v___x_729_ = lean_uint8_land(v___x_716_, v___x_728_);
v___x_730_ = lean_uint8_dec_eq(v___x_729_, v___x_725_);
if (v___x_730_ == 0)
{
return v___x_730_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_731_ = lean_unsigned_to_nat(3u);
v___x_732_ = lean_nat_add(v_i_713_, v___x_731_);
v___x_733_ = lean_nat_dec_lt(v___x_732_, v___x_714_);
if (v___x_733_ == 0)
{
lean_dec(v___x_732_);
return v___x_727_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; uint8_t v___x_740_; uint8_t v___y_742_; uint8_t v___x_769_; uint8_t v___x_770_; uint8_t v___x_771_; 
v___x_734_ = lean_unsigned_to_nat(1u);
v___x_735_ = lean_nat_add(v_i_713_, v___x_734_);
v___x_736_ = lean_byte_array_fget(v_bytes_712_, v___x_735_);
lean_dec(v___x_735_);
v___x_737_ = lean_unsigned_to_nat(2u);
v___x_738_ = lean_nat_add(v_i_713_, v___x_737_);
v___x_739_ = lean_byte_array_fget(v_bytes_712_, v___x_738_);
lean_dec(v___x_738_);
v___x_740_ = lean_byte_array_fget(v_bytes_712_, v___x_732_);
lean_dec(v___x_732_);
v___x_769_ = lean_uint8_land(v___x_736_, v___x_723_);
v___x_770_ = lean_uint8_dec_eq(v___x_769_, v___x_717_);
v___x_771_ = lean_bool_not(v___x_770_);
if (v___x_771_ == 0)
{
uint8_t v___x_772_; uint8_t v___x_773_; uint8_t v___x_774_; 
v___x_772_ = lean_uint8_land(v___x_739_, v___x_723_);
v___x_773_ = lean_uint8_dec_eq(v___x_772_, v___x_717_);
v___x_774_ = lean_bool_not(v___x_773_);
v___y_742_ = v___x_774_;
goto v___jp_741_;
}
else
{
v___y_742_ = v___x_771_;
goto v___jp_741_;
}
v___jp_741_:
{
if (v___y_742_ == 0)
{
uint8_t v___x_743_; uint8_t v___x_744_; uint8_t v___x_745_; 
v___x_743_ = lean_uint8_land(v___x_740_, v___x_723_);
v___x_744_ = lean_uint8_dec_eq(v___x_743_, v___x_717_);
v___x_745_ = lean_bool_not(v___x_744_);
if (v___x_745_ == 0)
{
uint8_t v___x_746_; uint8_t v_b_u2080_747_; uint8_t v___x_748_; uint8_t v_b_u2081_749_; uint8_t v_b_u2082_750_; uint8_t v_b_u2083_751_; uint32_t v___x_752_; uint32_t v___x_753_; uint32_t v___x_754_; uint32_t v___x_755_; uint32_t v___x_756_; uint32_t v___x_757_; uint32_t v___x_758_; uint32_t v___x_759_; uint32_t v___x_760_; uint32_t v___x_761_; uint32_t v___x_762_; uint32_t v___x_763_; uint32_t v_r_764_; uint32_t v___x_765_; uint8_t v___x_766_; 
v___x_746_ = 7;
v_b_u2080_747_ = lean_uint8_land(v___x_716_, v___x_746_);
v___x_748_ = 63;
v_b_u2081_749_ = lean_uint8_land(v___x_736_, v___x_748_);
v_b_u2082_750_ = lean_uint8_land(v___x_739_, v___x_748_);
v_b_u2083_751_ = lean_uint8_land(v___x_740_, v___x_748_);
v___x_752_ = lean_uint8_to_uint32(v_b_u2080_747_);
v___x_753_ = 18;
v___x_754_ = lean_uint32_shift_left(v___x_752_, v___x_753_);
v___x_755_ = lean_uint8_to_uint32(v_b_u2081_749_);
v___x_756_ = 12;
v___x_757_ = lean_uint32_shift_left(v___x_755_, v___x_756_);
v___x_758_ = lean_uint32_lor(v___x_754_, v___x_757_);
v___x_759_ = lean_uint8_to_uint32(v_b_u2082_750_);
v___x_760_ = 6;
v___x_761_ = lean_uint32_shift_left(v___x_759_, v___x_760_);
v___x_762_ = lean_uint32_lor(v___x_758_, v___x_761_);
v___x_763_ = lean_uint8_to_uint32(v_b_u2083_751_);
v_r_764_ = lean_uint32_lor(v___x_762_, v___x_763_);
v___x_765_ = 65536;
v___x_766_ = lean_uint32_dec_le(v___x_765_, v_r_764_);
if (v___x_766_ == 0)
{
return v___x_745_;
}
else
{
uint32_t v___x_767_; uint8_t v___x_768_; 
v___x_767_ = 1114111;
v___x_768_ = lean_uint32_dec_le(v_r_764_, v___x_767_);
if (v___x_768_ == 0)
{
return v___x_745_;
}
else
{
return v___x_730_;
}
}
}
else
{
return v___y_742_;
}
}
else
{
return v___x_727_;
}
}
}
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_775_ = lean_unsigned_to_nat(2u);
v___x_776_ = lean_nat_add(v_i_713_, v___x_775_);
v___x_777_ = lean_nat_dec_lt(v___x_776_, v___x_714_);
if (v___x_777_ == 0)
{
lean_dec(v___x_776_);
return v___x_724_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; uint8_t v___x_781_; uint8_t v___y_783_; uint8_t v___x_804_; uint8_t v___x_805_; uint8_t v___x_806_; 
v___x_778_ = lean_unsigned_to_nat(1u);
v___x_779_ = lean_nat_add(v_i_713_, v___x_778_);
v___x_780_ = lean_byte_array_fget(v_bytes_712_, v___x_779_);
lean_dec(v___x_779_);
v___x_781_ = lean_byte_array_fget(v_bytes_712_, v___x_776_);
lean_dec(v___x_776_);
v___x_804_ = lean_uint8_land(v___x_780_, v___x_723_);
v___x_805_ = lean_uint8_dec_eq(v___x_804_, v___x_717_);
v___x_806_ = lean_bool_not(v___x_805_);
if (v___x_806_ == 0)
{
uint8_t v___x_807_; uint8_t v___x_808_; uint8_t v___x_809_; 
v___x_807_ = lean_uint8_land(v___x_781_, v___x_723_);
v___x_808_ = lean_uint8_dec_eq(v___x_807_, v___x_717_);
v___x_809_ = lean_bool_not(v___x_808_);
v___y_783_ = v___x_809_;
goto v___jp_782_;
}
else
{
v___y_783_ = v___x_806_;
goto v___jp_782_;
}
v___jp_782_:
{
if (v___y_783_ == 0)
{
uint8_t v___x_784_; uint8_t v_b_u2080_785_; uint8_t v___x_786_; uint8_t v_b_u2081_787_; uint8_t v_b_u2082_788_; uint32_t v___x_789_; uint32_t v___x_790_; uint32_t v___x_791_; uint32_t v___x_792_; uint32_t v___x_793_; uint32_t v___x_794_; uint32_t v___x_795_; uint32_t v___x_796_; uint32_t v_r_797_; uint32_t v___x_798_; uint8_t v___x_799_; 
v___x_784_ = 15;
v_b_u2080_785_ = lean_uint8_land(v___x_716_, v___x_784_);
v___x_786_ = 63;
v_b_u2081_787_ = lean_uint8_land(v___x_780_, v___x_786_);
v_b_u2082_788_ = lean_uint8_land(v___x_781_, v___x_786_);
v___x_789_ = lean_uint8_to_uint32(v_b_u2080_785_);
v___x_790_ = 12;
v___x_791_ = lean_uint32_shift_left(v___x_789_, v___x_790_);
v___x_792_ = lean_uint8_to_uint32(v_b_u2081_787_);
v___x_793_ = 6;
v___x_794_ = lean_uint32_shift_left(v___x_792_, v___x_793_);
v___x_795_ = lean_uint32_lor(v___x_791_, v___x_794_);
v___x_796_ = lean_uint8_to_uint32(v_b_u2082_788_);
v_r_797_ = lean_uint32_lor(v___x_795_, v___x_796_);
v___x_798_ = 2048;
v___x_799_ = lean_uint32_dec_le(v___x_798_, v_r_797_);
if (v___x_799_ == 0)
{
return v___y_783_;
}
else
{
uint32_t v___x_800_; uint8_t v___x_801_; 
v___x_800_ = 55296;
v___x_801_ = lean_uint32_dec_lt(v_r_797_, v___x_800_);
if (v___x_801_ == 0)
{
uint32_t v___x_802_; uint8_t v___x_803_; 
v___x_802_ = 57343;
v___x_803_ = lean_uint32_dec_lt(v___x_802_, v_r_797_);
if (v___x_803_ == 0)
{
return v___y_783_;
}
else
{
return v___x_727_;
}
}
else
{
return v___x_727_;
}
}
}
else
{
return v___x_724_;
}
}
}
}
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_810_ = lean_unsigned_to_nat(1u);
v___x_811_ = lean_nat_add(v_i_713_, v___x_810_);
v___x_812_ = lean_nat_dec_lt(v___x_811_, v___x_714_);
if (v___x_812_ == 0)
{
lean_dec(v___x_811_);
return v___x_720_;
}
else
{
uint8_t v___x_813_; uint8_t v___x_814_; uint8_t v___x_815_; uint8_t v___x_816_; 
v___x_813_ = lean_byte_array_fget(v_bytes_712_, v___x_811_);
lean_dec(v___x_811_);
v___x_814_ = lean_uint8_land(v___x_813_, v___x_723_);
v___x_815_ = lean_uint8_dec_eq(v___x_814_, v___x_717_);
v___x_816_ = lean_bool_not(v___x_815_);
if (v___x_816_ == 0)
{
uint8_t v___x_817_; uint8_t v_b_u2080_818_; uint8_t v___x_819_; uint8_t v_b_u2081_820_; uint32_t v___x_821_; uint32_t v___x_822_; uint32_t v___x_823_; uint32_t v___x_824_; uint32_t v_r_825_; uint32_t v___x_826_; uint8_t v___x_827_; 
v___x_817_ = 31;
v_b_u2080_818_ = lean_uint8_land(v___x_716_, v___x_817_);
v___x_819_ = 63;
v_b_u2081_820_ = lean_uint8_land(v___x_813_, v___x_819_);
v___x_821_ = lean_uint8_to_uint32(v_b_u2080_818_);
v___x_822_ = 6;
v___x_823_ = lean_uint32_shift_left(v___x_821_, v___x_822_);
v___x_824_ = lean_uint8_to_uint32(v_b_u2081_820_);
v_r_825_ = lean_uint32_lor(v___x_823_, v___x_824_);
v___x_826_ = 128;
v___x_827_ = lean_uint32_dec_le(v___x_826_, v_r_825_);
return v___x_827_;
}
else
{
return v___x_720_;
}
}
}
}
else
{
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8At___boxed(lean_object* v_bytes_828_, lean_object* v_i_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l_ByteArray_validateUTF8At(v_bytes_828_, v_i_829_);
lean_dec(v_i_829_);
lean_dec_ref(v_bytes_828_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t v_x_832_, lean_object* v_h__1_833_, lean_object* v_h__2_834_, lean_object* v_h__3_835_, lean_object* v_h__4_836_, lean_object* v_h__5_837_){
_start:
{
switch(v_x_832_)
{
case 0:
{
lean_object* v___x_838_; 
lean_dec(v_h__5_837_);
lean_dec(v_h__4_836_);
lean_dec(v_h__3_835_);
lean_dec(v_h__2_834_);
v___x_838_ = lean_apply_1(v_h__1_833_, lean_box(0));
return v___x_838_;
}
case 1:
{
lean_object* v___x_839_; 
lean_dec(v_h__5_837_);
lean_dec(v_h__4_836_);
lean_dec(v_h__3_835_);
lean_dec(v_h__1_833_);
v___x_839_ = lean_apply_1(v_h__2_834_, lean_box(0));
return v___x_839_;
}
case 2:
{
lean_object* v___x_840_; 
lean_dec(v_h__5_837_);
lean_dec(v_h__4_836_);
lean_dec(v_h__2_834_);
lean_dec(v_h__1_833_);
v___x_840_ = lean_apply_1(v_h__3_835_, lean_box(0));
return v___x_840_;
}
case 3:
{
lean_object* v___x_841_; 
lean_dec(v_h__5_837_);
lean_dec(v_h__3_835_);
lean_dec(v_h__2_834_);
lean_dec(v_h__1_833_);
v___x_841_ = lean_apply_1(v_h__4_836_, lean_box(0));
return v___x_841_;
}
default: 
{
lean_object* v___x_842_; 
lean_dec(v_h__4_836_);
lean_dec(v_h__3_835_);
lean_dec(v_h__2_834_);
lean_dec(v_h__1_833_);
v___x_842_ = lean_apply_1(v_h__5_837_, lean_box(0));
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_843_, lean_object* v_h__1_844_, lean_object* v_h__2_845_, lean_object* v_h__3_846_, lean_object* v_h__4_847_, lean_object* v_h__5_848_){
_start:
{
uint8_t v_x_47__boxed_849_; lean_object* v_res_850_; 
v_x_47__boxed_849_ = lean_unbox(v_x_843_);
v_res_850_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(v_x_47__boxed_849_, v_h__1_844_, v_h__2_845_, v_h__3_846_, v_h__4_847_, v_h__5_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object* v_motive_851_, uint8_t v_x_852_, lean_object* v_h__1_853_, lean_object* v_h__2_854_, lean_object* v_h__3_855_, lean_object* v_h__4_856_, lean_object* v_h__5_857_){
_start:
{
switch(v_x_852_)
{
case 0:
{
lean_object* v___x_858_; 
lean_dec(v_h__5_857_);
lean_dec(v_h__4_856_);
lean_dec(v_h__3_855_);
lean_dec(v_h__2_854_);
v___x_858_ = lean_apply_1(v_h__1_853_, lean_box(0));
return v___x_858_;
}
case 1:
{
lean_object* v___x_859_; 
lean_dec(v_h__5_857_);
lean_dec(v_h__4_856_);
lean_dec(v_h__3_855_);
lean_dec(v_h__1_853_);
v___x_859_ = lean_apply_1(v_h__2_854_, lean_box(0));
return v___x_859_;
}
case 2:
{
lean_object* v___x_860_; 
lean_dec(v_h__5_857_);
lean_dec(v_h__4_856_);
lean_dec(v_h__2_854_);
lean_dec(v_h__1_853_);
v___x_860_ = lean_apply_1(v_h__3_855_, lean_box(0));
return v___x_860_;
}
case 3:
{
lean_object* v___x_861_; 
lean_dec(v_h__5_857_);
lean_dec(v_h__3_855_);
lean_dec(v_h__2_854_);
lean_dec(v_h__1_853_);
v___x_861_ = lean_apply_1(v_h__4_856_, lean_box(0));
return v___x_861_;
}
default: 
{
lean_object* v___x_862_; 
lean_dec(v_h__4_856_);
lean_dec(v_h__3_855_);
lean_dec(v_h__2_854_);
lean_dec(v_h__1_853_);
v___x_862_ = lean_apply_1(v_h__5_857_, lean_box(0));
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object* v_motive_863_, lean_object* v_x_864_, lean_object* v_h__1_865_, lean_object* v_h__2_866_, lean_object* v_h__3_867_, lean_object* v_h__4_868_, lean_object* v_h__5_869_){
_start:
{
uint8_t v_x_60__boxed_870_; lean_object* v_res_871_; 
v_x_60__boxed_870_ = lean_unbox(v_x_864_);
v_res_871_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(v_motive_863_, v_x_60__boxed_870_, v_h__1_865_, v_h__2_866_, v_h__3_867_, v_h__4_868_, v_h__5_869_);
return v_res_871_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar___redArg(lean_object* v_bytes_872_, lean_object* v_i_873_){
_start:
{
lean_object* v___x_874_; uint8_t v___x_875_; uint8_t v___x_876_; uint8_t v___x_877_; uint8_t v___x_878_; uint8_t v___x_879_; uint8_t v___x_880_; 
v___x_874_ = lean_byte_array_size(v_bytes_872_);
v___x_875_ = lean_nat_dec_lt(v_i_873_, v___x_874_);
v___x_876_ = lean_byte_array_fget(v_bytes_872_, v_i_873_);
v___x_877_ = 128;
v___x_878_ = lean_uint8_land(v___x_876_, v___x_877_);
v___x_879_ = 0;
v___x_880_ = lean_uint8_dec_eq(v___x_878_, v___x_879_);
if (v___x_880_ == 0)
{
uint8_t v___x_881_; uint8_t v___x_882_; uint8_t v___x_883_; uint8_t v___x_884_; 
v___x_881_ = 224;
v___x_882_ = lean_uint8_land(v___x_876_, v___x_881_);
v___x_883_ = 192;
v___x_884_ = lean_uint8_dec_eq(v___x_882_, v___x_883_);
if (v___x_884_ == 0)
{
uint8_t v___x_885_; uint8_t v___x_886_; uint8_t v___x_887_; 
v___x_885_ = 240;
v___x_886_ = lean_uint8_land(v___x_876_, v___x_885_);
v___x_887_ = lean_uint8_dec_eq(v___x_886_, v___x_881_);
if (v___x_887_ == 0)
{
uint8_t v___x_888_; uint8_t v___x_889_; uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; uint8_t v___x_900_; uint8_t v___y_902_; uint8_t v___x_929_; uint8_t v___x_930_; uint8_t v___x_931_; 
v___x_888_ = 248;
v___x_889_ = lean_uint8_land(v___x_876_, v___x_888_);
v___x_890_ = lean_uint8_dec_eq(v___x_889_, v___x_885_);
v___x_891_ = lean_unsigned_to_nat(3u);
v___x_892_ = lean_nat_add(v_i_873_, v___x_891_);
v___x_893_ = lean_nat_dec_lt(v___x_892_, v___x_874_);
v___x_894_ = lean_unsigned_to_nat(1u);
v___x_895_ = lean_nat_add(v_i_873_, v___x_894_);
v___x_896_ = lean_byte_array_fget(v_bytes_872_, v___x_895_);
lean_dec(v___x_895_);
v___x_897_ = lean_unsigned_to_nat(2u);
v___x_898_ = lean_nat_add(v_i_873_, v___x_897_);
v___x_899_ = lean_byte_array_fget(v_bytes_872_, v___x_898_);
lean_dec(v___x_898_);
v___x_900_ = lean_byte_array_fget(v_bytes_872_, v___x_892_);
lean_dec(v___x_892_);
v___x_929_ = lean_uint8_land(v___x_896_, v___x_883_);
v___x_930_ = lean_uint8_dec_eq(v___x_929_, v___x_877_);
v___x_931_ = lean_bool_not(v___x_930_);
if (v___x_931_ == 0)
{
uint8_t v___x_932_; uint8_t v___x_933_; uint8_t v___x_934_; 
v___x_932_ = lean_uint8_land(v___x_899_, v___x_883_);
v___x_933_ = lean_uint8_dec_eq(v___x_932_, v___x_877_);
v___x_934_ = lean_bool_not(v___x_933_);
v___y_902_ = v___x_934_;
goto v___jp_901_;
}
else
{
v___y_902_ = v___x_931_;
goto v___jp_901_;
}
v___jp_901_:
{
uint8_t v___x_903_; uint8_t v___x_904_; uint8_t v___x_905_; uint8_t v___x_906_; uint8_t v_b_u2080_907_; uint8_t v___x_908_; uint8_t v_b_u2081_909_; uint8_t v_b_u2082_910_; uint8_t v_b_u2083_911_; uint32_t v___x_912_; uint32_t v___x_913_; uint32_t v___x_914_; uint32_t v___x_915_; uint32_t v___x_916_; uint32_t v___x_917_; uint32_t v___x_918_; uint32_t v___x_919_; uint32_t v___x_920_; uint32_t v___x_921_; uint32_t v___x_922_; uint32_t v___x_923_; uint32_t v_r_924_; uint32_t v___x_925_; uint8_t v___x_926_; uint32_t v___x_927_; uint8_t v___x_928_; 
v___x_903_ = lean_uint8_land(v___x_900_, v___x_883_);
v___x_904_ = lean_uint8_dec_eq(v___x_903_, v___x_877_);
v___x_905_ = lean_bool_not(v___x_904_);
v___x_906_ = 7;
v_b_u2080_907_ = lean_uint8_land(v___x_876_, v___x_906_);
v___x_908_ = 63;
v_b_u2081_909_ = lean_uint8_land(v___x_896_, v___x_908_);
v_b_u2082_910_ = lean_uint8_land(v___x_899_, v___x_908_);
v_b_u2083_911_ = lean_uint8_land(v___x_900_, v___x_908_);
v___x_912_ = lean_uint8_to_uint32(v_b_u2080_907_);
v___x_913_ = 18;
v___x_914_ = lean_uint32_shift_left(v___x_912_, v___x_913_);
v___x_915_ = lean_uint8_to_uint32(v_b_u2081_909_);
v___x_916_ = 12;
v___x_917_ = lean_uint32_shift_left(v___x_915_, v___x_916_);
v___x_918_ = lean_uint32_lor(v___x_914_, v___x_917_);
v___x_919_ = lean_uint8_to_uint32(v_b_u2082_910_);
v___x_920_ = 6;
v___x_921_ = lean_uint32_shift_left(v___x_919_, v___x_920_);
v___x_922_ = lean_uint32_lor(v___x_918_, v___x_921_);
v___x_923_ = lean_uint8_to_uint32(v_b_u2083_911_);
v_r_924_ = lean_uint32_lor(v___x_922_, v___x_923_);
v___x_925_ = 65536;
v___x_926_ = lean_uint32_dec_lt(v_r_924_, v___x_925_);
v___x_927_ = 1114111;
v___x_928_ = lean_uint32_dec_lt(v___x_927_, v_r_924_);
return v_r_924_;
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; uint8_t v___x_941_; uint8_t v___y_943_; uint8_t v___x_964_; uint8_t v___x_965_; uint8_t v___x_966_; 
v___x_935_ = lean_unsigned_to_nat(2u);
v___x_936_ = lean_nat_add(v_i_873_, v___x_935_);
v___x_937_ = lean_nat_dec_lt(v___x_936_, v___x_874_);
v___x_938_ = lean_unsigned_to_nat(1u);
v___x_939_ = lean_nat_add(v_i_873_, v___x_938_);
v___x_940_ = lean_byte_array_fget(v_bytes_872_, v___x_939_);
lean_dec(v___x_939_);
v___x_941_ = lean_byte_array_fget(v_bytes_872_, v___x_936_);
lean_dec(v___x_936_);
v___x_964_ = lean_uint8_land(v___x_940_, v___x_883_);
v___x_965_ = lean_uint8_dec_eq(v___x_964_, v___x_877_);
v___x_966_ = lean_bool_not(v___x_965_);
if (v___x_966_ == 0)
{
uint8_t v___x_967_; uint8_t v___x_968_; uint8_t v___x_969_; 
v___x_967_ = lean_uint8_land(v___x_941_, v___x_883_);
v___x_968_ = lean_uint8_dec_eq(v___x_967_, v___x_877_);
v___x_969_ = lean_bool_not(v___x_968_);
v___y_943_ = v___x_969_;
goto v___jp_942_;
}
else
{
v___y_943_ = v___x_966_;
goto v___jp_942_;
}
v___jp_942_:
{
uint8_t v___x_944_; uint8_t v_b_u2080_945_; uint8_t v___x_946_; uint8_t v_b_u2081_947_; uint8_t v_b_u2082_948_; uint32_t v___x_949_; uint32_t v___x_950_; uint32_t v___x_951_; uint32_t v___x_952_; uint32_t v___x_953_; uint32_t v___x_954_; uint32_t v___x_955_; uint32_t v___x_956_; uint32_t v_r_957_; uint32_t v___x_958_; uint8_t v___x_959_; uint32_t v___x_960_; uint8_t v___x_961_; 
v___x_944_ = 15;
v_b_u2080_945_ = lean_uint8_land(v___x_876_, v___x_944_);
v___x_946_ = 63;
v_b_u2081_947_ = lean_uint8_land(v___x_940_, v___x_946_);
v_b_u2082_948_ = lean_uint8_land(v___x_941_, v___x_946_);
v___x_949_ = lean_uint8_to_uint32(v_b_u2080_945_);
v___x_950_ = 12;
v___x_951_ = lean_uint32_shift_left(v___x_949_, v___x_950_);
v___x_952_ = lean_uint8_to_uint32(v_b_u2081_947_);
v___x_953_ = 6;
v___x_954_ = lean_uint32_shift_left(v___x_952_, v___x_953_);
v___x_955_ = lean_uint32_lor(v___x_951_, v___x_954_);
v___x_956_ = lean_uint8_to_uint32(v_b_u2082_948_);
v_r_957_ = lean_uint32_lor(v___x_955_, v___x_956_);
v___x_958_ = 2048;
v___x_959_ = lean_uint32_dec_lt(v_r_957_, v___x_958_);
v___x_960_ = 55296;
v___x_961_ = lean_uint32_dec_le(v___x_960_, v_r_957_);
if (v___x_961_ == 0)
{
return v_r_957_;
}
else
{
uint32_t v___x_962_; uint8_t v___x_963_; 
v___x_962_ = 57343;
v___x_963_ = lean_uint32_dec_le(v_r_957_, v___x_962_);
return v_r_957_;
}
}
}
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; uint8_t v___x_973_; uint8_t v___x_974_; uint8_t v___x_975_; uint8_t v___x_976_; uint8_t v___x_977_; uint8_t v_b_u2080_978_; uint8_t v___x_979_; uint8_t v_b_u2081_980_; uint32_t v___x_981_; uint32_t v___x_982_; uint32_t v___x_983_; uint32_t v___x_984_; uint32_t v_r_985_; uint32_t v___x_986_; uint8_t v___x_987_; 
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = lean_nat_add(v_i_873_, v___x_970_);
v___x_972_ = lean_nat_dec_lt(v___x_971_, v___x_874_);
v___x_973_ = lean_byte_array_fget(v_bytes_872_, v___x_971_);
lean_dec(v___x_971_);
v___x_974_ = lean_uint8_land(v___x_973_, v___x_883_);
v___x_975_ = lean_uint8_dec_eq(v___x_974_, v___x_877_);
v___x_976_ = lean_bool_not(v___x_975_);
v___x_977_ = 31;
v_b_u2080_978_ = lean_uint8_land(v___x_876_, v___x_977_);
v___x_979_ = 63;
v_b_u2081_980_ = lean_uint8_land(v___x_973_, v___x_979_);
v___x_981_ = lean_uint8_to_uint32(v_b_u2080_978_);
v___x_982_ = 6;
v___x_983_ = lean_uint32_shift_left(v___x_981_, v___x_982_);
v___x_984_ = lean_uint8_to_uint32(v_b_u2081_980_);
v_r_985_ = lean_uint32_lor(v___x_983_, v___x_984_);
v___x_986_ = 128;
v___x_987_ = lean_uint32_dec_lt(v_r_985_, v___x_986_);
return v_r_985_;
}
}
else
{
uint32_t v___x_988_; 
v___x_988_ = lean_uint8_to_uint32(v___x_876_);
return v___x_988_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___redArg___boxed(lean_object* v_bytes_989_, lean_object* v_i_990_){
_start:
{
uint32_t v_res_991_; lean_object* v_r_992_; 
v_res_991_ = l_ByteArray_utf8DecodeChar___redArg(v_bytes_989_, v_i_990_);
lean_dec(v_i_990_);
lean_dec_ref(v_bytes_989_);
v_r_992_ = lean_box_uint32(v_res_991_);
return v_r_992_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar(lean_object* v_bytes_993_, lean_object* v_i_994_, lean_object* v_h_995_){
_start:
{
lean_object* v___x_996_; uint8_t v___x_997_; uint8_t v___x_998_; uint8_t v___x_999_; uint8_t v___x_1000_; uint8_t v___x_1001_; uint8_t v___x_1002_; 
v___x_996_ = lean_byte_array_size(v_bytes_993_);
v___x_997_ = lean_nat_dec_lt(v_i_994_, v___x_996_);
v___x_998_ = lean_byte_array_fget(v_bytes_993_, v_i_994_);
v___x_999_ = 128;
v___x_1000_ = lean_uint8_land(v___x_998_, v___x_999_);
v___x_1001_ = 0;
v___x_1002_ = lean_uint8_dec_eq(v___x_1000_, v___x_1001_);
if (v___x_1002_ == 0)
{
uint8_t v___x_1003_; uint8_t v___x_1004_; uint8_t v___x_1005_; uint8_t v___x_1006_; 
v___x_1003_ = 224;
v___x_1004_ = lean_uint8_land(v___x_998_, v___x_1003_);
v___x_1005_ = 192;
v___x_1006_ = lean_uint8_dec_eq(v___x_1004_, v___x_1005_);
if (v___x_1006_ == 0)
{
uint8_t v___x_1007_; uint8_t v___x_1008_; uint8_t v___x_1009_; 
v___x_1007_ = 240;
v___x_1008_ = lean_uint8_land(v___x_998_, v___x_1007_);
v___x_1009_ = lean_uint8_dec_eq(v___x_1008_, v___x_1003_);
if (v___x_1009_ == 0)
{
uint8_t v___x_1010_; uint8_t v___x_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; uint8_t v___x_1022_; uint8_t v___y_1024_; uint8_t v___x_1051_; uint8_t v___x_1052_; uint8_t v___x_1053_; 
v___x_1010_ = 248;
v___x_1011_ = lean_uint8_land(v___x_998_, v___x_1010_);
v___x_1012_ = lean_uint8_dec_eq(v___x_1011_, v___x_1007_);
v___x_1013_ = lean_unsigned_to_nat(3u);
v___x_1014_ = lean_nat_add(v_i_994_, v___x_1013_);
v___x_1015_ = lean_nat_dec_lt(v___x_1014_, v___x_996_);
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_nat_add(v_i_994_, v___x_1016_);
v___x_1018_ = lean_byte_array_fget(v_bytes_993_, v___x_1017_);
lean_dec(v___x_1017_);
v___x_1019_ = lean_unsigned_to_nat(2u);
v___x_1020_ = lean_nat_add(v_i_994_, v___x_1019_);
v___x_1021_ = lean_byte_array_fget(v_bytes_993_, v___x_1020_);
lean_dec(v___x_1020_);
v___x_1022_ = lean_byte_array_fget(v_bytes_993_, v___x_1014_);
lean_dec(v___x_1014_);
v___x_1051_ = lean_uint8_land(v___x_1018_, v___x_1005_);
v___x_1052_ = lean_uint8_dec_eq(v___x_1051_, v___x_999_);
v___x_1053_ = lean_bool_not(v___x_1052_);
if (v___x_1053_ == 0)
{
uint8_t v___x_1054_; uint8_t v___x_1055_; uint8_t v___x_1056_; 
v___x_1054_ = lean_uint8_land(v___x_1021_, v___x_1005_);
v___x_1055_ = lean_uint8_dec_eq(v___x_1054_, v___x_999_);
v___x_1056_ = lean_bool_not(v___x_1055_);
v___y_1024_ = v___x_1056_;
goto v___jp_1023_;
}
else
{
v___y_1024_ = v___x_1053_;
goto v___jp_1023_;
}
v___jp_1023_:
{
uint8_t v___x_1025_; uint8_t v___x_1026_; uint8_t v___x_1027_; uint8_t v___x_1028_; uint8_t v_b_u2080_1029_; uint8_t v___x_1030_; uint8_t v_b_u2081_1031_; uint8_t v_b_u2082_1032_; uint8_t v_b_u2083_1033_; uint32_t v___x_1034_; uint32_t v___x_1035_; uint32_t v___x_1036_; uint32_t v___x_1037_; uint32_t v___x_1038_; uint32_t v___x_1039_; uint32_t v___x_1040_; uint32_t v___x_1041_; uint32_t v___x_1042_; uint32_t v___x_1043_; uint32_t v___x_1044_; uint32_t v___x_1045_; uint32_t v_r_1046_; uint32_t v___x_1047_; uint8_t v___x_1048_; uint32_t v___x_1049_; uint8_t v___x_1050_; 
v___x_1025_ = lean_uint8_land(v___x_1022_, v___x_1005_);
v___x_1026_ = lean_uint8_dec_eq(v___x_1025_, v___x_999_);
v___x_1027_ = lean_bool_not(v___x_1026_);
v___x_1028_ = 7;
v_b_u2080_1029_ = lean_uint8_land(v___x_998_, v___x_1028_);
v___x_1030_ = 63;
v_b_u2081_1031_ = lean_uint8_land(v___x_1018_, v___x_1030_);
v_b_u2082_1032_ = lean_uint8_land(v___x_1021_, v___x_1030_);
v_b_u2083_1033_ = lean_uint8_land(v___x_1022_, v___x_1030_);
v___x_1034_ = lean_uint8_to_uint32(v_b_u2080_1029_);
v___x_1035_ = 18;
v___x_1036_ = lean_uint32_shift_left(v___x_1034_, v___x_1035_);
v___x_1037_ = lean_uint8_to_uint32(v_b_u2081_1031_);
v___x_1038_ = 12;
v___x_1039_ = lean_uint32_shift_left(v___x_1037_, v___x_1038_);
v___x_1040_ = lean_uint32_lor(v___x_1036_, v___x_1039_);
v___x_1041_ = lean_uint8_to_uint32(v_b_u2082_1032_);
v___x_1042_ = 6;
v___x_1043_ = lean_uint32_shift_left(v___x_1041_, v___x_1042_);
v___x_1044_ = lean_uint32_lor(v___x_1040_, v___x_1043_);
v___x_1045_ = lean_uint8_to_uint32(v_b_u2083_1033_);
v_r_1046_ = lean_uint32_lor(v___x_1044_, v___x_1045_);
v___x_1047_ = 65536;
v___x_1048_ = lean_uint32_dec_lt(v_r_1046_, v___x_1047_);
v___x_1049_ = 1114111;
v___x_1050_ = lean_uint32_dec_lt(v___x_1049_, v_r_1046_);
return v_r_1046_;
}
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; uint8_t v___x_1063_; uint8_t v___y_1065_; uint8_t v___x_1086_; uint8_t v___x_1087_; uint8_t v___x_1088_; 
v___x_1057_ = lean_unsigned_to_nat(2u);
v___x_1058_ = lean_nat_add(v_i_994_, v___x_1057_);
v___x_1059_ = lean_nat_dec_lt(v___x_1058_, v___x_996_);
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1061_ = lean_nat_add(v_i_994_, v___x_1060_);
v___x_1062_ = lean_byte_array_fget(v_bytes_993_, v___x_1061_);
lean_dec(v___x_1061_);
v___x_1063_ = lean_byte_array_fget(v_bytes_993_, v___x_1058_);
lean_dec(v___x_1058_);
v___x_1086_ = lean_uint8_land(v___x_1062_, v___x_1005_);
v___x_1087_ = lean_uint8_dec_eq(v___x_1086_, v___x_999_);
v___x_1088_ = lean_bool_not(v___x_1087_);
if (v___x_1088_ == 0)
{
uint8_t v___x_1089_; uint8_t v___x_1090_; uint8_t v___x_1091_; 
v___x_1089_ = lean_uint8_land(v___x_1063_, v___x_1005_);
v___x_1090_ = lean_uint8_dec_eq(v___x_1089_, v___x_999_);
v___x_1091_ = lean_bool_not(v___x_1090_);
v___y_1065_ = v___x_1091_;
goto v___jp_1064_;
}
else
{
v___y_1065_ = v___x_1088_;
goto v___jp_1064_;
}
v___jp_1064_:
{
uint8_t v___x_1066_; uint8_t v_b_u2080_1067_; uint8_t v___x_1068_; uint8_t v_b_u2081_1069_; uint8_t v_b_u2082_1070_; uint32_t v___x_1071_; uint32_t v___x_1072_; uint32_t v___x_1073_; uint32_t v___x_1074_; uint32_t v___x_1075_; uint32_t v___x_1076_; uint32_t v___x_1077_; uint32_t v___x_1078_; uint32_t v_r_1079_; uint32_t v___x_1080_; uint8_t v___x_1081_; uint32_t v___x_1082_; uint8_t v___x_1083_; 
v___x_1066_ = 15;
v_b_u2080_1067_ = lean_uint8_land(v___x_998_, v___x_1066_);
v___x_1068_ = 63;
v_b_u2081_1069_ = lean_uint8_land(v___x_1062_, v___x_1068_);
v_b_u2082_1070_ = lean_uint8_land(v___x_1063_, v___x_1068_);
v___x_1071_ = lean_uint8_to_uint32(v_b_u2080_1067_);
v___x_1072_ = 12;
v___x_1073_ = lean_uint32_shift_left(v___x_1071_, v___x_1072_);
v___x_1074_ = lean_uint8_to_uint32(v_b_u2081_1069_);
v___x_1075_ = 6;
v___x_1076_ = lean_uint32_shift_left(v___x_1074_, v___x_1075_);
v___x_1077_ = lean_uint32_lor(v___x_1073_, v___x_1076_);
v___x_1078_ = lean_uint8_to_uint32(v_b_u2082_1070_);
v_r_1079_ = lean_uint32_lor(v___x_1077_, v___x_1078_);
v___x_1080_ = 2048;
v___x_1081_ = lean_uint32_dec_lt(v_r_1079_, v___x_1080_);
v___x_1082_ = 55296;
v___x_1083_ = lean_uint32_dec_le(v___x_1082_, v_r_1079_);
if (v___x_1083_ == 0)
{
return v_r_1079_;
}
else
{
uint32_t v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = 57343;
v___x_1085_ = lean_uint32_dec_le(v_r_1079_, v___x_1084_);
return v_r_1079_;
}
}
}
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; uint8_t v___x_1095_; uint8_t v___x_1096_; uint8_t v___x_1097_; uint8_t v___x_1098_; uint8_t v___x_1099_; uint8_t v_b_u2080_1100_; uint8_t v___x_1101_; uint8_t v_b_u2081_1102_; uint32_t v___x_1103_; uint32_t v___x_1104_; uint32_t v___x_1105_; uint32_t v___x_1106_; uint32_t v_r_1107_; uint32_t v___x_1108_; uint8_t v___x_1109_; 
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = lean_nat_add(v_i_994_, v___x_1092_);
v___x_1094_ = lean_nat_dec_lt(v___x_1093_, v___x_996_);
v___x_1095_ = lean_byte_array_fget(v_bytes_993_, v___x_1093_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_uint8_land(v___x_1095_, v___x_1005_);
v___x_1097_ = lean_uint8_dec_eq(v___x_1096_, v___x_999_);
v___x_1098_ = lean_bool_not(v___x_1097_);
v___x_1099_ = 31;
v_b_u2080_1100_ = lean_uint8_land(v___x_998_, v___x_1099_);
v___x_1101_ = 63;
v_b_u2081_1102_ = lean_uint8_land(v___x_1095_, v___x_1101_);
v___x_1103_ = lean_uint8_to_uint32(v_b_u2080_1100_);
v___x_1104_ = 6;
v___x_1105_ = lean_uint32_shift_left(v___x_1103_, v___x_1104_);
v___x_1106_ = lean_uint8_to_uint32(v_b_u2081_1102_);
v_r_1107_ = lean_uint32_lor(v___x_1105_, v___x_1106_);
v___x_1108_ = 128;
v___x_1109_ = lean_uint32_dec_lt(v_r_1107_, v___x_1108_);
return v_r_1107_;
}
}
else
{
uint32_t v___x_1110_; 
v___x_1110_ = lean_uint8_to_uint32(v___x_998_);
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___boxed(lean_object* v_bytes_1111_, lean_object* v_i_1112_, lean_object* v_h_1113_){
_start:
{
uint32_t v_res_1114_; lean_object* v_r_1115_; 
v_res_1114_ = l_ByteArray_utf8DecodeChar(v_bytes_1111_, v_i_1112_, v_h_1113_);
lean_dec(v_i_1112_);
lean_dec_ref(v_bytes_1111_);
v_r_1115_ = lean_box_uint32(v_res_1114_);
return v_r_1115_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableIsUTF8FirstByte___aux__1(uint8_t v_c_1116_){
_start:
{
uint8_t v___x_1117_; uint8_t v___x_1118_; uint8_t v___x_1119_; uint8_t v___x_1120_; 
v___x_1117_ = 128;
v___x_1118_ = lean_uint8_land(v_c_1116_, v___x_1117_);
v___x_1119_ = 0;
v___x_1120_ = lean_uint8_dec_eq(v___x_1118_, v___x_1119_);
if (v___x_1120_ == 0)
{
uint8_t v___x_1121_; uint8_t v___x_1122_; uint8_t v___x_1123_; uint8_t v___x_1124_; 
v___x_1121_ = 224;
v___x_1122_ = lean_uint8_land(v_c_1116_, v___x_1121_);
v___x_1123_ = 192;
v___x_1124_ = lean_uint8_dec_eq(v___x_1122_, v___x_1123_);
if (v___x_1124_ == 0)
{
uint8_t v___x_1125_; uint8_t v___x_1126_; uint8_t v___x_1127_; 
v___x_1125_ = 240;
v___x_1126_ = lean_uint8_land(v_c_1116_, v___x_1125_);
v___x_1127_ = lean_uint8_dec_eq(v___x_1126_, v___x_1121_);
if (v___x_1127_ == 0)
{
uint8_t v___x_1128_; uint8_t v___x_1129_; uint8_t v___x_1130_; 
v___x_1128_ = 248;
v___x_1129_ = lean_uint8_land(v_c_1116_, v___x_1128_);
v___x_1130_ = lean_uint8_dec_eq(v___x_1129_, v___x_1125_);
return v___x_1130_;
}
else
{
return v___x_1127_;
}
}
else
{
return v___x_1124_;
}
}
else
{
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableIsUTF8FirstByte___aux__1___boxed(lean_object* v_c_1131_){
_start:
{
uint8_t v_c_boxed_1132_; uint8_t v_res_1133_; lean_object* v_r_1134_; 
v_c_boxed_1132_ = lean_unbox(v_c_1131_);
v_res_1133_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v_c_boxed_1132_);
v_r_1134_ = lean_box(v_res_1133_);
return v_r_1134_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableIsUTF8FirstByte(uint8_t v___y_1135_){
_start:
{
uint8_t v___x_1136_; 
v___x_1136_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v___y_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableIsUTF8FirstByte___boxed(lean_object* v___y_1137_){
_start:
{
uint8_t v___y_4__boxed_1138_; uint8_t v_res_1139_; lean_object* v_r_1140_; 
v___y_4__boxed_1138_ = lean_unbox(v___y_1137_);
v_res_1139_ = l_UInt8_instDecidableIsUTF8FirstByte(v___y_4__boxed_1138_);
v_r_1140_ = lean_box(v_res_1139_);
return v_r_1140_;
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg(uint8_t v_c_1141_){
_start:
{
uint8_t v___x_1142_; uint8_t v___x_1143_; uint8_t v___x_1144_; uint8_t v___x_1145_; 
v___x_1142_ = 128;
v___x_1143_ = lean_uint8_land(v_c_1141_, v___x_1142_);
v___x_1144_ = 0;
v___x_1145_ = lean_uint8_dec_eq(v___x_1143_, v___x_1144_);
if (v___x_1145_ == 0)
{
uint8_t v___x_1146_; uint8_t v___x_1147_; uint8_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1146_ = 224;
v___x_1147_ = lean_uint8_land(v_c_1141_, v___x_1146_);
v___x_1148_ = 192;
v___x_1149_ = lean_uint8_dec_eq(v___x_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
uint8_t v___x_1150_; uint8_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = 240;
v___x_1151_ = lean_uint8_land(v_c_1141_, v___x_1150_);
v___x_1152_ = lean_uint8_dec_eq(v___x_1151_, v___x_1146_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_unsigned_to_nat(4u);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_unsigned_to_nat(3u);
return v___x_1154_;
}
}
else
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_unsigned_to_nat(2u);
return v___x_1155_;
}
}
else
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_unsigned_to_nat(1u);
return v___x_1156_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg___boxed(lean_object* v_c_1157_){
_start:
{
uint8_t v_c_boxed_1158_; lean_object* v_res_1159_; 
v_c_boxed_1158_ = lean_unbox(v_c_1157_);
v_res_1159_ = l_UInt8_utf8ByteSize___redArg(v_c_boxed_1158_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize(uint8_t v_c_1160_, lean_object* v___h_1161_){
_start:
{
uint8_t v___x_1162_; uint8_t v___x_1163_; uint8_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1162_ = 128;
v___x_1163_ = lean_uint8_land(v_c_1160_, v___x_1162_);
v___x_1164_ = 0;
v___x_1165_ = lean_uint8_dec_eq(v___x_1163_, v___x_1164_);
if (v___x_1165_ == 0)
{
uint8_t v___x_1166_; uint8_t v___x_1167_; uint8_t v___x_1168_; uint8_t v___x_1169_; 
v___x_1166_ = 224;
v___x_1167_ = lean_uint8_land(v_c_1160_, v___x_1166_);
v___x_1168_ = 192;
v___x_1169_ = lean_uint8_dec_eq(v___x_1167_, v___x_1168_);
if (v___x_1169_ == 0)
{
uint8_t v___x_1170_; uint8_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1170_ = 240;
v___x_1171_ = lean_uint8_land(v_c_1160_, v___x_1170_);
v___x_1172_ = lean_uint8_dec_eq(v___x_1171_, v___x_1166_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_unsigned_to_nat(4u);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_unsigned_to_nat(3u);
return v___x_1174_;
}
}
else
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_unsigned_to_nat(2u);
return v___x_1175_;
}
}
else
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_unsigned_to_nat(1u);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___boxed(lean_object* v_c_1177_, lean_object* v___h_1178_){
_start:
{
uint8_t v_c_boxed_1179_; lean_object* v_res_1180_; 
v_c_boxed_1179_ = lean_unbox(v_c_1177_);
v_res_1180_ = l_UInt8_utf8ByteSize(v_c_boxed_1179_, v___h_1178_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(uint8_t v_x_1181_){
_start:
{
switch(v_x_1181_)
{
case 0:
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_unsigned_to_nat(0u);
return v___x_1182_;
}
case 1:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_unsigned_to_nat(1u);
return v___x_1183_;
}
case 2:
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_unsigned_to_nat(2u);
return v___x_1184_;
}
case 3:
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_unsigned_to_nat(3u);
return v___x_1185_;
}
default: 
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_unsigned_to_nat(4u);
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize___boxed(lean_object* v_x_1187_){
_start:
{
uint8_t v_x_54__boxed_1188_; lean_object* v_res_1189_; 
v_x_54__boxed_1188_ = lean_unbox(v_x_1187_);
v_res_1189_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(v_x_54__boxed_1188_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(uint8_t v_x_1190_, lean_object* v_h__1_1191_, lean_object* v_h__2_1192_, lean_object* v_h__3_1193_, lean_object* v_h__4_1194_, lean_object* v_h__5_1195_){
_start:
{
switch(v_x_1190_)
{
case 0:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec(v_h__5_1195_);
lean_dec(v_h__4_1194_);
lean_dec(v_h__3_1193_);
lean_dec(v_h__2_1192_);
v___x_1196_ = lean_box(0);
v___x_1197_ = lean_apply_1(v_h__1_1191_, v___x_1196_);
return v___x_1197_;
}
case 1:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_dec(v_h__5_1195_);
lean_dec(v_h__4_1194_);
lean_dec(v_h__3_1193_);
lean_dec(v_h__1_1191_);
v___x_1198_ = lean_box(0);
v___x_1199_ = lean_apply_1(v_h__2_1192_, v___x_1198_);
return v___x_1199_;
}
case 2:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_dec(v_h__5_1195_);
lean_dec(v_h__4_1194_);
lean_dec(v_h__2_1192_);
lean_dec(v_h__1_1191_);
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_apply_1(v_h__3_1193_, v___x_1200_);
return v___x_1201_;
}
case 3:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_dec(v_h__5_1195_);
lean_dec(v_h__3_1193_);
lean_dec(v_h__2_1192_);
lean_dec(v_h__1_1191_);
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_apply_1(v_h__4_1194_, v___x_1202_);
return v___x_1203_;
}
default: 
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec(v_h__4_1194_);
lean_dec(v_h__3_1193_);
lean_dec(v_h__2_1192_);
lean_dec(v_h__1_1191_);
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_apply_1(v_h__5_1195_, v___x_1204_);
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg___boxed(lean_object* v_x_1206_, lean_object* v_h__1_1207_, lean_object* v_h__2_1208_, lean_object* v_h__3_1209_, lean_object* v_h__4_1210_, lean_object* v_h__5_1211_){
_start:
{
uint8_t v_x_51__boxed_1212_; lean_object* v_res_1213_; 
v_x_51__boxed_1212_ = lean_unbox(v_x_1206_);
v_res_1213_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(v_x_51__boxed_1212_, v_h__1_1207_, v_h__2_1208_, v_h__3_1209_, v_h__4_1210_, v_h__5_1211_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(lean_object* v_motive_1214_, uint8_t v_x_1215_, lean_object* v_h__1_1216_, lean_object* v_h__2_1217_, lean_object* v_h__3_1218_, lean_object* v_h__4_1219_, lean_object* v_h__5_1220_){
_start:
{
switch(v_x_1215_)
{
case 0:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec(v_h__5_1220_);
lean_dec(v_h__4_1219_);
lean_dec(v_h__3_1218_);
lean_dec(v_h__2_1217_);
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_apply_1(v_h__1_1216_, v___x_1221_);
return v___x_1222_;
}
case 1:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec(v_h__5_1220_);
lean_dec(v_h__4_1219_);
lean_dec(v_h__3_1218_);
lean_dec(v_h__1_1216_);
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_apply_1(v_h__2_1217_, v___x_1223_);
return v___x_1224_;
}
case 2:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_dec(v_h__5_1220_);
lean_dec(v_h__4_1219_);
lean_dec(v_h__2_1217_);
lean_dec(v_h__1_1216_);
v___x_1225_ = lean_box(0);
v___x_1226_ = lean_apply_1(v_h__3_1218_, v___x_1225_);
return v___x_1226_;
}
case 3:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec(v_h__5_1220_);
lean_dec(v_h__3_1218_);
lean_dec(v_h__2_1217_);
lean_dec(v_h__1_1216_);
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_apply_1(v_h__4_1219_, v___x_1227_);
return v___x_1228_;
}
default: 
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec(v_h__4_1219_);
lean_dec(v_h__3_1218_);
lean_dec(v_h__2_1217_);
lean_dec(v_h__1_1216_);
v___x_1229_ = lean_box(0);
v___x_1230_ = lean_apply_1(v_h__5_1220_, v___x_1229_);
return v___x_1230_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___boxed(lean_object* v_motive_1231_, lean_object* v_x_1232_, lean_object* v_h__1_1233_, lean_object* v_h__2_1234_, lean_object* v_h__3_1235_, lean_object* v_h__4_1236_, lean_object* v_h__5_1237_){
_start:
{
uint8_t v_x_74__boxed_1238_; lean_object* v_res_1239_; 
v_x_74__boxed_1238_ = lean_unbox(v_x_1232_);
v_res_1239_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(v_motive_1231_, v_x_74__boxed_1238_, v_h__1_1233_, v_h__2_1234_, v_h__3_1235_, v_h__4_1236_, v_h__5_1237_);
return v_res_1239_;
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

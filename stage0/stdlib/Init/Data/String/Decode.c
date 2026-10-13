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
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_String_utf8EncodeCharFast(uint32_t);
LEAN_EXPORT lean_object* l_String_utf8EncodeCharFast___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___impl(uint8_t v_x_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_box(v_x_87_);
v___x_89_ = lean_obj_tag_nat(v___x_88_);
lean_dec(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___impl___boxed(lean_object* v_x_90_){
_start:
{
uint8_t v_x_4__boxed_91_; lean_object* v_res_92_; 
v_x_4__boxed_91_ = lean_unbox(v_x_90_);
v_res_92_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___impl(v_x_4__boxed_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg(lean_object* v_k_93_){
_start:
{
lean_inc(v_k_93_);
return v_k_93_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg___boxed(lean_object* v_k_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg(v_k_94_);
lean_dec(v_k_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim(lean_object* v_motive_96_, lean_object* v_ctorIdx_97_, uint8_t v_t_98_, lean_object* v_h_99_, lean_object* v_k_100_){
_start:
{
lean_inc(v_k_100_);
return v_k_100_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___boxed(lean_object* v_motive_101_, lean_object* v_ctorIdx_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_k_105_){
_start:
{
uint8_t v_t_boxed_106_; lean_object* v_res_107_; 
v_t_boxed_106_ = lean_unbox(v_t_103_);
v_res_107_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim(v_motive_101_, v_ctorIdx_102_, v_t_boxed_106_, v_h_104_, v_k_105_);
lean_dec(v_k_105_);
lean_dec(v_ctorIdx_102_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg(lean_object* v_invalid_108_){
_start:
{
lean_inc(v_invalid_108_);
return v_invalid_108_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg___boxed(lean_object* v_invalid_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg(v_invalid_109_);
lean_dec(v_invalid_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(lean_object* v_motive_111_, uint8_t v_t_112_, lean_object* v_h_113_, lean_object* v_invalid_114_){
_start:
{
lean_inc(v_invalid_114_);
return v_invalid_114_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___boxed(lean_object* v_motive_115_, lean_object* v_t_116_, lean_object* v_h_117_, lean_object* v_invalid_118_){
_start:
{
uint8_t v_t_boxed_119_; lean_object* v_res_120_; 
v_t_boxed_119_ = lean_unbox(v_t_116_);
v_res_120_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(v_motive_115_, v_t_boxed_119_, v_h_117_, v_invalid_118_);
lean_dec(v_invalid_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg(lean_object* v_done_121_){
_start:
{
lean_inc(v_done_121_);
return v_done_121_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg___boxed(lean_object* v_done_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg(v_done_122_);
lean_dec(v_done_122_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(lean_object* v_motive_124_, uint8_t v_t_125_, lean_object* v_h_126_, lean_object* v_done_127_){
_start:
{
lean_inc(v_done_127_);
return v_done_127_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___boxed(lean_object* v_motive_128_, lean_object* v_t_129_, lean_object* v_h_130_, lean_object* v_done_131_){
_start:
{
uint8_t v_t_boxed_132_; lean_object* v_res_133_; 
v_t_boxed_132_ = lean_unbox(v_t_129_);
v_res_133_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(v_motive_128_, v_t_boxed_132_, v_h_130_, v_done_131_);
lean_dec(v_done_131_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg(lean_object* v_oneMore_134_){
_start:
{
lean_inc(v_oneMore_134_);
return v_oneMore_134_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg___boxed(lean_object* v_oneMore_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg(v_oneMore_135_);
lean_dec(v_oneMore_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(lean_object* v_motive_137_, uint8_t v_t_138_, lean_object* v_h_139_, lean_object* v_oneMore_140_){
_start:
{
lean_inc(v_oneMore_140_);
return v_oneMore_140_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___boxed(lean_object* v_motive_141_, lean_object* v_t_142_, lean_object* v_h_143_, lean_object* v_oneMore_144_){
_start:
{
uint8_t v_t_boxed_145_; lean_object* v_res_146_; 
v_t_boxed_145_ = lean_unbox(v_t_142_);
v_res_146_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(v_motive_141_, v_t_boxed_145_, v_h_143_, v_oneMore_144_);
lean_dec(v_oneMore_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg(lean_object* v_twoMore_147_){
_start:
{
lean_inc(v_twoMore_147_);
return v_twoMore_147_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg___boxed(lean_object* v_twoMore_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg(v_twoMore_148_);
lean_dec(v_twoMore_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(lean_object* v_motive_150_, uint8_t v_t_151_, lean_object* v_h_152_, lean_object* v_twoMore_153_){
_start:
{
lean_inc(v_twoMore_153_);
return v_twoMore_153_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___boxed(lean_object* v_motive_154_, lean_object* v_t_155_, lean_object* v_h_156_, lean_object* v_twoMore_157_){
_start:
{
uint8_t v_t_boxed_158_; lean_object* v_res_159_; 
v_t_boxed_158_ = lean_unbox(v_t_155_);
v_res_159_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(v_motive_154_, v_t_boxed_158_, v_h_156_, v_twoMore_157_);
lean_dec(v_twoMore_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg(lean_object* v_threeMore_160_){
_start:
{
lean_inc(v_threeMore_160_);
return v_threeMore_160_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg___boxed(lean_object* v_threeMore_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg(v_threeMore_161_);
lean_dec(v_threeMore_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim(lean_object* v_motive_163_, uint8_t v_t_164_, lean_object* v_h_165_, lean_object* v_threeMore_166_){
_start:
{
lean_inc(v_threeMore_166_);
return v_threeMore_166_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___boxed(lean_object* v_motive_167_, lean_object* v_t_168_, lean_object* v_h_169_, lean_object* v_threeMore_170_){
_start:
{
uint8_t v_t_boxed_171_; lean_object* v_res_172_; 
v_t_boxed_171_ = lean_unbox(v_t_168_);
v_res_172_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim(v_motive_167_, v_t_boxed_171_, v_h_169_, v_threeMore_170_);
lean_dec(v_threeMore_170_);
return v_res_172_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(uint8_t v_b_173_){
_start:
{
uint8_t v___x_174_; uint8_t v___x_175_; uint8_t v___x_176_; uint8_t v___x_177_; 
v___x_174_ = 128;
v___x_175_ = lean_uint8_land(v_b_173_, v___x_174_);
v___x_176_ = 0;
v___x_177_ = lean_uint8_dec_eq(v___x_175_, v___x_176_);
if (v___x_177_ == 0)
{
uint8_t v___x_178_; uint8_t v___x_179_; uint8_t v___x_180_; uint8_t v___x_181_; 
v___x_178_ = 224;
v___x_179_ = lean_uint8_land(v_b_173_, v___x_178_);
v___x_180_ = 192;
v___x_181_ = lean_uint8_dec_eq(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
uint8_t v___x_182_; uint8_t v___x_183_; uint8_t v___x_184_; 
v___x_182_ = 240;
v___x_183_ = lean_uint8_land(v_b_173_, v___x_182_);
v___x_184_ = lean_uint8_dec_eq(v___x_183_, v___x_178_);
if (v___x_184_ == 0)
{
uint8_t v___x_185_; uint8_t v___x_186_; uint8_t v___x_187_; 
v___x_185_ = 248;
v___x_186_ = lean_uint8_land(v_b_173_, v___x_185_);
v___x_187_ = lean_uint8_dec_eq(v___x_186_, v___x_182_);
if (v___x_187_ == 0)
{
uint8_t v___x_188_; 
v___x_188_ = 0;
return v___x_188_;
}
else
{
uint8_t v___x_189_; 
v___x_189_ = 4;
return v___x_189_;
}
}
else
{
uint8_t v___x_190_; 
v___x_190_ = 3;
return v___x_190_;
}
}
else
{
uint8_t v___x_191_; 
v___x_191_ = 2;
return v___x_191_;
}
}
else
{
uint8_t v___x_192_; 
v___x_192_ = 1;
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_parseFirstByte___boxed(lean_object* v_b_193_){
_start:
{
uint8_t v_b_boxed_194_; uint8_t v_res_195_; lean_object* v_r_196_; 
v_b_boxed_194_ = lean_unbox(v_b_193_);
v_res_195_ = l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(v_b_boxed_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(uint8_t v_b_197_){
_start:
{
uint8_t v___x_198_; uint8_t v___x_199_; uint8_t v___x_200_; uint8_t v___x_201_; 
v___x_198_ = 192;
v___x_199_ = lean_uint8_land(v_b_197_, v___x_198_);
v___x_200_ = 128;
v___x_201_ = lean_uint8_dec_eq(v___x_199_, v___x_200_);
if (v___x_201_ == 0)
{
uint8_t v___x_202_; 
v___x_202_ = 1;
return v___x_202_;
}
else
{
uint8_t v___x_203_; 
v___x_203_ = 0;
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte___boxed(lean_object* v_b_204_){
_start:
{
uint8_t v_b_boxed_205_; uint8_t v_res_206_; lean_object* v_r_207_; 
v_b_boxed_205_ = lean_unbox(v_b_204_);
v_res_206_ = l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(v_b_boxed_205_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(uint8_t v_w_208_){
_start:
{
uint32_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_uint8_to_uint32(v_w_208_);
v___x_210_ = lean_box_uint32(v___x_209_);
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg___boxed(lean_object* v_w_212_){
_start:
{
uint8_t v_w_boxed_213_; lean_object* v_res_214_; 
v_w_boxed_213_ = lean_unbox(v_w_212_);
v_res_214_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(v_w_boxed_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(uint8_t v_w_215_, lean_object* v_h_216_){
_start:
{
uint32_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = lean_uint8_to_uint32(v_w_215_);
v___x_218_ = lean_box_uint32(v___x_217_);
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___boxed(lean_object* v_w_220_, lean_object* v_h_221_){
_start:
{
uint8_t v_w_boxed_222_; lean_object* v_res_223_; 
v_w_boxed_222_ = lean_unbox(v_w_220_);
v_res_223_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(v_w_boxed_222_, v_h_221_);
return v_res_223_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg(){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = 1;
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg___boxed(lean_object* v___dummy_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg();
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2081(uint8_t v_w_229_, uint8_t v___w_230_, lean_object* v___h_231_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = 1;
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2081___boxed(lean_object* v_w_233_, lean_object* v___w_234_, lean_object* v___h_235_){
_start:
{
uint8_t v_w_boxed_236_; uint8_t v___w_boxed_237_; uint8_t v_res_238_; lean_object* v_r_239_; 
v_w_boxed_236_ = lean_unbox(v_w_233_);
v___w_boxed_237_ = lean_unbox(v___w_234_);
v_res_238_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2081(v_w_boxed_236_, v___w_boxed_237_, v___h_235_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(uint8_t v_w_240_, uint8_t v_x_241_){
_start:
{
uint8_t v___x_242_; uint8_t v_b_u2080_243_; uint8_t v___x_244_; uint8_t v_b_u2081_245_; uint32_t v___x_246_; uint32_t v___x_247_; uint32_t v___x_248_; uint32_t v___x_249_; uint32_t v___x_250_; 
v___x_242_ = 31;
v_b_u2080_243_ = lean_uint8_land(v_w_240_, v___x_242_);
v___x_244_ = 63;
v_b_u2081_245_ = lean_uint8_land(v_x_241_, v___x_244_);
v___x_246_ = lean_uint8_to_uint32(v_b_u2080_243_);
v___x_247_ = 6;
v___x_248_ = lean_uint32_shift_left(v___x_246_, v___x_247_);
v___x_249_ = lean_uint8_to_uint32(v_b_u2081_245_);
v___x_250_ = lean_uint32_lor(v___x_248_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked___boxed(lean_object* v_w_251_, lean_object* v_x_252_){
_start:
{
uint8_t v_w_boxed_253_; uint8_t v_x_boxed_254_; uint32_t v_res_255_; lean_object* v_r_256_; 
v_w_boxed_253_ = lean_unbox(v_w_251_);
v_x_boxed_254_ = lean_unbox(v_x_252_);
v_res_255_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(v_w_boxed_253_, v_x_boxed_254_);
v_r_256_ = lean_box_uint32(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(uint8_t v_w_257_, uint8_t v_x_258_){
_start:
{
uint8_t v___x_259_; uint8_t v___x_260_; uint8_t v___x_261_; uint8_t v___x_262_; 
v___x_259_ = 192;
v___x_260_ = lean_uint8_land(v_x_258_, v___x_259_);
v___x_261_ = 128;
v___x_262_ = lean_uint8_dec_eq(v___x_260_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
v___x_263_ = lean_box(0);
return v___x_263_;
}
else
{
uint8_t v___x_264_; uint8_t v_b_u2080_265_; uint8_t v___x_266_; uint8_t v_b_u2081_267_; uint32_t v___x_268_; uint32_t v___x_269_; uint32_t v___x_270_; uint32_t v___x_271_; uint32_t v_r_272_; uint32_t v___x_273_; uint8_t v___x_274_; 
v___x_264_ = 31;
v_b_u2080_265_ = lean_uint8_land(v_w_257_, v___x_264_);
v___x_266_ = 63;
v_b_u2081_267_ = lean_uint8_land(v_x_258_, v___x_266_);
v___x_268_ = lean_uint8_to_uint32(v_b_u2080_265_);
v___x_269_ = 6;
v___x_270_ = lean_uint32_shift_left(v___x_268_, v___x_269_);
v___x_271_ = lean_uint8_to_uint32(v_b_u2081_267_);
v_r_272_ = lean_uint32_lor(v___x_270_, v___x_271_);
v___x_273_ = 128;
v___x_274_ = lean_uint32_dec_lt(v_r_272_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_box_uint32(v_r_272_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = lean_box(0);
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082___boxed(lean_object* v_w_278_, lean_object* v_x_279_){
_start:
{
uint8_t v_w_boxed_280_; uint8_t v_x_boxed_281_; lean_object* v_res_282_; 
v_w_boxed_280_ = lean_unbox(v_w_278_);
v_x_boxed_281_ = lean_unbox(v_x_279_);
v_res_282_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(v_w_boxed_280_, v_x_boxed_281_);
return v_res_282_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2082(uint8_t v_w_283_, uint8_t v_x_284_){
_start:
{
uint8_t v___x_285_; uint8_t v___x_286_; uint8_t v___x_287_; uint8_t v___x_288_; 
v___x_285_ = 192;
v___x_286_ = lean_uint8_land(v_x_284_, v___x_285_);
v___x_287_ = 128;
v___x_288_ = lean_uint8_dec_eq(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
return v___x_288_;
}
else
{
uint8_t v___x_289_; uint8_t v_b_u2080_290_; uint8_t v___x_291_; uint8_t v_b_u2081_292_; uint32_t v___x_293_; uint32_t v___x_294_; uint32_t v___x_295_; uint32_t v___x_296_; uint32_t v_r_297_; uint32_t v___x_298_; uint8_t v___x_299_; 
v___x_289_ = 31;
v_b_u2080_290_ = lean_uint8_land(v_w_283_, v___x_289_);
v___x_291_ = 63;
v_b_u2081_292_ = lean_uint8_land(v_x_284_, v___x_291_);
v___x_293_ = lean_uint8_to_uint32(v_b_u2080_290_);
v___x_294_ = 6;
v___x_295_ = lean_uint32_shift_left(v___x_293_, v___x_294_);
v___x_296_ = lean_uint8_to_uint32(v_b_u2081_292_);
v_r_297_ = lean_uint32_lor(v___x_295_, v___x_296_);
v___x_298_ = 128;
v___x_299_ = lean_uint32_dec_le(v___x_298_, v_r_297_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2082___boxed(lean_object* v_w_300_, lean_object* v_x_301_){
_start:
{
uint8_t v_w_boxed_302_; uint8_t v_x_boxed_303_; uint8_t v_res_304_; lean_object* v_r_305_; 
v_w_boxed_302_ = lean_unbox(v_w_300_);
v_x_boxed_303_ = lean_unbox(v_x_301_);
v_res_304_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2082(v_w_boxed_302_, v_x_boxed_303_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(uint8_t v_w_306_, uint8_t v_x_307_, uint8_t v_y_308_){
_start:
{
uint8_t v___x_309_; uint8_t v_b_u2080_310_; uint8_t v___x_311_; uint8_t v_b_u2081_312_; uint8_t v_b_u2082_313_; uint32_t v___x_314_; uint32_t v___x_315_; uint32_t v___x_316_; uint32_t v___x_317_; uint32_t v___x_318_; uint32_t v___x_319_; uint32_t v___x_320_; uint32_t v___x_321_; uint32_t v___x_322_; 
v___x_309_ = 15;
v_b_u2080_310_ = lean_uint8_land(v_w_306_, v___x_309_);
v___x_311_ = 63;
v_b_u2081_312_ = lean_uint8_land(v_x_307_, v___x_311_);
v_b_u2082_313_ = lean_uint8_land(v_y_308_, v___x_311_);
v___x_314_ = lean_uint8_to_uint32(v_b_u2080_310_);
v___x_315_ = 12;
v___x_316_ = lean_uint32_shift_left(v___x_314_, v___x_315_);
v___x_317_ = lean_uint8_to_uint32(v_b_u2081_312_);
v___x_318_ = 6;
v___x_319_ = lean_uint32_shift_left(v___x_317_, v___x_318_);
v___x_320_ = lean_uint32_lor(v___x_316_, v___x_319_);
v___x_321_ = lean_uint8_to_uint32(v_b_u2082_313_);
v___x_322_ = lean_uint32_lor(v___x_320_, v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked___boxed(lean_object* v_w_323_, lean_object* v_x_324_, lean_object* v_y_325_){
_start:
{
uint8_t v_w_boxed_326_; uint8_t v_x_boxed_327_; uint8_t v_y_boxed_328_; uint32_t v_res_329_; lean_object* v_r_330_; 
v_w_boxed_326_ = lean_unbox(v_w_323_);
v_x_boxed_327_ = lean_unbox(v_x_324_);
v_y_boxed_328_ = lean_unbox(v_y_325_);
v_res_329_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(v_w_boxed_326_, v_x_boxed_327_, v_y_boxed_328_);
v_r_330_ = lean_box_uint32(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(uint8_t v_w_331_, uint8_t v_x_332_, uint8_t v_y_333_){
_start:
{
uint8_t v___x_334_; uint8_t v___x_335_; uint8_t v___x_336_; uint8_t v___x_337_; 
v___x_334_ = 192;
v___x_335_ = lean_uint8_land(v_x_332_, v___x_334_);
v___x_336_ = 128;
v___x_337_ = lean_uint8_dec_eq(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
v___x_338_ = lean_box(0);
return v___x_338_;
}
else
{
uint8_t v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_uint8_land(v_y_333_, v___x_334_);
v___x_340_ = lean_uint8_dec_eq(v___x_339_, v___x_336_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
v___x_341_ = lean_box(0);
return v___x_341_;
}
else
{
uint8_t v___x_342_; uint8_t v_b_u2080_343_; uint8_t v___x_344_; uint8_t v_b_u2081_345_; uint8_t v_b_u2082_346_; uint32_t v___x_347_; uint32_t v___x_348_; uint32_t v___x_349_; uint32_t v___x_350_; uint32_t v___x_351_; uint32_t v___x_352_; uint32_t v___x_353_; uint32_t v___x_354_; uint32_t v_r_355_; uint32_t v___x_356_; uint8_t v___x_357_; 
v___x_342_ = 15;
v_b_u2080_343_ = lean_uint8_land(v_w_331_, v___x_342_);
v___x_344_ = 63;
v_b_u2081_345_ = lean_uint8_land(v_x_332_, v___x_344_);
v_b_u2082_346_ = lean_uint8_land(v_y_333_, v___x_344_);
v___x_347_ = lean_uint8_to_uint32(v_b_u2080_343_);
v___x_348_ = 12;
v___x_349_ = lean_uint32_shift_left(v___x_347_, v___x_348_);
v___x_350_ = lean_uint8_to_uint32(v_b_u2081_345_);
v___x_351_ = 6;
v___x_352_ = lean_uint32_shift_left(v___x_350_, v___x_351_);
v___x_353_ = lean_uint32_lor(v___x_349_, v___x_352_);
v___x_354_ = lean_uint8_to_uint32(v_b_u2082_346_);
v_r_355_ = lean_uint32_lor(v___x_353_, v___x_354_);
v___x_356_ = 2048;
v___x_357_ = lean_uint32_dec_lt(v_r_355_, v___x_356_);
if (v___x_357_ == 0)
{
uint32_t v___x_358_; uint8_t v___x_359_; 
v___x_358_ = 55296;
v___x_359_ = lean_uint32_dec_le(v___x_358_, v_r_355_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_box_uint32(v_r_355_);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
else
{
uint32_t v___x_362_; uint8_t v___x_363_; 
v___x_362_ = 57343;
v___x_363_ = lean_uint32_dec_le(v_r_355_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_box_uint32(v_r_355_);
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; 
v___x_366_ = lean_box(0);
return v___x_366_;
}
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
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083___boxed(lean_object* v_w_368_, lean_object* v_x_369_, lean_object* v_y_370_){
_start:
{
uint8_t v_w_boxed_371_; uint8_t v_x_boxed_372_; uint8_t v_y_boxed_373_; lean_object* v_res_374_; 
v_w_boxed_371_ = lean_unbox(v_w_368_);
v_x_boxed_372_ = lean_unbox(v_x_369_);
v_y_boxed_373_ = lean_unbox(v_y_370_);
v_res_374_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(v_w_boxed_371_, v_x_boxed_372_, v_y_boxed_373_);
return v_res_374_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2083(uint8_t v_w_375_, uint8_t v_x_376_, uint8_t v_y_377_){
_start:
{
uint8_t v___x_378_; uint8_t v___x_379_; uint8_t v___x_380_; uint8_t v___x_381_; 
v___x_378_ = 192;
v___x_379_ = lean_uint8_land(v_x_376_, v___x_378_);
v___x_380_ = 128;
v___x_381_ = lean_uint8_dec_eq(v___x_379_, v___x_380_);
if (v___x_381_ == 0)
{
return v___x_381_;
}
else
{
uint8_t v___x_382_; uint8_t v___x_383_; uint8_t v___x_384_; 
v___x_382_ = 0;
v___x_383_ = lean_uint8_land(v_y_377_, v___x_378_);
v___x_384_ = lean_uint8_dec_eq(v___x_383_, v___x_380_);
if (v___x_384_ == 0)
{
return v___x_382_;
}
else
{
uint8_t v___x_385_; uint8_t v_b_u2080_386_; uint8_t v___x_387_; uint8_t v_b_u2081_388_; uint8_t v_b_u2082_389_; uint32_t v___x_390_; uint32_t v___x_391_; uint32_t v___x_392_; uint32_t v___x_393_; uint32_t v___x_394_; uint32_t v___x_395_; uint32_t v___x_396_; uint32_t v___x_397_; uint32_t v_r_398_; uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_385_ = 15;
v_b_u2080_386_ = lean_uint8_land(v_w_375_, v___x_385_);
v___x_387_ = 63;
v_b_u2081_388_ = lean_uint8_land(v_x_376_, v___x_387_);
v_b_u2082_389_ = lean_uint8_land(v_y_377_, v___x_387_);
v___x_390_ = lean_uint8_to_uint32(v_b_u2080_386_);
v___x_391_ = 12;
v___x_392_ = lean_uint32_shift_left(v___x_390_, v___x_391_);
v___x_393_ = lean_uint8_to_uint32(v_b_u2081_388_);
v___x_394_ = 6;
v___x_395_ = lean_uint32_shift_left(v___x_393_, v___x_394_);
v___x_396_ = lean_uint32_lor(v___x_392_, v___x_395_);
v___x_397_ = lean_uint8_to_uint32(v_b_u2082_389_);
v_r_398_ = lean_uint32_lor(v___x_396_, v___x_397_);
v___x_399_ = 2048;
v___x_400_ = lean_uint32_dec_le(v___x_399_, v_r_398_);
if (v___x_400_ == 0)
{
return v___x_382_;
}
else
{
uint32_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = 55296;
v___x_402_ = lean_uint32_dec_lt(v_r_398_, v___x_401_);
if (v___x_402_ == 0)
{
uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 57343;
v___x_404_ = lean_uint32_dec_lt(v___x_403_, v_r_398_);
return v___x_404_;
}
else
{
return v___x_402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2083___boxed(lean_object* v_w_405_, lean_object* v_x_406_, lean_object* v_y_407_){
_start:
{
uint8_t v_w_boxed_408_; uint8_t v_x_boxed_409_; uint8_t v_y_boxed_410_; uint8_t v_res_411_; lean_object* v_r_412_; 
v_w_boxed_408_ = lean_unbox(v_w_405_);
v_x_boxed_409_ = lean_unbox(v_x_406_);
v_y_boxed_410_ = lean_unbox(v_y_407_);
v_res_411_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2083(v_w_boxed_408_, v_x_boxed_409_, v_y_boxed_410_);
v_r_412_ = lean_box(v_res_411_);
return v_r_412_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(uint8_t v_w_413_, uint8_t v_x_414_, uint8_t v_y_415_, uint8_t v_z_416_){
_start:
{
uint8_t v___x_417_; uint8_t v_b_u2080_418_; uint8_t v___x_419_; uint8_t v_b_u2081_420_; uint8_t v_b_u2082_421_; uint8_t v_b_u2083_422_; uint32_t v___x_423_; uint32_t v___x_424_; uint32_t v___x_425_; uint32_t v___x_426_; uint32_t v___x_427_; uint32_t v___x_428_; uint32_t v___x_429_; uint32_t v___x_430_; uint32_t v___x_431_; uint32_t v___x_432_; uint32_t v___x_433_; uint32_t v___x_434_; uint32_t v___x_435_; 
v___x_417_ = 7;
v_b_u2080_418_ = lean_uint8_land(v_w_413_, v___x_417_);
v___x_419_ = 63;
v_b_u2081_420_ = lean_uint8_land(v_x_414_, v___x_419_);
v_b_u2082_421_ = lean_uint8_land(v_y_415_, v___x_419_);
v_b_u2083_422_ = lean_uint8_land(v_z_416_, v___x_419_);
v___x_423_ = lean_uint8_to_uint32(v_b_u2080_418_);
v___x_424_ = 18;
v___x_425_ = lean_uint32_shift_left(v___x_423_, v___x_424_);
v___x_426_ = lean_uint8_to_uint32(v_b_u2081_420_);
v___x_427_ = 12;
v___x_428_ = lean_uint32_shift_left(v___x_426_, v___x_427_);
v___x_429_ = lean_uint32_lor(v___x_425_, v___x_428_);
v___x_430_ = lean_uint8_to_uint32(v_b_u2082_421_);
v___x_431_ = 6;
v___x_432_ = lean_uint32_shift_left(v___x_430_, v___x_431_);
v___x_433_ = lean_uint32_lor(v___x_429_, v___x_432_);
v___x_434_ = lean_uint8_to_uint32(v_b_u2083_422_);
v___x_435_ = lean_uint32_lor(v___x_433_, v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked___boxed(lean_object* v_w_436_, lean_object* v_x_437_, lean_object* v_y_438_, lean_object* v_z_439_){
_start:
{
uint8_t v_w_boxed_440_; uint8_t v_x_boxed_441_; uint8_t v_y_boxed_442_; uint8_t v_z_boxed_443_; uint32_t v_res_444_; lean_object* v_r_445_; 
v_w_boxed_440_ = lean_unbox(v_w_436_);
v_x_boxed_441_ = lean_unbox(v_x_437_);
v_y_boxed_442_ = lean_unbox(v_y_438_);
v_z_boxed_443_ = lean_unbox(v_z_439_);
v_res_444_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(v_w_boxed_440_, v_x_boxed_441_, v_y_boxed_442_, v_z_boxed_443_);
v_r_445_ = lean_box_uint32(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(uint8_t v_w_446_, uint8_t v_x_447_, uint8_t v_y_448_, uint8_t v_z_449_){
_start:
{
uint8_t v___x_450_; uint8_t v___x_451_; uint8_t v___x_452_; uint8_t v___x_453_; 
v___x_450_ = 192;
v___x_451_ = lean_uint8_land(v_x_447_, v___x_450_);
v___x_452_ = 128;
v___x_453_ = lean_uint8_dec_eq(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
v___x_454_ = lean_box(0);
return v___x_454_;
}
else
{
uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_uint8_land(v_y_448_, v___x_450_);
v___x_456_ = lean_uint8_dec_eq(v___x_455_, v___x_452_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
v___x_457_ = lean_box(0);
return v___x_457_;
}
else
{
uint8_t v___x_458_; uint8_t v___x_459_; 
v___x_458_ = lean_uint8_land(v_z_449_, v___x_450_);
v___x_459_ = lean_uint8_dec_eq(v___x_458_, v___x_452_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
v___x_460_ = lean_box(0);
return v___x_460_;
}
else
{
uint8_t v___x_461_; uint8_t v_b_u2080_462_; uint8_t v___x_463_; uint8_t v_b_u2081_464_; uint8_t v_b_u2082_465_; uint8_t v_b_u2083_466_; uint32_t v___x_467_; uint32_t v___x_468_; uint32_t v___x_469_; uint32_t v___x_470_; uint32_t v___x_471_; uint32_t v___x_472_; uint32_t v___x_473_; uint32_t v___x_474_; uint32_t v___x_475_; uint32_t v___x_476_; uint32_t v___x_477_; uint32_t v___x_478_; uint32_t v_r_479_; uint32_t v___x_480_; uint8_t v___x_481_; 
v___x_461_ = 7;
v_b_u2080_462_ = lean_uint8_land(v_w_446_, v___x_461_);
v___x_463_ = 63;
v_b_u2081_464_ = lean_uint8_land(v_x_447_, v___x_463_);
v_b_u2082_465_ = lean_uint8_land(v_y_448_, v___x_463_);
v_b_u2083_466_ = lean_uint8_land(v_z_449_, v___x_463_);
v___x_467_ = lean_uint8_to_uint32(v_b_u2080_462_);
v___x_468_ = 18;
v___x_469_ = lean_uint32_shift_left(v___x_467_, v___x_468_);
v___x_470_ = lean_uint8_to_uint32(v_b_u2081_464_);
v___x_471_ = 12;
v___x_472_ = lean_uint32_shift_left(v___x_470_, v___x_471_);
v___x_473_ = lean_uint32_lor(v___x_469_, v___x_472_);
v___x_474_ = lean_uint8_to_uint32(v_b_u2082_465_);
v___x_475_ = 6;
v___x_476_ = lean_uint32_shift_left(v___x_474_, v___x_475_);
v___x_477_ = lean_uint32_lor(v___x_473_, v___x_476_);
v___x_478_ = lean_uint8_to_uint32(v_b_u2083_466_);
v_r_479_ = lean_uint32_lor(v___x_477_, v___x_478_);
v___x_480_ = 65536;
v___x_481_ = lean_uint32_dec_lt(v_r_479_, v___x_480_);
if (v___x_481_ == 0)
{
uint32_t v___x_482_; uint8_t v___x_483_; 
v___x_482_ = 1114111;
v___x_483_ = lean_uint32_dec_lt(v___x_482_, v_r_479_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_box_uint32(v_r_479_);
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; 
v___x_486_ = lean_box(0);
return v___x_486_;
}
}
else
{
lean_object* v___x_487_; 
v___x_487_ = lean_box(0);
return v___x_487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084___boxed(lean_object* v_w_488_, lean_object* v_x_489_, lean_object* v_y_490_, lean_object* v_z_491_){
_start:
{
uint8_t v_w_boxed_492_; uint8_t v_x_boxed_493_; uint8_t v_y_boxed_494_; uint8_t v_z_boxed_495_; lean_object* v_res_496_; 
v_w_boxed_492_ = lean_unbox(v_w_488_);
v_x_boxed_493_ = lean_unbox(v_x_489_);
v_y_boxed_494_ = lean_unbox(v_y_490_);
v_z_boxed_495_ = lean_unbox(v_z_491_);
v_res_496_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(v_w_boxed_492_, v_x_boxed_493_, v_y_boxed_494_, v_z_boxed_495_);
return v_res_496_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2084(uint8_t v_w_497_, uint8_t v_x_498_, uint8_t v_y_499_, uint8_t v_z_500_){
_start:
{
uint8_t v___x_501_; uint8_t v___x_502_; uint8_t v___x_503_; uint8_t v___x_504_; 
v___x_501_ = 192;
v___x_502_ = lean_uint8_land(v_x_498_, v___x_501_);
v___x_503_ = 128;
v___x_504_ = lean_uint8_dec_eq(v___x_502_, v___x_503_);
if (v___x_504_ == 0)
{
return v___x_504_;
}
else
{
uint8_t v___x_505_; uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_505_ = 0;
v___x_506_ = lean_uint8_land(v_y_499_, v___x_501_);
v___x_507_ = lean_uint8_dec_eq(v___x_506_, v___x_503_);
if (v___x_507_ == 0)
{
return v___x_505_;
}
else
{
uint8_t v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_uint8_land(v_z_500_, v___x_501_);
v___x_509_ = lean_uint8_dec_eq(v___x_508_, v___x_503_);
if (v___x_509_ == 0)
{
return v___x_505_;
}
else
{
uint8_t v___x_510_; uint8_t v_b_u2080_511_; uint8_t v___x_512_; uint8_t v_b_u2081_513_; uint8_t v_b_u2082_514_; uint8_t v_b_u2083_515_; uint32_t v___x_516_; uint32_t v___x_517_; uint32_t v___x_518_; uint32_t v___x_519_; uint32_t v___x_520_; uint32_t v___x_521_; uint32_t v___x_522_; uint32_t v___x_523_; uint32_t v___x_524_; uint32_t v___x_525_; uint32_t v___x_526_; uint32_t v___x_527_; uint32_t v_r_528_; uint32_t v___x_529_; uint8_t v___x_530_; 
v___x_510_ = 7;
v_b_u2080_511_ = lean_uint8_land(v_w_497_, v___x_510_);
v___x_512_ = 63;
v_b_u2081_513_ = lean_uint8_land(v_x_498_, v___x_512_);
v_b_u2082_514_ = lean_uint8_land(v_y_499_, v___x_512_);
v_b_u2083_515_ = lean_uint8_land(v_z_500_, v___x_512_);
v___x_516_ = lean_uint8_to_uint32(v_b_u2080_511_);
v___x_517_ = 18;
v___x_518_ = lean_uint32_shift_left(v___x_516_, v___x_517_);
v___x_519_ = lean_uint8_to_uint32(v_b_u2081_513_);
v___x_520_ = 12;
v___x_521_ = lean_uint32_shift_left(v___x_519_, v___x_520_);
v___x_522_ = lean_uint32_lor(v___x_518_, v___x_521_);
v___x_523_ = lean_uint8_to_uint32(v_b_u2082_514_);
v___x_524_ = 6;
v___x_525_ = lean_uint32_shift_left(v___x_523_, v___x_524_);
v___x_526_ = lean_uint32_lor(v___x_522_, v___x_525_);
v___x_527_ = lean_uint8_to_uint32(v_b_u2083_515_);
v_r_528_ = lean_uint32_lor(v___x_526_, v___x_527_);
v___x_529_ = 65536;
v___x_530_ = lean_uint32_dec_le(v___x_529_, v_r_528_);
if (v___x_530_ == 0)
{
return v___x_505_;
}
else
{
uint32_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 1114111;
v___x_532_ = lean_uint32_dec_le(v_r_528_, v___x_531_);
return v___x_532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2084___boxed(lean_object* v_w_533_, lean_object* v_x_534_, lean_object* v_y_535_, lean_object* v_z_536_){
_start:
{
uint8_t v_w_boxed_537_; uint8_t v_x_boxed_538_; uint8_t v_y_boxed_539_; uint8_t v_z_boxed_540_; uint8_t v_res_541_; lean_object* v_r_542_; 
v_w_boxed_537_ = lean_unbox(v_w_533_);
v_x_boxed_538_ = lean_unbox(v_x_534_);
v_y_boxed_539_ = lean_unbox(v_y_535_);
v_z_boxed_540_ = lean_unbox(v_z_536_);
v_res_541_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2084(v_w_boxed_537_, v_x_boxed_538_, v_y_boxed_539_, v_z_boxed_540_);
v_r_542_ = lean_box(v_res_541_);
return v_r_542_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f(lean_object* v_bytes_543_, lean_object* v_i_544_){
_start:
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_byte_array_size(v_bytes_543_);
v___x_546_ = lean_nat_dec_lt(v_i_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
v___x_547_ = lean_box(0);
return v___x_547_;
}
else
{
uint8_t v___x_548_; uint8_t v___x_549_; uint8_t v___x_550_; uint8_t v___x_551_; uint8_t v___x_552_; 
v___x_548_ = lean_byte_array_fget(v_bytes_543_, v_i_544_);
v___x_549_ = 128;
v___x_550_ = lean_uint8_land(v___x_548_, v___x_549_);
v___x_551_ = 0;
v___x_552_ = lean_uint8_dec_eq(v___x_550_, v___x_551_);
if (v___x_552_ == 0)
{
uint8_t v___x_553_; uint8_t v___x_554_; uint8_t v___x_555_; uint8_t v___x_556_; 
v___x_553_ = 224;
v___x_554_ = lean_uint8_land(v___x_548_, v___x_553_);
v___x_555_ = 192;
v___x_556_ = lean_uint8_dec_eq(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
uint8_t v___x_557_; uint8_t v___x_558_; uint8_t v___x_559_; 
v___x_557_ = 240;
v___x_558_ = lean_uint8_land(v___x_548_, v___x_557_);
v___x_559_ = lean_uint8_dec_eq(v___x_558_, v___x_553_);
if (v___x_559_ == 0)
{
uint8_t v___x_560_; uint8_t v___x_561_; uint8_t v___x_562_; 
v___x_560_ = 248;
v___x_561_ = lean_uint8_land(v___x_548_, v___x_560_);
v___x_562_ = lean_uint8_dec_eq(v___x_561_, v___x_557_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
v___x_563_ = lean_box(0);
return v___x_563_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_564_ = lean_unsigned_to_nat(3u);
v___x_565_ = lean_nat_add(v_i_544_, v___x_564_);
v___x_566_ = lean_nat_dec_lt(v___x_565_, v___x_545_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; 
lean_dec(v___x_565_);
v___x_567_ = lean_box(0);
return v___x_567_;
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; uint8_t v___x_571_; uint8_t v___x_572_; 
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = lean_nat_add(v_i_544_, v___x_568_);
v___x_570_ = lean_byte_array_fget(v_bytes_543_, v___x_569_);
lean_dec(v___x_569_);
v___x_571_ = lean_uint8_land(v___x_570_, v___x_555_);
v___x_572_ = lean_uint8_dec_eq(v___x_571_, v___x_549_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
lean_dec(v___x_565_);
v___x_573_ = lean_box(0);
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; uint8_t v___x_577_; uint8_t v___x_578_; 
v___x_574_ = lean_unsigned_to_nat(2u);
v___x_575_ = lean_nat_add(v_i_544_, v___x_574_);
v___x_576_ = lean_byte_array_fget(v_bytes_543_, v___x_575_);
lean_dec(v___x_575_);
v___x_577_ = lean_uint8_land(v___x_576_, v___x_555_);
v___x_578_ = lean_uint8_dec_eq(v___x_577_, v___x_549_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
lean_dec(v___x_565_);
v___x_579_ = lean_box(0);
return v___x_579_;
}
else
{
uint8_t v___x_580_; uint8_t v___x_581_; uint8_t v___x_582_; 
v___x_580_ = lean_byte_array_fget(v_bytes_543_, v___x_565_);
lean_dec(v___x_565_);
v___x_581_ = lean_uint8_land(v___x_580_, v___x_555_);
v___x_582_ = lean_uint8_dec_eq(v___x_581_, v___x_549_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
v___x_583_ = lean_box(0);
return v___x_583_;
}
else
{
uint8_t v___x_584_; uint8_t v_b_u2080_585_; uint8_t v___x_586_; uint8_t v_b_u2081_587_; uint8_t v_b_u2082_588_; uint8_t v_b_u2083_589_; uint32_t v___x_590_; uint32_t v___x_591_; uint32_t v___x_592_; uint32_t v___x_593_; uint32_t v___x_594_; uint32_t v___x_595_; uint32_t v___x_596_; uint32_t v___x_597_; uint32_t v___x_598_; uint32_t v___x_599_; uint32_t v___x_600_; uint32_t v___x_601_; uint32_t v_r_602_; uint32_t v___x_603_; uint8_t v___x_604_; 
v___x_584_ = 7;
v_b_u2080_585_ = lean_uint8_land(v___x_548_, v___x_584_);
v___x_586_ = 63;
v_b_u2081_587_ = lean_uint8_land(v___x_570_, v___x_586_);
v_b_u2082_588_ = lean_uint8_land(v___x_576_, v___x_586_);
v_b_u2083_589_ = lean_uint8_land(v___x_580_, v___x_586_);
v___x_590_ = lean_uint8_to_uint32(v_b_u2080_585_);
v___x_591_ = 18;
v___x_592_ = lean_uint32_shift_left(v___x_590_, v___x_591_);
v___x_593_ = lean_uint8_to_uint32(v_b_u2081_587_);
v___x_594_ = 12;
v___x_595_ = lean_uint32_shift_left(v___x_593_, v___x_594_);
v___x_596_ = lean_uint32_lor(v___x_592_, v___x_595_);
v___x_597_ = lean_uint8_to_uint32(v_b_u2082_588_);
v___x_598_ = 6;
v___x_599_ = lean_uint32_shift_left(v___x_597_, v___x_598_);
v___x_600_ = lean_uint32_lor(v___x_596_, v___x_599_);
v___x_601_ = lean_uint8_to_uint32(v_b_u2083_589_);
v_r_602_ = lean_uint32_lor(v___x_600_, v___x_601_);
v___x_603_ = 65536;
v___x_604_ = lean_uint32_dec_lt(v_r_602_, v___x_603_);
if (v___x_604_ == 0)
{
uint32_t v___x_605_; uint8_t v___x_606_; 
v___x_605_ = 1114111;
v___x_606_ = lean_uint32_dec_lt(v___x_605_, v_r_602_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_box_uint32(v_r_602_);
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; 
v___x_609_ = lean_box(0);
return v___x_609_;
}
}
else
{
lean_object* v___x_610_; 
v___x_610_ = lean_box(0);
return v___x_610_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_unsigned_to_nat(2u);
v___x_612_ = lean_nat_add(v_i_544_, v___x_611_);
v___x_613_ = lean_nat_dec_lt(v___x_612_, v___x_545_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
lean_dec(v___x_612_);
v___x_614_ = lean_box(0);
return v___x_614_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; uint8_t v___x_618_; uint8_t v___x_619_; 
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_add(v_i_544_, v___x_615_);
v___x_617_ = lean_byte_array_fget(v_bytes_543_, v___x_616_);
lean_dec(v___x_616_);
v___x_618_ = lean_uint8_land(v___x_617_, v___x_555_);
v___x_619_ = lean_uint8_dec_eq(v___x_618_, v___x_549_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_dec(v___x_612_);
v___x_620_ = lean_box(0);
return v___x_620_;
}
else
{
uint8_t v___x_621_; uint8_t v___x_622_; uint8_t v___x_623_; 
v___x_621_ = lean_byte_array_fget(v_bytes_543_, v___x_612_);
lean_dec(v___x_612_);
v___x_622_ = lean_uint8_land(v___x_621_, v___x_555_);
v___x_623_ = lean_uint8_dec_eq(v___x_622_, v___x_549_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
v___x_624_ = lean_box(0);
return v___x_624_;
}
else
{
uint8_t v___x_625_; uint8_t v_b_u2080_626_; uint8_t v___x_627_; uint8_t v_b_u2081_628_; uint8_t v_b_u2082_629_; uint32_t v___x_630_; uint32_t v___x_631_; uint32_t v___x_632_; uint32_t v___x_633_; uint32_t v___x_634_; uint32_t v___x_635_; uint32_t v___x_636_; uint32_t v___x_637_; uint32_t v_r_638_; uint32_t v___x_639_; uint8_t v___x_640_; 
v___x_625_ = 15;
v_b_u2080_626_ = lean_uint8_land(v___x_548_, v___x_625_);
v___x_627_ = 63;
v_b_u2081_628_ = lean_uint8_land(v___x_617_, v___x_627_);
v_b_u2082_629_ = lean_uint8_land(v___x_621_, v___x_627_);
v___x_630_ = lean_uint8_to_uint32(v_b_u2080_626_);
v___x_631_ = 12;
v___x_632_ = lean_uint32_shift_left(v___x_630_, v___x_631_);
v___x_633_ = lean_uint8_to_uint32(v_b_u2081_628_);
v___x_634_ = 6;
v___x_635_ = lean_uint32_shift_left(v___x_633_, v___x_634_);
v___x_636_ = lean_uint32_lor(v___x_632_, v___x_635_);
v___x_637_ = lean_uint8_to_uint32(v_b_u2082_629_);
v_r_638_ = lean_uint32_lor(v___x_636_, v___x_637_);
v___x_639_ = 2048;
v___x_640_ = lean_uint32_dec_lt(v_r_638_, v___x_639_);
if (v___x_640_ == 0)
{
uint32_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = 55296;
v___x_642_ = lean_uint32_dec_le(v___x_641_, v_r_638_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_box_uint32(v_r_638_);
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
else
{
uint32_t v___x_645_; uint8_t v___x_646_; 
v___x_645_ = 57343;
v___x_646_ = lean_uint32_dec_le(v_r_638_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_box_uint32(v_r_638_);
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; 
v___x_649_ = lean_box(0);
return v___x_649_;
}
}
}
else
{
lean_object* v___x_650_; 
v___x_650_ = lean_box(0);
return v___x_650_;
}
}
}
}
}
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_nat_add(v_i_544_, v___x_651_);
v___x_653_ = lean_nat_dec_lt(v___x_652_, v___x_545_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec(v___x_652_);
v___x_654_ = lean_box(0);
return v___x_654_;
}
else
{
uint8_t v___x_655_; uint8_t v___x_656_; uint8_t v___x_657_; 
v___x_655_ = lean_byte_array_fget(v_bytes_543_, v___x_652_);
lean_dec(v___x_652_);
v___x_656_ = lean_uint8_land(v___x_655_, v___x_555_);
v___x_657_ = lean_uint8_dec_eq(v___x_656_, v___x_549_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
v___x_658_ = lean_box(0);
return v___x_658_;
}
else
{
uint8_t v___x_659_; uint8_t v_b_u2080_660_; uint8_t v___x_661_; uint8_t v_b_u2081_662_; uint32_t v___x_663_; uint32_t v___x_664_; uint32_t v___x_665_; uint32_t v___x_666_; uint32_t v_r_667_; uint32_t v___x_668_; uint8_t v___x_669_; 
v___x_659_ = 31;
v_b_u2080_660_ = lean_uint8_land(v___x_548_, v___x_659_);
v___x_661_ = 63;
v_b_u2081_662_ = lean_uint8_land(v___x_655_, v___x_661_);
v___x_663_ = lean_uint8_to_uint32(v_b_u2080_660_);
v___x_664_ = 6;
v___x_665_ = lean_uint32_shift_left(v___x_663_, v___x_664_);
v___x_666_ = lean_uint8_to_uint32(v_b_u2081_662_);
v_r_667_ = lean_uint32_lor(v___x_665_, v___x_666_);
v___x_668_ = 128;
v___x_669_ = lean_uint32_dec_lt(v_r_667_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_box_uint32(v_r_667_);
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
else
{
lean_object* v___x_672_; 
v___x_672_ = lean_box(0);
return v___x_672_;
}
}
}
}
}
else
{
uint32_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = lean_uint8_to_uint32(v___x_548_);
v___x_674_ = lean_box_uint32(v___x_673_);
v___x_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f___boxed(lean_object* v_bytes_676_, lean_object* v_i_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_ByteArray_utf8DecodeChar_x3f(v_bytes_676_, v_i_677_);
lean_dec(v_i_677_);
lean_dec_ref(v_bytes_676_);
return v_res_678_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8At(lean_object* v_bytes_679_, lean_object* v_i_680_){
_start:
{
lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = lean_byte_array_size(v_bytes_679_);
v___x_682_ = lean_nat_dec_lt(v_i_680_, v___x_681_);
if (v___x_682_ == 0)
{
return v___x_682_;
}
else
{
uint8_t v___x_683_; uint8_t v___x_684_; uint8_t v___x_685_; uint8_t v___x_686_; uint8_t v___x_687_; 
v___x_683_ = lean_byte_array_fget(v_bytes_679_, v_i_680_);
v___x_684_ = 128;
v___x_685_ = lean_uint8_land(v___x_683_, v___x_684_);
v___x_686_ = 0;
v___x_687_ = lean_uint8_dec_eq(v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
uint8_t v___x_688_; uint8_t v___x_689_; uint8_t v___x_690_; uint8_t v___x_691_; 
v___x_688_ = 224;
v___x_689_ = lean_uint8_land(v___x_683_, v___x_688_);
v___x_690_ = 192;
v___x_691_ = lean_uint8_dec_eq(v___x_689_, v___x_690_);
if (v___x_691_ == 0)
{
uint8_t v___x_692_; uint8_t v___x_693_; uint8_t v___x_694_; 
v___x_692_ = 240;
v___x_693_ = lean_uint8_land(v___x_683_, v___x_692_);
v___x_694_ = lean_uint8_dec_eq(v___x_693_, v___x_688_);
if (v___x_694_ == 0)
{
uint8_t v___x_695_; uint8_t v___x_696_; uint8_t v___x_697_; 
v___x_695_ = 248;
v___x_696_ = lean_uint8_land(v___x_683_, v___x_695_);
v___x_697_ = lean_uint8_dec_eq(v___x_696_, v___x_692_);
if (v___x_697_ == 0)
{
return v___x_697_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_698_ = lean_unsigned_to_nat(3u);
v___x_699_ = lean_nat_add(v_i_680_, v___x_698_);
v___x_700_ = lean_nat_dec_lt(v___x_699_, v___x_681_);
if (v___x_700_ == 0)
{
lean_dec(v___x_699_);
return v___x_700_;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; uint8_t v___x_704_; uint8_t v___x_705_; 
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = lean_nat_add(v_i_680_, v___x_701_);
v___x_703_ = lean_byte_array_fget(v_bytes_679_, v___x_702_);
lean_dec(v___x_702_);
v___x_704_ = lean_uint8_land(v___x_703_, v___x_690_);
v___x_705_ = lean_uint8_dec_eq(v___x_704_, v___x_684_);
if (v___x_705_ == 0)
{
lean_dec(v___x_699_);
return v___x_705_;
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; uint8_t v___x_709_; uint8_t v___x_710_; 
v___x_706_ = lean_unsigned_to_nat(2u);
v___x_707_ = lean_nat_add(v_i_680_, v___x_706_);
v___x_708_ = lean_byte_array_fget(v_bytes_679_, v___x_707_);
lean_dec(v___x_707_);
v___x_709_ = lean_uint8_land(v___x_708_, v___x_690_);
v___x_710_ = lean_uint8_dec_eq(v___x_709_, v___x_684_);
if (v___x_710_ == 0)
{
lean_dec(v___x_699_);
return v___x_694_;
}
else
{
uint8_t v___x_711_; uint8_t v___x_712_; uint8_t v___x_713_; 
v___x_711_ = lean_byte_array_fget(v_bytes_679_, v___x_699_);
lean_dec(v___x_699_);
v___x_712_ = lean_uint8_land(v___x_711_, v___x_690_);
v___x_713_ = lean_uint8_dec_eq(v___x_712_, v___x_684_);
if (v___x_713_ == 0)
{
return v___x_694_;
}
else
{
uint8_t v___x_714_; uint8_t v_b_u2080_715_; uint8_t v___x_716_; uint8_t v_b_u2081_717_; uint8_t v_b_u2082_718_; uint8_t v_b_u2083_719_; uint32_t v___x_720_; uint32_t v___x_721_; uint32_t v___x_722_; uint32_t v___x_723_; uint32_t v___x_724_; uint32_t v___x_725_; uint32_t v___x_726_; uint32_t v___x_727_; uint32_t v___x_728_; uint32_t v___x_729_; uint32_t v___x_730_; uint32_t v___x_731_; uint32_t v_r_732_; uint32_t v___x_733_; uint8_t v___x_734_; 
v___x_714_ = 7;
v_b_u2080_715_ = lean_uint8_land(v___x_683_, v___x_714_);
v___x_716_ = 63;
v_b_u2081_717_ = lean_uint8_land(v___x_703_, v___x_716_);
v_b_u2082_718_ = lean_uint8_land(v___x_708_, v___x_716_);
v_b_u2083_719_ = lean_uint8_land(v___x_711_, v___x_716_);
v___x_720_ = lean_uint8_to_uint32(v_b_u2080_715_);
v___x_721_ = 18;
v___x_722_ = lean_uint32_shift_left(v___x_720_, v___x_721_);
v___x_723_ = lean_uint8_to_uint32(v_b_u2081_717_);
v___x_724_ = 12;
v___x_725_ = lean_uint32_shift_left(v___x_723_, v___x_724_);
v___x_726_ = lean_uint32_lor(v___x_722_, v___x_725_);
v___x_727_ = lean_uint8_to_uint32(v_b_u2082_718_);
v___x_728_ = 6;
v___x_729_ = lean_uint32_shift_left(v___x_727_, v___x_728_);
v___x_730_ = lean_uint32_lor(v___x_726_, v___x_729_);
v___x_731_ = lean_uint8_to_uint32(v_b_u2083_719_);
v_r_732_ = lean_uint32_lor(v___x_730_, v___x_731_);
v___x_733_ = 65536;
v___x_734_ = lean_uint32_dec_le(v___x_733_, v_r_732_);
if (v___x_734_ == 0)
{
return v___x_694_;
}
else
{
uint32_t v___x_735_; uint8_t v___x_736_; 
v___x_735_ = 1114111;
v___x_736_ = lean_uint32_dec_le(v_r_732_, v___x_735_);
return v___x_736_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_737_ = lean_unsigned_to_nat(2u);
v___x_738_ = lean_nat_add(v_i_680_, v___x_737_);
v___x_739_ = lean_nat_dec_lt(v___x_738_, v___x_681_);
if (v___x_739_ == 0)
{
lean_dec(v___x_738_);
return v___x_739_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; uint8_t v___x_743_; uint8_t v___x_744_; 
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_add(v_i_680_, v___x_740_);
v___x_742_ = lean_byte_array_fget(v_bytes_679_, v___x_741_);
lean_dec(v___x_741_);
v___x_743_ = lean_uint8_land(v___x_742_, v___x_690_);
v___x_744_ = lean_uint8_dec_eq(v___x_743_, v___x_684_);
if (v___x_744_ == 0)
{
lean_dec(v___x_738_);
return v___x_744_;
}
else
{
uint8_t v___x_745_; uint8_t v___x_746_; uint8_t v___x_747_; 
v___x_745_ = lean_byte_array_fget(v_bytes_679_, v___x_738_);
lean_dec(v___x_738_);
v___x_746_ = lean_uint8_land(v___x_745_, v___x_690_);
v___x_747_ = lean_uint8_dec_eq(v___x_746_, v___x_684_);
if (v___x_747_ == 0)
{
return v___x_691_;
}
else
{
uint8_t v___x_748_; uint8_t v_b_u2080_749_; uint8_t v___x_750_; uint8_t v_b_u2081_751_; uint8_t v_b_u2082_752_; uint32_t v___x_753_; uint32_t v___x_754_; uint32_t v___x_755_; uint32_t v___x_756_; uint32_t v___x_757_; uint32_t v___x_758_; uint32_t v___x_759_; uint32_t v___x_760_; uint32_t v_r_761_; uint32_t v___x_762_; uint8_t v___x_763_; 
v___x_748_ = 15;
v_b_u2080_749_ = lean_uint8_land(v___x_683_, v___x_748_);
v___x_750_ = 63;
v_b_u2081_751_ = lean_uint8_land(v___x_742_, v___x_750_);
v_b_u2082_752_ = lean_uint8_land(v___x_745_, v___x_750_);
v___x_753_ = lean_uint8_to_uint32(v_b_u2080_749_);
v___x_754_ = 12;
v___x_755_ = lean_uint32_shift_left(v___x_753_, v___x_754_);
v___x_756_ = lean_uint8_to_uint32(v_b_u2081_751_);
v___x_757_ = 6;
v___x_758_ = lean_uint32_shift_left(v___x_756_, v___x_757_);
v___x_759_ = lean_uint32_lor(v___x_755_, v___x_758_);
v___x_760_ = lean_uint8_to_uint32(v_b_u2082_752_);
v_r_761_ = lean_uint32_lor(v___x_759_, v___x_760_);
v___x_762_ = 2048;
v___x_763_ = lean_uint32_dec_le(v___x_762_, v_r_761_);
if (v___x_763_ == 0)
{
return v___x_691_;
}
else
{
uint32_t v___x_764_; uint8_t v___x_765_; 
v___x_764_ = 55296;
v___x_765_ = lean_uint32_dec_lt(v_r_761_, v___x_764_);
if (v___x_765_ == 0)
{
uint32_t v___x_766_; uint8_t v___x_767_; 
v___x_766_ = 57343;
v___x_767_ = lean_uint32_dec_lt(v___x_766_, v_r_761_);
return v___x_767_;
}
else
{
return v___x_765_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_768_ = lean_unsigned_to_nat(1u);
v___x_769_ = lean_nat_add(v_i_680_, v___x_768_);
v___x_770_ = lean_nat_dec_lt(v___x_769_, v___x_681_);
if (v___x_770_ == 0)
{
lean_dec(v___x_769_);
return v___x_770_;
}
else
{
uint8_t v___x_771_; uint8_t v___x_772_; uint8_t v___x_773_; 
v___x_771_ = lean_byte_array_fget(v_bytes_679_, v___x_769_);
lean_dec(v___x_769_);
v___x_772_ = lean_uint8_land(v___x_771_, v___x_690_);
v___x_773_ = lean_uint8_dec_eq(v___x_772_, v___x_684_);
if (v___x_773_ == 0)
{
return v___x_773_;
}
else
{
uint8_t v___x_774_; uint8_t v_b_u2080_775_; uint8_t v___x_776_; uint8_t v_b_u2081_777_; uint32_t v___x_778_; uint32_t v___x_779_; uint32_t v___x_780_; uint32_t v___x_781_; uint32_t v_r_782_; uint32_t v___x_783_; uint8_t v___x_784_; 
v___x_774_ = 31;
v_b_u2080_775_ = lean_uint8_land(v___x_683_, v___x_774_);
v___x_776_ = 63;
v_b_u2081_777_ = lean_uint8_land(v___x_771_, v___x_776_);
v___x_778_ = lean_uint8_to_uint32(v_b_u2080_775_);
v___x_779_ = 6;
v___x_780_ = lean_uint32_shift_left(v___x_778_, v___x_779_);
v___x_781_ = lean_uint8_to_uint32(v_b_u2081_777_);
v_r_782_ = lean_uint32_lor(v___x_780_, v___x_781_);
v___x_783_ = 128;
v___x_784_ = lean_uint32_dec_le(v___x_783_, v_r_782_);
return v___x_784_;
}
}
}
}
else
{
return v___x_682_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8At___boxed(lean_object* v_bytes_785_, lean_object* v_i_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_ByteArray_validateUTF8At(v_bytes_785_, v_i_786_);
lean_dec(v_i_786_);
lean_dec_ref(v_bytes_785_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t v_x_789_, lean_object* v_h__1_790_, lean_object* v_h__2_791_, lean_object* v_h__3_792_, lean_object* v_h__4_793_, lean_object* v_h__5_794_){
_start:
{
switch(v_x_789_)
{
case 0:
{
lean_object* v___x_795_; 
lean_dec(v_h__5_794_);
lean_dec(v_h__4_793_);
lean_dec(v_h__3_792_);
lean_dec(v_h__2_791_);
v___x_795_ = lean_apply_1(v_h__1_790_, lean_box(0));
return v___x_795_;
}
case 1:
{
lean_object* v___x_796_; 
lean_dec(v_h__5_794_);
lean_dec(v_h__4_793_);
lean_dec(v_h__3_792_);
lean_dec(v_h__1_790_);
v___x_796_ = lean_apply_1(v_h__2_791_, lean_box(0));
return v___x_796_;
}
case 2:
{
lean_object* v___x_797_; 
lean_dec(v_h__5_794_);
lean_dec(v_h__4_793_);
lean_dec(v_h__2_791_);
lean_dec(v_h__1_790_);
v___x_797_ = lean_apply_1(v_h__3_792_, lean_box(0));
return v___x_797_;
}
case 3:
{
lean_object* v___x_798_; 
lean_dec(v_h__5_794_);
lean_dec(v_h__3_792_);
lean_dec(v_h__2_791_);
lean_dec(v_h__1_790_);
v___x_798_ = lean_apply_1(v_h__4_793_, lean_box(0));
return v___x_798_;
}
default: 
{
lean_object* v___x_799_; 
lean_dec(v_h__4_793_);
lean_dec(v_h__3_792_);
lean_dec(v_h__2_791_);
lean_dec(v_h__1_790_);
v___x_799_ = lean_apply_1(v_h__5_794_, lean_box(0));
return v___x_799_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_800_, lean_object* v_h__1_801_, lean_object* v_h__2_802_, lean_object* v_h__3_803_, lean_object* v_h__4_804_, lean_object* v_h__5_805_){
_start:
{
uint8_t v_x_47__boxed_806_; lean_object* v_res_807_; 
v_x_47__boxed_806_ = lean_unbox(v_x_800_);
v_res_807_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(v_x_47__boxed_806_, v_h__1_801_, v_h__2_802_, v_h__3_803_, v_h__4_804_, v_h__5_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object* v_motive_808_, uint8_t v_x_809_, lean_object* v_h__1_810_, lean_object* v_h__2_811_, lean_object* v_h__3_812_, lean_object* v_h__4_813_, lean_object* v_h__5_814_){
_start:
{
switch(v_x_809_)
{
case 0:
{
lean_object* v___x_815_; 
lean_dec(v_h__5_814_);
lean_dec(v_h__4_813_);
lean_dec(v_h__3_812_);
lean_dec(v_h__2_811_);
v___x_815_ = lean_apply_1(v_h__1_810_, lean_box(0));
return v___x_815_;
}
case 1:
{
lean_object* v___x_816_; 
lean_dec(v_h__5_814_);
lean_dec(v_h__4_813_);
lean_dec(v_h__3_812_);
lean_dec(v_h__1_810_);
v___x_816_ = lean_apply_1(v_h__2_811_, lean_box(0));
return v___x_816_;
}
case 2:
{
lean_object* v___x_817_; 
lean_dec(v_h__5_814_);
lean_dec(v_h__4_813_);
lean_dec(v_h__2_811_);
lean_dec(v_h__1_810_);
v___x_817_ = lean_apply_1(v_h__3_812_, lean_box(0));
return v___x_817_;
}
case 3:
{
lean_object* v___x_818_; 
lean_dec(v_h__5_814_);
lean_dec(v_h__3_812_);
lean_dec(v_h__2_811_);
lean_dec(v_h__1_810_);
v___x_818_ = lean_apply_1(v_h__4_813_, lean_box(0));
return v___x_818_;
}
default: 
{
lean_object* v___x_819_; 
lean_dec(v_h__4_813_);
lean_dec(v_h__3_812_);
lean_dec(v_h__2_811_);
lean_dec(v_h__1_810_);
v___x_819_ = lean_apply_1(v_h__5_814_, lean_box(0));
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object* v_motive_820_, lean_object* v_x_821_, lean_object* v_h__1_822_, lean_object* v_h__2_823_, lean_object* v_h__3_824_, lean_object* v_h__4_825_, lean_object* v_h__5_826_){
_start:
{
uint8_t v_x_60__boxed_827_; lean_object* v_res_828_; 
v_x_60__boxed_827_ = lean_unbox(v_x_821_);
v_res_828_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(v_motive_820_, v_x_60__boxed_827_, v_h__1_822_, v_h__2_823_, v_h__3_824_, v_h__4_825_, v_h__5_826_);
return v_res_828_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar___redArg(lean_object* v_bytes_829_, lean_object* v_i_830_){
_start:
{
lean_object* v___x_831_; uint8_t v___x_832_; uint8_t v___x_833_; uint8_t v___x_834_; uint8_t v___x_835_; uint8_t v___x_836_; uint8_t v___x_837_; 
v___x_831_ = lean_byte_array_size(v_bytes_829_);
v___x_832_ = lean_nat_dec_lt(v_i_830_, v___x_831_);
v___x_833_ = lean_byte_array_fget(v_bytes_829_, v_i_830_);
v___x_834_ = 128;
v___x_835_ = lean_uint8_land(v___x_833_, v___x_834_);
v___x_836_ = 0;
v___x_837_ = lean_uint8_dec_eq(v___x_835_, v___x_836_);
if (v___x_837_ == 0)
{
uint8_t v___x_838_; uint8_t v___x_839_; uint8_t v___x_840_; uint8_t v___x_841_; 
v___x_838_ = 224;
v___x_839_ = lean_uint8_land(v___x_833_, v___x_838_);
v___x_840_ = 192;
v___x_841_ = lean_uint8_dec_eq(v___x_839_, v___x_840_);
if (v___x_841_ == 0)
{
uint8_t v___x_842_; uint8_t v___x_843_; uint8_t v___x_844_; 
v___x_842_ = 240;
v___x_843_ = lean_uint8_land(v___x_833_, v___x_842_);
v___x_844_ = lean_uint8_dec_eq(v___x_843_, v___x_838_);
if (v___x_844_ == 0)
{
uint8_t v___x_845_; uint8_t v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; uint8_t v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; uint8_t v___x_859_; uint8_t v___x_860_; uint8_t v___x_861_; uint8_t v___x_862_; uint8_t v___x_863_; uint8_t v___x_864_; uint8_t v_b_u2080_865_; uint8_t v___x_866_; uint8_t v_b_u2081_867_; uint8_t v_b_u2082_868_; uint8_t v_b_u2083_869_; uint32_t v___x_870_; uint32_t v___x_871_; uint32_t v___x_872_; uint32_t v___x_873_; uint32_t v___x_874_; uint32_t v___x_875_; uint32_t v___x_876_; uint32_t v___x_877_; uint32_t v___x_878_; uint32_t v___x_879_; uint32_t v___x_880_; uint32_t v___x_881_; uint32_t v_r_882_; uint32_t v___x_883_; uint8_t v___x_884_; uint32_t v___x_885_; uint8_t v___x_886_; 
v___x_845_ = 248;
v___x_846_ = lean_uint8_land(v___x_833_, v___x_845_);
v___x_847_ = lean_uint8_dec_eq(v___x_846_, v___x_842_);
v___x_848_ = lean_unsigned_to_nat(3u);
v___x_849_ = lean_nat_add(v_i_830_, v___x_848_);
v___x_850_ = lean_nat_dec_lt(v___x_849_, v___x_831_);
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = lean_nat_add(v_i_830_, v___x_851_);
v___x_853_ = lean_byte_array_fget(v_bytes_829_, v___x_852_);
lean_dec(v___x_852_);
v___x_854_ = lean_uint8_land(v___x_853_, v___x_840_);
v___x_855_ = lean_uint8_dec_eq(v___x_854_, v___x_834_);
v___x_856_ = lean_unsigned_to_nat(2u);
v___x_857_ = lean_nat_add(v_i_830_, v___x_856_);
v___x_858_ = lean_byte_array_fget(v_bytes_829_, v___x_857_);
lean_dec(v___x_857_);
v___x_859_ = lean_uint8_land(v___x_858_, v___x_840_);
v___x_860_ = lean_uint8_dec_eq(v___x_859_, v___x_834_);
v___x_861_ = lean_byte_array_fget(v_bytes_829_, v___x_849_);
lean_dec(v___x_849_);
v___x_862_ = lean_uint8_land(v___x_861_, v___x_840_);
v___x_863_ = lean_uint8_dec_eq(v___x_862_, v___x_834_);
v___x_864_ = 7;
v_b_u2080_865_ = lean_uint8_land(v___x_833_, v___x_864_);
v___x_866_ = 63;
v_b_u2081_867_ = lean_uint8_land(v___x_853_, v___x_866_);
v_b_u2082_868_ = lean_uint8_land(v___x_858_, v___x_866_);
v_b_u2083_869_ = lean_uint8_land(v___x_861_, v___x_866_);
v___x_870_ = lean_uint8_to_uint32(v_b_u2080_865_);
v___x_871_ = 18;
v___x_872_ = lean_uint32_shift_left(v___x_870_, v___x_871_);
v___x_873_ = lean_uint8_to_uint32(v_b_u2081_867_);
v___x_874_ = 12;
v___x_875_ = lean_uint32_shift_left(v___x_873_, v___x_874_);
v___x_876_ = lean_uint32_lor(v___x_872_, v___x_875_);
v___x_877_ = lean_uint8_to_uint32(v_b_u2082_868_);
v___x_878_ = 6;
v___x_879_ = lean_uint32_shift_left(v___x_877_, v___x_878_);
v___x_880_ = lean_uint32_lor(v___x_876_, v___x_879_);
v___x_881_ = lean_uint8_to_uint32(v_b_u2083_869_);
v_r_882_ = lean_uint32_lor(v___x_880_, v___x_881_);
v___x_883_ = 65536;
v___x_884_ = lean_uint32_dec_lt(v_r_882_, v___x_883_);
v___x_885_ = 1114111;
v___x_886_ = lean_uint32_dec_lt(v___x_885_, v_r_882_);
return v_r_882_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; uint8_t v___x_893_; uint8_t v___x_894_; uint8_t v___x_895_; uint8_t v___x_896_; uint8_t v___x_897_; uint8_t v___x_898_; uint8_t v_b_u2080_899_; uint8_t v___x_900_; uint8_t v_b_u2081_901_; uint8_t v_b_u2082_902_; uint32_t v___x_903_; uint32_t v___x_904_; uint32_t v___x_905_; uint32_t v___x_906_; uint32_t v___x_907_; uint32_t v___x_908_; uint32_t v___x_909_; uint32_t v___x_910_; uint32_t v_r_911_; uint32_t v___x_912_; uint8_t v___x_913_; uint32_t v___x_914_; uint8_t v___x_915_; 
v___x_887_ = lean_unsigned_to_nat(2u);
v___x_888_ = lean_nat_add(v_i_830_, v___x_887_);
v___x_889_ = lean_nat_dec_lt(v___x_888_, v___x_831_);
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_891_ = lean_nat_add(v_i_830_, v___x_890_);
v___x_892_ = lean_byte_array_fget(v_bytes_829_, v___x_891_);
lean_dec(v___x_891_);
v___x_893_ = lean_uint8_land(v___x_892_, v___x_840_);
v___x_894_ = lean_uint8_dec_eq(v___x_893_, v___x_834_);
v___x_895_ = lean_byte_array_fget(v_bytes_829_, v___x_888_);
lean_dec(v___x_888_);
v___x_896_ = lean_uint8_land(v___x_895_, v___x_840_);
v___x_897_ = lean_uint8_dec_eq(v___x_896_, v___x_834_);
v___x_898_ = 15;
v_b_u2080_899_ = lean_uint8_land(v___x_833_, v___x_898_);
v___x_900_ = 63;
v_b_u2081_901_ = lean_uint8_land(v___x_892_, v___x_900_);
v_b_u2082_902_ = lean_uint8_land(v___x_895_, v___x_900_);
v___x_903_ = lean_uint8_to_uint32(v_b_u2080_899_);
v___x_904_ = 12;
v___x_905_ = lean_uint32_shift_left(v___x_903_, v___x_904_);
v___x_906_ = lean_uint8_to_uint32(v_b_u2081_901_);
v___x_907_ = 6;
v___x_908_ = lean_uint32_shift_left(v___x_906_, v___x_907_);
v___x_909_ = lean_uint32_lor(v___x_905_, v___x_908_);
v___x_910_ = lean_uint8_to_uint32(v_b_u2082_902_);
v_r_911_ = lean_uint32_lor(v___x_909_, v___x_910_);
v___x_912_ = 2048;
v___x_913_ = lean_uint32_dec_lt(v_r_911_, v___x_912_);
v___x_914_ = 55296;
v___x_915_ = lean_uint32_dec_le(v___x_914_, v_r_911_);
if (v___x_915_ == 0)
{
return v_r_911_;
}
else
{
uint32_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = 57343;
v___x_917_ = lean_uint32_dec_le(v_r_911_, v___x_916_);
return v_r_911_;
}
}
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; uint8_t v___x_921_; uint8_t v___x_922_; uint8_t v___x_923_; uint8_t v___x_924_; uint8_t v_b_u2080_925_; uint8_t v___x_926_; uint8_t v_b_u2081_927_; uint32_t v___x_928_; uint32_t v___x_929_; uint32_t v___x_930_; uint32_t v___x_931_; uint32_t v_r_932_; uint32_t v___x_933_; uint8_t v___x_934_; 
v___x_918_ = lean_unsigned_to_nat(1u);
v___x_919_ = lean_nat_add(v_i_830_, v___x_918_);
v___x_920_ = lean_nat_dec_lt(v___x_919_, v___x_831_);
v___x_921_ = lean_byte_array_fget(v_bytes_829_, v___x_919_);
lean_dec(v___x_919_);
v___x_922_ = lean_uint8_land(v___x_921_, v___x_840_);
v___x_923_ = lean_uint8_dec_eq(v___x_922_, v___x_834_);
v___x_924_ = 31;
v_b_u2080_925_ = lean_uint8_land(v___x_833_, v___x_924_);
v___x_926_ = 63;
v_b_u2081_927_ = lean_uint8_land(v___x_921_, v___x_926_);
v___x_928_ = lean_uint8_to_uint32(v_b_u2080_925_);
v___x_929_ = 6;
v___x_930_ = lean_uint32_shift_left(v___x_928_, v___x_929_);
v___x_931_ = lean_uint8_to_uint32(v_b_u2081_927_);
v_r_932_ = lean_uint32_lor(v___x_930_, v___x_931_);
v___x_933_ = 128;
v___x_934_ = lean_uint32_dec_lt(v_r_932_, v___x_933_);
return v_r_932_;
}
}
else
{
uint32_t v___x_935_; 
v___x_935_ = lean_uint8_to_uint32(v___x_833_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___redArg___boxed(lean_object* v_bytes_936_, lean_object* v_i_937_){
_start:
{
uint32_t v_res_938_; lean_object* v_r_939_; 
v_res_938_ = l_ByteArray_utf8DecodeChar___redArg(v_bytes_936_, v_i_937_);
lean_dec(v_i_937_);
lean_dec_ref(v_bytes_936_);
v_r_939_ = lean_box_uint32(v_res_938_);
return v_r_939_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar(lean_object* v_bytes_940_, lean_object* v_i_941_, lean_object* v_h_942_){
_start:
{
lean_object* v___x_943_; uint8_t v___x_944_; uint8_t v___x_945_; uint8_t v___x_946_; uint8_t v___x_947_; uint8_t v___x_948_; uint8_t v___x_949_; 
v___x_943_ = lean_byte_array_size(v_bytes_940_);
v___x_944_ = lean_nat_dec_lt(v_i_941_, v___x_943_);
v___x_945_ = lean_byte_array_fget(v_bytes_940_, v_i_941_);
v___x_946_ = 128;
v___x_947_ = lean_uint8_land(v___x_945_, v___x_946_);
v___x_948_ = 0;
v___x_949_ = lean_uint8_dec_eq(v___x_947_, v___x_948_);
if (v___x_949_ == 0)
{
uint8_t v___x_950_; uint8_t v___x_951_; uint8_t v___x_952_; uint8_t v___x_953_; 
v___x_950_ = 224;
v___x_951_ = lean_uint8_land(v___x_945_, v___x_950_);
v___x_952_ = 192;
v___x_953_ = lean_uint8_dec_eq(v___x_951_, v___x_952_);
if (v___x_953_ == 0)
{
uint8_t v___x_954_; uint8_t v___x_955_; uint8_t v___x_956_; 
v___x_954_ = 240;
v___x_955_ = lean_uint8_land(v___x_945_, v___x_954_);
v___x_956_ = lean_uint8_dec_eq(v___x_955_, v___x_950_);
if (v___x_956_ == 0)
{
uint8_t v___x_957_; uint8_t v___x_958_; uint8_t v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; uint8_t v___x_966_; uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; uint8_t v___x_971_; uint8_t v___x_972_; uint8_t v___x_973_; uint8_t v___x_974_; uint8_t v___x_975_; uint8_t v___x_976_; uint8_t v_b_u2080_977_; uint8_t v___x_978_; uint8_t v_b_u2081_979_; uint8_t v_b_u2082_980_; uint8_t v_b_u2083_981_; uint32_t v___x_982_; uint32_t v___x_983_; uint32_t v___x_984_; uint32_t v___x_985_; uint32_t v___x_986_; uint32_t v___x_987_; uint32_t v___x_988_; uint32_t v___x_989_; uint32_t v___x_990_; uint32_t v___x_991_; uint32_t v___x_992_; uint32_t v___x_993_; uint32_t v_r_994_; uint32_t v___x_995_; uint8_t v___x_996_; uint32_t v___x_997_; uint8_t v___x_998_; 
v___x_957_ = 248;
v___x_958_ = lean_uint8_land(v___x_945_, v___x_957_);
v___x_959_ = lean_uint8_dec_eq(v___x_958_, v___x_954_);
v___x_960_ = lean_unsigned_to_nat(3u);
v___x_961_ = lean_nat_add(v_i_941_, v___x_960_);
v___x_962_ = lean_nat_dec_lt(v___x_961_, v___x_943_);
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = lean_nat_add(v_i_941_, v___x_963_);
v___x_965_ = lean_byte_array_fget(v_bytes_940_, v___x_964_);
lean_dec(v___x_964_);
v___x_966_ = lean_uint8_land(v___x_965_, v___x_952_);
v___x_967_ = lean_uint8_dec_eq(v___x_966_, v___x_946_);
v___x_968_ = lean_unsigned_to_nat(2u);
v___x_969_ = lean_nat_add(v_i_941_, v___x_968_);
v___x_970_ = lean_byte_array_fget(v_bytes_940_, v___x_969_);
lean_dec(v___x_969_);
v___x_971_ = lean_uint8_land(v___x_970_, v___x_952_);
v___x_972_ = lean_uint8_dec_eq(v___x_971_, v___x_946_);
v___x_973_ = lean_byte_array_fget(v_bytes_940_, v___x_961_);
lean_dec(v___x_961_);
v___x_974_ = lean_uint8_land(v___x_973_, v___x_952_);
v___x_975_ = lean_uint8_dec_eq(v___x_974_, v___x_946_);
v___x_976_ = 7;
v_b_u2080_977_ = lean_uint8_land(v___x_945_, v___x_976_);
v___x_978_ = 63;
v_b_u2081_979_ = lean_uint8_land(v___x_965_, v___x_978_);
v_b_u2082_980_ = lean_uint8_land(v___x_970_, v___x_978_);
v_b_u2083_981_ = lean_uint8_land(v___x_973_, v___x_978_);
v___x_982_ = lean_uint8_to_uint32(v_b_u2080_977_);
v___x_983_ = 18;
v___x_984_ = lean_uint32_shift_left(v___x_982_, v___x_983_);
v___x_985_ = lean_uint8_to_uint32(v_b_u2081_979_);
v___x_986_ = 12;
v___x_987_ = lean_uint32_shift_left(v___x_985_, v___x_986_);
v___x_988_ = lean_uint32_lor(v___x_984_, v___x_987_);
v___x_989_ = lean_uint8_to_uint32(v_b_u2082_980_);
v___x_990_ = 6;
v___x_991_ = lean_uint32_shift_left(v___x_989_, v___x_990_);
v___x_992_ = lean_uint32_lor(v___x_988_, v___x_991_);
v___x_993_ = lean_uint8_to_uint32(v_b_u2083_981_);
v_r_994_ = lean_uint32_lor(v___x_992_, v___x_993_);
v___x_995_ = 65536;
v___x_996_ = lean_uint32_dec_lt(v_r_994_, v___x_995_);
v___x_997_ = 1114111;
v___x_998_ = lean_uint32_dec_lt(v___x_997_, v_r_994_);
return v_r_994_;
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; uint8_t v___x_1005_; uint8_t v___x_1006_; uint8_t v___x_1007_; uint8_t v___x_1008_; uint8_t v___x_1009_; uint8_t v___x_1010_; uint8_t v_b_u2080_1011_; uint8_t v___x_1012_; uint8_t v_b_u2081_1013_; uint8_t v_b_u2082_1014_; uint32_t v___x_1015_; uint32_t v___x_1016_; uint32_t v___x_1017_; uint32_t v___x_1018_; uint32_t v___x_1019_; uint32_t v___x_1020_; uint32_t v___x_1021_; uint32_t v___x_1022_; uint32_t v_r_1023_; uint32_t v___x_1024_; uint8_t v___x_1025_; uint32_t v___x_1026_; uint8_t v___x_1027_; 
v___x_999_ = lean_unsigned_to_nat(2u);
v___x_1000_ = lean_nat_add(v_i_941_, v___x_999_);
v___x_1001_ = lean_nat_dec_lt(v___x_1000_, v___x_943_);
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_nat_add(v_i_941_, v___x_1002_);
v___x_1004_ = lean_byte_array_fget(v_bytes_940_, v___x_1003_);
lean_dec(v___x_1003_);
v___x_1005_ = lean_uint8_land(v___x_1004_, v___x_952_);
v___x_1006_ = lean_uint8_dec_eq(v___x_1005_, v___x_946_);
v___x_1007_ = lean_byte_array_fget(v_bytes_940_, v___x_1000_);
lean_dec(v___x_1000_);
v___x_1008_ = lean_uint8_land(v___x_1007_, v___x_952_);
v___x_1009_ = lean_uint8_dec_eq(v___x_1008_, v___x_946_);
v___x_1010_ = 15;
v_b_u2080_1011_ = lean_uint8_land(v___x_945_, v___x_1010_);
v___x_1012_ = 63;
v_b_u2081_1013_ = lean_uint8_land(v___x_1004_, v___x_1012_);
v_b_u2082_1014_ = lean_uint8_land(v___x_1007_, v___x_1012_);
v___x_1015_ = lean_uint8_to_uint32(v_b_u2080_1011_);
v___x_1016_ = 12;
v___x_1017_ = lean_uint32_shift_left(v___x_1015_, v___x_1016_);
v___x_1018_ = lean_uint8_to_uint32(v_b_u2081_1013_);
v___x_1019_ = 6;
v___x_1020_ = lean_uint32_shift_left(v___x_1018_, v___x_1019_);
v___x_1021_ = lean_uint32_lor(v___x_1017_, v___x_1020_);
v___x_1022_ = lean_uint8_to_uint32(v_b_u2082_1014_);
v_r_1023_ = lean_uint32_lor(v___x_1021_, v___x_1022_);
v___x_1024_ = 2048;
v___x_1025_ = lean_uint32_dec_lt(v_r_1023_, v___x_1024_);
v___x_1026_ = 55296;
v___x_1027_ = lean_uint32_dec_le(v___x_1026_, v_r_1023_);
if (v___x_1027_ == 0)
{
return v_r_1023_;
}
else
{
uint32_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = 57343;
v___x_1029_ = lean_uint32_dec_le(v_r_1023_, v___x_1028_);
return v_r_1023_;
}
}
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; uint8_t v___x_1033_; uint8_t v___x_1034_; uint8_t v___x_1035_; uint8_t v___x_1036_; uint8_t v_b_u2080_1037_; uint8_t v___x_1038_; uint8_t v_b_u2081_1039_; uint32_t v___x_1040_; uint32_t v___x_1041_; uint32_t v___x_1042_; uint32_t v___x_1043_; uint32_t v_r_1044_; uint32_t v___x_1045_; uint8_t v___x_1046_; 
v___x_1030_ = lean_unsigned_to_nat(1u);
v___x_1031_ = lean_nat_add(v_i_941_, v___x_1030_);
v___x_1032_ = lean_nat_dec_lt(v___x_1031_, v___x_943_);
v___x_1033_ = lean_byte_array_fget(v_bytes_940_, v___x_1031_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_uint8_land(v___x_1033_, v___x_952_);
v___x_1035_ = lean_uint8_dec_eq(v___x_1034_, v___x_946_);
v___x_1036_ = 31;
v_b_u2080_1037_ = lean_uint8_land(v___x_945_, v___x_1036_);
v___x_1038_ = 63;
v_b_u2081_1039_ = lean_uint8_land(v___x_1033_, v___x_1038_);
v___x_1040_ = lean_uint8_to_uint32(v_b_u2080_1037_);
v___x_1041_ = 6;
v___x_1042_ = lean_uint32_shift_left(v___x_1040_, v___x_1041_);
v___x_1043_ = lean_uint8_to_uint32(v_b_u2081_1039_);
v_r_1044_ = lean_uint32_lor(v___x_1042_, v___x_1043_);
v___x_1045_ = 128;
v___x_1046_ = lean_uint32_dec_lt(v_r_1044_, v___x_1045_);
return v_r_1044_;
}
}
else
{
uint32_t v___x_1047_; 
v___x_1047_ = lean_uint8_to_uint32(v___x_945_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___boxed(lean_object* v_bytes_1048_, lean_object* v_i_1049_, lean_object* v_h_1050_){
_start:
{
uint32_t v_res_1051_; lean_object* v_r_1052_; 
v_res_1051_ = l_ByteArray_utf8DecodeChar(v_bytes_1048_, v_i_1049_, v_h_1050_);
lean_dec(v_i_1049_);
lean_dec_ref(v_bytes_1048_);
v_r_1052_ = lean_box_uint32(v_res_1051_);
return v_r_1052_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableIsUTF8FirstByte(uint8_t v_c_1053_){
_start:
{
uint8_t v___x_1054_; uint8_t v___x_1055_; uint8_t v___x_1056_; uint8_t v___x_1057_; 
v___x_1054_ = 128;
v___x_1055_ = lean_uint8_land(v_c_1053_, v___x_1054_);
v___x_1056_ = 0;
v___x_1057_ = lean_uint8_dec_eq(v___x_1055_, v___x_1056_);
if (v___x_1057_ == 0)
{
uint8_t v___x_1058_; uint8_t v___x_1059_; uint8_t v___x_1060_; uint8_t v___x_1061_; 
v___x_1058_ = 224;
v___x_1059_ = lean_uint8_land(v_c_1053_, v___x_1058_);
v___x_1060_ = 192;
v___x_1061_ = lean_uint8_dec_eq(v___x_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
uint8_t v___x_1062_; uint8_t v___x_1063_; uint8_t v___x_1064_; 
v___x_1062_ = 240;
v___x_1063_ = lean_uint8_land(v_c_1053_, v___x_1062_);
v___x_1064_ = lean_uint8_dec_eq(v___x_1063_, v___x_1058_);
if (v___x_1064_ == 0)
{
uint8_t v___x_1065_; uint8_t v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = 248;
v___x_1066_ = lean_uint8_land(v_c_1053_, v___x_1065_);
v___x_1067_ = lean_uint8_dec_eq(v___x_1066_, v___x_1062_);
return v___x_1067_;
}
else
{
return v___x_1064_;
}
}
else
{
return v___x_1061_;
}
}
else
{
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableIsUTF8FirstByte___boxed(lean_object* v_c_1068_){
_start:
{
uint8_t v_c_boxed_1069_; uint8_t v_res_1070_; lean_object* v_r_1071_; 
v_c_boxed_1069_ = lean_unbox(v_c_1068_);
v_res_1070_ = l_UInt8_instDecidableIsUTF8FirstByte(v_c_boxed_1069_);
v_r_1071_ = lean_box(v_res_1070_);
return v_r_1071_;
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg(uint8_t v_c_1072_){
_start:
{
uint8_t v___x_1073_; uint8_t v___x_1074_; uint8_t v___x_1075_; uint8_t v___x_1076_; 
v___x_1073_ = 128;
v___x_1074_ = lean_uint8_land(v_c_1072_, v___x_1073_);
v___x_1075_ = 0;
v___x_1076_ = lean_uint8_dec_eq(v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
uint8_t v___x_1077_; uint8_t v___x_1078_; uint8_t v___x_1079_; uint8_t v___x_1080_; 
v___x_1077_ = 224;
v___x_1078_ = lean_uint8_land(v_c_1072_, v___x_1077_);
v___x_1079_ = 192;
v___x_1080_ = lean_uint8_dec_eq(v___x_1078_, v___x_1079_);
if (v___x_1080_ == 0)
{
uint8_t v___x_1081_; uint8_t v___x_1082_; uint8_t v___x_1083_; 
v___x_1081_ = 240;
v___x_1082_ = lean_uint8_land(v_c_1072_, v___x_1081_);
v___x_1083_ = lean_uint8_dec_eq(v___x_1082_, v___x_1077_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_unsigned_to_nat(4u);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_unsigned_to_nat(3u);
return v___x_1085_;
}
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_unsigned_to_nat(2u);
return v___x_1086_;
}
}
else
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_unsigned_to_nat(1u);
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg___boxed(lean_object* v_c_1088_){
_start:
{
uint8_t v_c_boxed_1089_; lean_object* v_res_1090_; 
v_c_boxed_1089_ = lean_unbox(v_c_1088_);
v_res_1090_ = l_UInt8_utf8ByteSize___redArg(v_c_boxed_1089_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize(uint8_t v_c_1091_, lean_object* v___h_1092_){
_start:
{
uint8_t v___x_1093_; uint8_t v___x_1094_; uint8_t v___x_1095_; uint8_t v___x_1096_; 
v___x_1093_ = 128;
v___x_1094_ = lean_uint8_land(v_c_1091_, v___x_1093_);
v___x_1095_ = 0;
v___x_1096_ = lean_uint8_dec_eq(v___x_1094_, v___x_1095_);
if (v___x_1096_ == 0)
{
uint8_t v___x_1097_; uint8_t v___x_1098_; uint8_t v___x_1099_; uint8_t v___x_1100_; 
v___x_1097_ = 224;
v___x_1098_ = lean_uint8_land(v_c_1091_, v___x_1097_);
v___x_1099_ = 192;
v___x_1100_ = lean_uint8_dec_eq(v___x_1098_, v___x_1099_);
if (v___x_1100_ == 0)
{
uint8_t v___x_1101_; uint8_t v___x_1102_; uint8_t v___x_1103_; 
v___x_1101_ = 240;
v___x_1102_ = lean_uint8_land(v_c_1091_, v___x_1101_);
v___x_1103_ = lean_uint8_dec_eq(v___x_1102_, v___x_1097_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_unsigned_to_nat(4u);
return v___x_1104_;
}
else
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_unsigned_to_nat(3u);
return v___x_1105_;
}
}
else
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_unsigned_to_nat(2u);
return v___x_1106_;
}
}
else
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_unsigned_to_nat(1u);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___boxed(lean_object* v_c_1108_, lean_object* v___h_1109_){
_start:
{
uint8_t v_c_boxed_1110_; lean_object* v_res_1111_; 
v_c_boxed_1110_ = lean_unbox(v_c_1108_);
v_res_1111_ = l_UInt8_utf8ByteSize(v_c_boxed_1110_, v___h_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(uint8_t v_x_1112_){
_start:
{
switch(v_x_1112_)
{
case 0:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_unsigned_to_nat(0u);
return v___x_1113_;
}
case 1:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_unsigned_to_nat(1u);
return v___x_1114_;
}
case 2:
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_unsigned_to_nat(2u);
return v___x_1115_;
}
case 3:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_unsigned_to_nat(3u);
return v___x_1116_;
}
default: 
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_unsigned_to_nat(4u);
return v___x_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize___boxed(lean_object* v_x_1118_){
_start:
{
uint8_t v_x_54__boxed_1119_; lean_object* v_res_1120_; 
v_x_54__boxed_1119_ = lean_unbox(v_x_1118_);
v_res_1120_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(v_x_54__boxed_1119_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(uint8_t v_x_1121_, lean_object* v_h__1_1122_, lean_object* v_h__2_1123_, lean_object* v_h__3_1124_, lean_object* v_h__4_1125_, lean_object* v_h__5_1126_){
_start:
{
switch(v_x_1121_)
{
case 0:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_dec(v_h__5_1126_);
lean_dec(v_h__4_1125_);
lean_dec(v_h__3_1124_);
lean_dec(v_h__2_1123_);
v___x_1127_ = lean_box(0);
v___x_1128_ = lean_apply_1(v_h__1_1122_, v___x_1127_);
return v___x_1128_;
}
case 1:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec(v_h__5_1126_);
lean_dec(v_h__4_1125_);
lean_dec(v_h__3_1124_);
lean_dec(v_h__1_1122_);
v___x_1129_ = lean_box(0);
v___x_1130_ = lean_apply_1(v_h__2_1123_, v___x_1129_);
return v___x_1130_;
}
case 2:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec(v_h__5_1126_);
lean_dec(v_h__4_1125_);
lean_dec(v_h__2_1123_);
lean_dec(v_h__1_1122_);
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_apply_1(v_h__3_1124_, v___x_1131_);
return v___x_1132_;
}
case 3:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v_h__5_1126_);
lean_dec(v_h__3_1124_);
lean_dec(v_h__2_1123_);
lean_dec(v_h__1_1122_);
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_apply_1(v_h__4_1125_, v___x_1133_);
return v___x_1134_;
}
default: 
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec(v_h__4_1125_);
lean_dec(v_h__3_1124_);
lean_dec(v_h__2_1123_);
lean_dec(v_h__1_1122_);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_apply_1(v_h__5_1126_, v___x_1135_);
return v___x_1136_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg___boxed(lean_object* v_x_1137_, lean_object* v_h__1_1138_, lean_object* v_h__2_1139_, lean_object* v_h__3_1140_, lean_object* v_h__4_1141_, lean_object* v_h__5_1142_){
_start:
{
uint8_t v_x_51__boxed_1143_; lean_object* v_res_1144_; 
v_x_51__boxed_1143_ = lean_unbox(v_x_1137_);
v_res_1144_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(v_x_51__boxed_1143_, v_h__1_1138_, v_h__2_1139_, v_h__3_1140_, v_h__4_1141_, v_h__5_1142_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(lean_object* v_motive_1145_, uint8_t v_x_1146_, lean_object* v_h__1_1147_, lean_object* v_h__2_1148_, lean_object* v_h__3_1149_, lean_object* v_h__4_1150_, lean_object* v_h__5_1151_){
_start:
{
switch(v_x_1146_)
{
case 0:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec(v_h__5_1151_);
lean_dec(v_h__4_1150_);
lean_dec(v_h__3_1149_);
lean_dec(v_h__2_1148_);
v___x_1152_ = lean_box(0);
v___x_1153_ = lean_apply_1(v_h__1_1147_, v___x_1152_);
return v___x_1153_;
}
case 1:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec(v_h__5_1151_);
lean_dec(v_h__4_1150_);
lean_dec(v_h__3_1149_);
lean_dec(v_h__1_1147_);
v___x_1154_ = lean_box(0);
v___x_1155_ = lean_apply_1(v_h__2_1148_, v___x_1154_);
return v___x_1155_;
}
case 2:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec(v_h__5_1151_);
lean_dec(v_h__4_1150_);
lean_dec(v_h__2_1148_);
lean_dec(v_h__1_1147_);
v___x_1156_ = lean_box(0);
v___x_1157_ = lean_apply_1(v_h__3_1149_, v___x_1156_);
return v___x_1157_;
}
case 3:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_dec(v_h__5_1151_);
lean_dec(v_h__3_1149_);
lean_dec(v_h__2_1148_);
lean_dec(v_h__1_1147_);
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_apply_1(v_h__4_1150_, v___x_1158_);
return v___x_1159_;
}
default: 
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v_h__4_1150_);
lean_dec(v_h__3_1149_);
lean_dec(v_h__2_1148_);
lean_dec(v_h__1_1147_);
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_apply_1(v_h__5_1151_, v___x_1160_);
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___boxed(lean_object* v_motive_1162_, lean_object* v_x_1163_, lean_object* v_h__1_1164_, lean_object* v_h__2_1165_, lean_object* v_h__3_1166_, lean_object* v_h__4_1167_, lean_object* v_h__5_1168_){
_start:
{
uint8_t v_x_74__boxed_1169_; lean_object* v_res_1170_; 
v_x_74__boxed_1169_ = lean_unbox(v_x_1163_);
v_res_1170_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(v_motive_1162_, v_x_74__boxed_1169_, v_h__1_1164_, v_h__2_1165_, v_h__3_1166_, v_h__4_1167_, v_h__5_1168_);
return v_res_1170_;
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

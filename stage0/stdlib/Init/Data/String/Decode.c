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
LEAN_EXPORT uint8_t l_UInt8_isUTF8ContinuationByte(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_isUTF8ContinuationByte___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String_Internal_utf8DecodeList(lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8At(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8At___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__10_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__10_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__6_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__6_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__8_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__8_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_UInt8_isUTF8ContinuationByte(uint8_t v_b_197_){
_start:
{
uint8_t v___x_198_; uint8_t v___x_199_; uint8_t v___x_200_; uint8_t v___x_201_; 
v___x_198_ = 192;
v___x_199_ = lean_uint8_land(v_b_197_, v___x_198_);
v___x_200_ = 128;
v___x_201_ = lean_uint8_dec_eq(v___x_199_, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_UInt8_isUTF8ContinuationByte___boxed(lean_object* v_b_202_){
_start:
{
uint8_t v_b_boxed_203_; uint8_t v_res_204_; lean_object* v_r_205_; 
v_b_boxed_203_ = lean_unbox(v_b_202_);
v_res_204_ = l_UInt8_isUTF8ContinuationByte(v_b_boxed_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(uint8_t v_w_206_){
_start:
{
uint32_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_uint8_to_uint32(v_w_206_);
v___x_208_ = lean_box_uint32(v___x_207_);
v___x_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg___boxed(lean_object* v_w_210_){
_start:
{
uint8_t v_w_boxed_211_; lean_object* v_res_212_; 
v_w_boxed_211_ = lean_unbox(v_w_210_);
v_res_212_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(v_w_boxed_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(uint8_t v_w_213_, lean_object* v_h_214_){
_start:
{
uint32_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_uint8_to_uint32(v_w_213_);
v___x_216_ = lean_box_uint32(v___x_215_);
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___boxed(lean_object* v_w_218_, lean_object* v_h_219_){
_start:
{
uint8_t v_w_boxed_220_; lean_object* v_res_221_; 
v_w_boxed_220_ = lean_unbox(v_w_218_);
v_res_221_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(v_w_boxed_220_, v_h_219_);
return v_res_221_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg(){
_start:
{
uint8_t v___x_223_; 
v___x_223_ = 1;
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg___boxed(lean_object* v___dummy_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg();
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
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
uint8_t v___x_380_; uint8_t v___x_381_; uint8_t v___x_382_; 
v___x_380_ = 0;
v___x_381_ = lean_uint8_land(v_y_375_, v___x_376_);
v___x_382_ = lean_uint8_dec_eq(v___x_381_, v___x_378_);
if (v___x_382_ == 0)
{
return v___x_380_;
}
else
{
uint8_t v___x_383_; uint8_t v_b_u2080_384_; uint8_t v___x_385_; uint8_t v_b_u2081_386_; uint8_t v_b_u2082_387_; uint32_t v___x_388_; uint32_t v___x_389_; uint32_t v___x_390_; uint32_t v___x_391_; uint32_t v___x_392_; uint32_t v___x_393_; uint32_t v___x_394_; uint32_t v___x_395_; uint32_t v_r_396_; uint32_t v___x_397_; uint8_t v___x_398_; 
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
return v___x_380_;
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
return v___x_402_;
}
else
{
return v___x_400_;
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
uint8_t v___x_503_; uint8_t v___x_504_; uint8_t v___x_505_; 
v___x_503_ = 0;
v___x_504_ = lean_uint8_land(v_y_497_, v___x_499_);
v___x_505_ = lean_uint8_dec_eq(v___x_504_, v___x_501_);
if (v___x_505_ == 0)
{
return v___x_503_;
}
else
{
uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_uint8_land(v_z_498_, v___x_499_);
v___x_507_ = lean_uint8_dec_eq(v___x_506_, v___x_501_);
if (v___x_507_ == 0)
{
return v___x_503_;
}
else
{
uint8_t v___x_508_; uint8_t v_b_u2080_509_; uint8_t v___x_510_; uint8_t v_b_u2081_511_; uint8_t v_b_u2082_512_; uint8_t v_b_u2083_513_; uint32_t v___x_514_; uint32_t v___x_515_; uint32_t v___x_516_; uint32_t v___x_517_; uint32_t v___x_518_; uint32_t v___x_519_; uint32_t v___x_520_; uint32_t v___x_521_; uint32_t v___x_522_; uint32_t v___x_523_; uint32_t v___x_524_; uint32_t v___x_525_; uint32_t v_r_526_; uint32_t v___x_527_; uint8_t v___x_528_; 
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
return v___x_503_;
}
else
{
uint32_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = 1114111;
v___x_530_ = lean_uint32_dec_le(v_r_526_, v___x_529_);
return v___x_530_;
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
LEAN_EXPORT lean_object* l_String_Internal_utf8DecodeList(lean_object* v_x_677_){
_start:
{
if (lean_obj_tag(v_x_677_) == 0)
{
lean_object* v___x_678_; 
v___x_678_ = lean_box(0);
return v___x_678_;
}
else
{
lean_object* v_head_679_; lean_object* v_tail_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_848_; 
v_head_679_ = lean_ctor_get(v_x_677_, 0);
v_tail_680_ = lean_ctor_get(v_x_677_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_x_677_);
if (v_isSharedCheck_848_ == 0)
{
v___x_682_ = v_x_677_;
v_isShared_683_ = v_isSharedCheck_848_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_tail_680_);
lean_inc(v_head_679_);
lean_dec(v_x_677_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_848_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
uint8_t v___x_684_; uint8_t v___x_685_; uint8_t v___x_686_; uint8_t v___x_687_; uint8_t v___x_688_; 
v___x_684_ = 128;
v___x_685_ = lean_unbox(v_head_679_);
v___x_686_ = lean_uint8_land(v___x_685_, v___x_684_);
v___x_687_ = 0;
v___x_688_ = lean_uint8_dec_eq(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
uint8_t v___x_689_; uint8_t v___x_690_; uint8_t v___x_691_; uint8_t v___x_692_; uint8_t v___x_693_; 
lean_del_object(v___x_682_);
v___x_689_ = 224;
v___x_690_ = lean_unbox(v_head_679_);
v___x_691_ = lean_uint8_land(v___x_690_, v___x_689_);
v___x_692_ = 192;
v___x_693_ = lean_uint8_dec_eq(v___x_691_, v___x_692_);
if (v___x_693_ == 0)
{
uint8_t v___x_694_; uint8_t v___x_695_; uint8_t v___x_696_; uint8_t v___x_697_; 
v___x_694_ = 240;
v___x_695_ = lean_unbox(v_head_679_);
v___x_696_ = lean_uint8_land(v___x_695_, v___x_694_);
v___x_697_ = lean_uint8_dec_eq(v___x_696_, v___x_689_);
if (v___x_697_ == 0)
{
uint8_t v___x_698_; uint8_t v___x_699_; uint8_t v___x_700_; uint8_t v___x_701_; 
v___x_698_ = 248;
v___x_699_ = lean_unbox(v_head_679_);
v___x_700_ = lean_uint8_land(v___x_699_, v___x_698_);
v___x_701_ = lean_uint8_dec_eq(v___x_700_, v___x_694_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
lean_dec(v_tail_680_);
lean_dec(v_head_679_);
v___x_702_ = lean_box(0);
return v___x_702_;
}
else
{
if (lean_obj_tag(v_tail_680_) == 1)
{
lean_object* v_tail_703_; 
v_tail_703_ = lean_ctor_get(v_tail_680_, 1);
lean_inc(v_tail_703_);
if (lean_obj_tag(v_tail_703_) == 1)
{
lean_object* v_tail_704_; 
v_tail_704_ = lean_ctor_get(v_tail_703_, 1);
lean_inc(v_tail_704_);
if (lean_obj_tag(v_tail_704_) == 1)
{
lean_object* v_head_705_; lean_object* v_head_706_; lean_object* v_head_707_; lean_object* v_tail_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_758_; 
v_head_705_ = lean_ctor_get(v_tail_680_, 0);
lean_inc(v_head_705_);
lean_dec_ref_known(v_tail_680_, 2);
v_head_706_ = lean_ctor_get(v_tail_703_, 0);
lean_inc(v_head_706_);
lean_dec_ref_known(v_tail_703_, 2);
v_head_707_ = lean_ctor_get(v_tail_704_, 0);
v_tail_708_ = lean_ctor_get(v_tail_704_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_tail_704_);
if (v_isSharedCheck_758_ == 0)
{
v___x_710_ = v_tail_704_;
v_isShared_711_ = v_isSharedCheck_758_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_tail_708_);
lean_inc(v_head_707_);
lean_dec(v_tail_704_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_758_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
uint8_t v___x_712_; uint8_t v___x_713_; uint8_t v___x_714_; 
v___x_712_ = lean_unbox(v_head_705_);
v___x_713_ = lean_uint8_land(v___x_712_, v___x_692_);
v___x_714_ = lean_uint8_dec_eq(v___x_713_, v___x_684_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
lean_del_object(v___x_710_);
lean_dec(v_tail_708_);
lean_dec(v_head_707_);
lean_dec(v_head_706_);
lean_dec(v_head_705_);
lean_dec(v_head_679_);
v___x_715_ = lean_box(0);
return v___x_715_;
}
else
{
uint8_t v___x_716_; uint8_t v___x_717_; uint8_t v___x_718_; 
v___x_716_ = lean_unbox(v_head_706_);
v___x_717_ = lean_uint8_land(v___x_716_, v___x_692_);
v___x_718_ = lean_uint8_dec_eq(v___x_717_, v___x_684_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
lean_del_object(v___x_710_);
lean_dec(v_tail_708_);
lean_dec(v_head_707_);
lean_dec(v_head_706_);
lean_dec(v_head_705_);
lean_dec(v_head_679_);
v___x_719_ = lean_box(0);
return v___x_719_;
}
else
{
uint8_t v___x_720_; uint8_t v___x_721_; uint8_t v___x_722_; 
v___x_720_ = lean_unbox(v_head_707_);
v___x_721_ = lean_uint8_land(v___x_720_, v___x_692_);
v___x_722_ = lean_uint8_dec_eq(v___x_721_, v___x_684_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_del_object(v___x_710_);
lean_dec(v_tail_708_);
lean_dec(v_head_707_);
lean_dec(v_head_706_);
lean_dec(v_head_705_);
lean_dec(v_head_679_);
v___x_723_ = lean_box(0);
return v___x_723_;
}
else
{
uint8_t v___x_724_; uint8_t v___x_725_; uint8_t v_b_u2080_726_; uint8_t v___x_727_; uint8_t v___x_728_; uint8_t v_b_u2081_729_; uint8_t v___x_730_; uint8_t v_b_u2082_731_; uint8_t v___x_732_; uint8_t v_b_u2083_733_; uint32_t v___x_734_; uint32_t v___x_735_; uint32_t v___x_736_; uint32_t v___x_737_; uint32_t v___x_738_; uint32_t v___x_739_; uint32_t v___x_740_; uint32_t v___x_741_; uint32_t v___x_742_; uint32_t v___x_743_; uint32_t v___x_744_; uint32_t v___x_745_; uint32_t v_r_746_; uint32_t v___x_747_; uint8_t v___x_748_; 
v___x_724_ = 7;
v___x_725_ = lean_unbox(v_head_679_);
lean_dec(v_head_679_);
v_b_u2080_726_ = lean_uint8_land(v___x_725_, v___x_724_);
v___x_727_ = 63;
v___x_728_ = lean_unbox(v_head_705_);
lean_dec(v_head_705_);
v_b_u2081_729_ = lean_uint8_land(v___x_728_, v___x_727_);
v___x_730_ = lean_unbox(v_head_706_);
lean_dec(v_head_706_);
v_b_u2082_731_ = lean_uint8_land(v___x_730_, v___x_727_);
v___x_732_ = lean_unbox(v_head_707_);
lean_dec(v_head_707_);
v_b_u2083_733_ = lean_uint8_land(v___x_732_, v___x_727_);
v___x_734_ = lean_uint8_to_uint32(v_b_u2080_726_);
v___x_735_ = 18;
v___x_736_ = lean_uint32_shift_left(v___x_734_, v___x_735_);
v___x_737_ = lean_uint8_to_uint32(v_b_u2081_729_);
v___x_738_ = 12;
v___x_739_ = lean_uint32_shift_left(v___x_737_, v___x_738_);
v___x_740_ = lean_uint32_lor(v___x_736_, v___x_739_);
v___x_741_ = lean_uint8_to_uint32(v_b_u2082_731_);
v___x_742_ = 6;
v___x_743_ = lean_uint32_shift_left(v___x_741_, v___x_742_);
v___x_744_ = lean_uint32_lor(v___x_740_, v___x_743_);
v___x_745_ = lean_uint8_to_uint32(v_b_u2083_733_);
v_r_746_ = lean_uint32_lor(v___x_744_, v___x_745_);
v___x_747_ = 65536;
v___x_748_ = lean_uint32_dec_lt(v_r_746_, v___x_747_);
if (v___x_748_ == 0)
{
uint32_t v___x_749_; uint8_t v___x_750_; 
v___x_749_ = 1114111;
v___x_750_ = lean_uint32_dec_lt(v___x_749_, v_r_746_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_751_ = l_String_Internal_utf8DecodeList(v_tail_708_);
v___x_752_ = lean_box_uint32(v_r_746_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_751_);
lean_ctor_set(v___x_710_, 0, v___x_752_);
v___x_754_ = v___x_710_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_751_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
else
{
lean_object* v___x_756_; 
lean_del_object(v___x_710_);
lean_dec(v_tail_708_);
v___x_756_ = lean_box(0);
return v___x_756_;
}
}
else
{
lean_object* v___x_757_; 
lean_del_object(v___x_710_);
lean_dec(v_tail_708_);
v___x_757_ = lean_box(0);
return v___x_757_;
}
}
}
}
}
}
else
{
lean_object* v___x_759_; 
lean_dec(v_tail_704_);
lean_dec_ref_known(v_tail_703_, 2);
lean_dec_ref_known(v_tail_680_, 2);
lean_dec(v_head_679_);
v___x_759_ = lean_box(0);
return v___x_759_;
}
}
else
{
lean_object* v___x_760_; 
lean_dec(v_tail_703_);
lean_dec_ref_known(v_tail_680_, 2);
lean_dec(v_head_679_);
v___x_760_ = lean_box(0);
return v___x_760_;
}
}
else
{
lean_object* v___x_761_; 
lean_dec(v_tail_680_);
lean_dec(v_head_679_);
v___x_761_ = lean_box(0);
return v___x_761_;
}
}
}
else
{
if (lean_obj_tag(v_tail_680_) == 1)
{
lean_object* v_tail_762_; 
v_tail_762_ = lean_ctor_get(v_tail_680_, 1);
lean_inc(v_tail_762_);
if (lean_obj_tag(v_tail_762_) == 1)
{
lean_object* v_head_763_; lean_object* v_head_764_; lean_object* v_tail_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_808_; 
v_head_763_ = lean_ctor_get(v_tail_680_, 0);
lean_inc(v_head_763_);
lean_dec_ref_known(v_tail_680_, 2);
v_head_764_ = lean_ctor_get(v_tail_762_, 0);
v_tail_765_ = lean_ctor_get(v_tail_762_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v_tail_762_);
if (v_isSharedCheck_808_ == 0)
{
v___x_767_ = v_tail_762_;
v_isShared_768_ = v_isSharedCheck_808_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_tail_765_);
lean_inc(v_head_764_);
lean_dec(v_tail_762_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_808_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
uint8_t v___x_769_; uint8_t v___x_770_; uint8_t v___x_771_; 
v___x_769_ = lean_unbox(v_head_763_);
v___x_770_ = lean_uint8_land(v___x_769_, v___x_692_);
v___x_771_ = lean_uint8_dec_eq(v___x_770_, v___x_684_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_del_object(v___x_767_);
lean_dec(v_tail_765_);
lean_dec(v_head_764_);
lean_dec(v_head_763_);
lean_dec(v_head_679_);
v___x_772_ = lean_box(0);
return v___x_772_;
}
else
{
uint8_t v___x_773_; uint8_t v___x_774_; uint8_t v___x_775_; 
v___x_773_ = lean_unbox(v_head_764_);
v___x_774_ = lean_uint8_land(v___x_773_, v___x_692_);
v___x_775_ = lean_uint8_dec_eq(v___x_774_, v___x_684_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_del_object(v___x_767_);
lean_dec(v_tail_765_);
lean_dec(v_head_764_);
lean_dec(v_head_763_);
lean_dec(v_head_679_);
v___x_776_ = lean_box(0);
return v___x_776_;
}
else
{
uint8_t v___x_777_; uint8_t v___x_778_; uint8_t v_b_u2080_779_; uint8_t v___x_780_; uint8_t v___x_781_; uint8_t v_b_u2081_782_; uint8_t v___x_783_; uint8_t v_b_u2082_784_; uint32_t v___x_785_; uint32_t v___x_786_; uint32_t v___x_787_; uint32_t v___x_788_; uint32_t v___x_789_; uint32_t v___x_790_; uint32_t v___x_791_; uint32_t v___x_792_; uint32_t v_r_793_; uint32_t v___x_800_; uint8_t v___x_801_; 
v___x_777_ = 15;
v___x_778_ = lean_unbox(v_head_679_);
lean_dec(v_head_679_);
v_b_u2080_779_ = lean_uint8_land(v___x_778_, v___x_777_);
v___x_780_ = 63;
v___x_781_ = lean_unbox(v_head_763_);
lean_dec(v_head_763_);
v_b_u2081_782_ = lean_uint8_land(v___x_781_, v___x_780_);
v___x_783_ = lean_unbox(v_head_764_);
lean_dec(v_head_764_);
v_b_u2082_784_ = lean_uint8_land(v___x_783_, v___x_780_);
v___x_785_ = lean_uint8_to_uint32(v_b_u2080_779_);
v___x_786_ = 12;
v___x_787_ = lean_uint32_shift_left(v___x_785_, v___x_786_);
v___x_788_ = lean_uint8_to_uint32(v_b_u2081_782_);
v___x_789_ = 6;
v___x_790_ = lean_uint32_shift_left(v___x_788_, v___x_789_);
v___x_791_ = lean_uint32_lor(v___x_787_, v___x_790_);
v___x_792_ = lean_uint8_to_uint32(v_b_u2082_784_);
v_r_793_ = lean_uint32_lor(v___x_791_, v___x_792_);
v___x_800_ = 2048;
v___x_801_ = lean_uint32_dec_lt(v_r_793_, v___x_800_);
if (v___x_801_ == 0)
{
uint32_t v___x_802_; uint8_t v___x_803_; 
v___x_802_ = 55296;
v___x_803_ = lean_uint32_dec_le(v___x_802_, v_r_793_);
if (v___x_803_ == 0)
{
goto v___jp_794_;
}
else
{
uint32_t v___x_804_; uint8_t v___x_805_; 
v___x_804_ = 57343;
v___x_805_ = lean_uint32_dec_le(v_r_793_, v___x_804_);
if (v___x_805_ == 0)
{
goto v___jp_794_;
}
else
{
lean_object* v___x_806_; 
lean_del_object(v___x_767_);
lean_dec(v_tail_765_);
v___x_806_ = lean_box(0);
return v___x_806_;
}
}
}
else
{
lean_object* v___x_807_; 
lean_del_object(v___x_767_);
lean_dec(v_tail_765_);
v___x_807_ = lean_box(0);
return v___x_807_;
}
v___jp_794_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_795_ = l_String_Internal_utf8DecodeList(v_tail_765_);
v___x_796_ = lean_box_uint32(v_r_793_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_795_);
lean_ctor_set(v___x_767_, 0, v___x_796_);
v___x_798_ = v___x_767_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_795_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
}
else
{
lean_object* v___x_809_; 
lean_dec_ref_known(v_tail_680_, 2);
lean_dec(v_tail_762_);
lean_dec(v_head_679_);
v___x_809_ = lean_box(0);
return v___x_809_;
}
}
else
{
lean_object* v___x_810_; 
lean_dec(v_tail_680_);
lean_dec(v_head_679_);
v___x_810_ = lean_box(0);
return v___x_810_;
}
}
}
else
{
if (lean_obj_tag(v_tail_680_) == 1)
{
lean_object* v_head_811_; lean_object* v_tail_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_839_; 
v_head_811_ = lean_ctor_get(v_tail_680_, 0);
v_tail_812_ = lean_ctor_get(v_tail_680_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_tail_680_);
if (v_isSharedCheck_839_ == 0)
{
v___x_814_ = v_tail_680_;
v_isShared_815_ = v_isSharedCheck_839_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_tail_812_);
lean_inc(v_head_811_);
lean_dec(v_tail_680_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_839_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
uint8_t v___x_816_; uint8_t v___x_817_; uint8_t v___x_818_; 
v___x_816_ = lean_unbox(v_head_811_);
v___x_817_ = lean_uint8_land(v___x_816_, v___x_692_);
v___x_818_ = lean_uint8_dec_eq(v___x_817_, v___x_684_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; 
lean_del_object(v___x_814_);
lean_dec(v_tail_812_);
lean_dec(v_head_811_);
lean_dec(v_head_679_);
v___x_819_ = lean_box(0);
return v___x_819_;
}
else
{
uint8_t v___x_820_; uint8_t v___x_821_; uint8_t v_b_u2080_822_; uint8_t v___x_823_; uint8_t v___x_824_; uint8_t v_b_u2081_825_; uint32_t v___x_826_; uint32_t v___x_827_; uint32_t v___x_828_; uint32_t v___x_829_; uint32_t v_r_830_; uint32_t v___x_831_; uint8_t v___x_832_; 
v___x_820_ = 31;
v___x_821_ = lean_unbox(v_head_679_);
lean_dec(v_head_679_);
v_b_u2080_822_ = lean_uint8_land(v___x_821_, v___x_820_);
v___x_823_ = 63;
v___x_824_ = lean_unbox(v_head_811_);
lean_dec(v_head_811_);
v_b_u2081_825_ = lean_uint8_land(v___x_824_, v___x_823_);
v___x_826_ = lean_uint8_to_uint32(v_b_u2080_822_);
v___x_827_ = 6;
v___x_828_ = lean_uint32_shift_left(v___x_826_, v___x_827_);
v___x_829_ = lean_uint8_to_uint32(v_b_u2081_825_);
v_r_830_ = lean_uint32_lor(v___x_828_, v___x_829_);
v___x_831_ = 128;
v___x_832_ = lean_uint32_dec_lt(v_r_830_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_833_ = l_String_Internal_utf8DecodeList(v_tail_812_);
v___x_834_ = lean_box_uint32(v_r_830_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v___x_833_);
lean_ctor_set(v___x_814_, 0, v___x_834_);
v___x_836_ = v___x_814_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v___x_833_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
else
{
lean_object* v___x_838_; 
lean_del_object(v___x_814_);
lean_dec(v_tail_812_);
v___x_838_ = lean_box(0);
return v___x_838_;
}
}
}
}
else
{
lean_object* v___x_840_; 
lean_dec(v_tail_680_);
lean_dec(v_head_679_);
v___x_840_ = lean_box(0);
return v___x_840_;
}
}
}
else
{
uint8_t v___x_841_; uint32_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_841_ = lean_unbox(v_head_679_);
lean_dec(v_head_679_);
v___x_842_ = lean_uint8_to_uint32(v___x_841_);
v___x_843_ = l_String_Internal_utf8DecodeList(v_tail_680_);
v___x_844_ = lean_box_uint32(v___x_842_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_843_);
lean_ctor_set(v___x_682_, 0, v___x_844_);
v___x_846_ = v___x_682_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_843_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8At(lean_object* v_bytes_849_, lean_object* v_i_850_){
_start:
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = lean_byte_array_size(v_bytes_849_);
v___x_852_ = lean_nat_dec_lt(v_i_850_, v___x_851_);
if (v___x_852_ == 0)
{
return v___x_852_;
}
else
{
uint8_t v___x_853_; uint8_t v___x_854_; uint8_t v___x_855_; uint8_t v___x_856_; uint8_t v___x_857_; 
v___x_853_ = lean_byte_array_fget(v_bytes_849_, v_i_850_);
v___x_854_ = 128;
v___x_855_ = lean_uint8_land(v___x_853_, v___x_854_);
v___x_856_ = 0;
v___x_857_ = lean_uint8_dec_eq(v___x_855_, v___x_856_);
if (v___x_857_ == 0)
{
uint8_t v___x_858_; uint8_t v___x_859_; uint8_t v___x_860_; uint8_t v___x_861_; 
v___x_858_ = 224;
v___x_859_ = lean_uint8_land(v___x_853_, v___x_858_);
v___x_860_ = 192;
v___x_861_ = lean_uint8_dec_eq(v___x_859_, v___x_860_);
if (v___x_861_ == 0)
{
uint8_t v___x_862_; uint8_t v___x_863_; uint8_t v___x_864_; 
v___x_862_ = 240;
v___x_863_ = lean_uint8_land(v___x_853_, v___x_862_);
v___x_864_ = lean_uint8_dec_eq(v___x_863_, v___x_858_);
if (v___x_864_ == 0)
{
uint8_t v___x_865_; uint8_t v___x_866_; uint8_t v___x_867_; 
v___x_865_ = 248;
v___x_866_ = lean_uint8_land(v___x_853_, v___x_865_);
v___x_867_ = lean_uint8_dec_eq(v___x_866_, v___x_862_);
if (v___x_867_ == 0)
{
return v___x_867_;
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_868_ = lean_unsigned_to_nat(3u);
v___x_869_ = lean_nat_add(v_i_850_, v___x_868_);
v___x_870_ = lean_nat_dec_lt(v___x_869_, v___x_851_);
if (v___x_870_ == 0)
{
lean_dec(v___x_869_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; uint8_t v___x_874_; uint8_t v___x_875_; 
v___x_871_ = lean_unsigned_to_nat(1u);
v___x_872_ = lean_nat_add(v_i_850_, v___x_871_);
v___x_873_ = lean_byte_array_fget(v_bytes_849_, v___x_872_);
lean_dec(v___x_872_);
v___x_874_ = lean_uint8_land(v___x_873_, v___x_860_);
v___x_875_ = lean_uint8_dec_eq(v___x_874_, v___x_854_);
if (v___x_875_ == 0)
{
lean_dec(v___x_869_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; uint8_t v___x_879_; uint8_t v___x_880_; 
v___x_876_ = lean_unsigned_to_nat(2u);
v___x_877_ = lean_nat_add(v_i_850_, v___x_876_);
v___x_878_ = lean_byte_array_fget(v_bytes_849_, v___x_877_);
lean_dec(v___x_877_);
v___x_879_ = lean_uint8_land(v___x_878_, v___x_860_);
v___x_880_ = lean_uint8_dec_eq(v___x_879_, v___x_854_);
if (v___x_880_ == 0)
{
lean_dec(v___x_869_);
return v___x_864_;
}
else
{
uint8_t v___x_881_; uint8_t v___x_882_; uint8_t v___x_883_; 
v___x_881_ = lean_byte_array_fget(v_bytes_849_, v___x_869_);
lean_dec(v___x_869_);
v___x_882_ = lean_uint8_land(v___x_881_, v___x_860_);
v___x_883_ = lean_uint8_dec_eq(v___x_882_, v___x_854_);
if (v___x_883_ == 0)
{
return v___x_864_;
}
else
{
uint8_t v___x_884_; uint8_t v_b_u2080_885_; uint8_t v___x_886_; uint8_t v_b_u2081_887_; uint8_t v_b_u2082_888_; uint8_t v_b_u2083_889_; uint32_t v___x_890_; uint32_t v___x_891_; uint32_t v___x_892_; uint32_t v___x_893_; uint32_t v___x_894_; uint32_t v___x_895_; uint32_t v___x_896_; uint32_t v___x_897_; uint32_t v___x_898_; uint32_t v___x_899_; uint32_t v___x_900_; uint32_t v___x_901_; uint32_t v_r_902_; uint32_t v___x_903_; uint8_t v___x_904_; 
v___x_884_ = 7;
v_b_u2080_885_ = lean_uint8_land(v___x_853_, v___x_884_);
v___x_886_ = 63;
v_b_u2081_887_ = lean_uint8_land(v___x_873_, v___x_886_);
v_b_u2082_888_ = lean_uint8_land(v___x_878_, v___x_886_);
v_b_u2083_889_ = lean_uint8_land(v___x_881_, v___x_886_);
v___x_890_ = lean_uint8_to_uint32(v_b_u2080_885_);
v___x_891_ = 18;
v___x_892_ = lean_uint32_shift_left(v___x_890_, v___x_891_);
v___x_893_ = lean_uint8_to_uint32(v_b_u2081_887_);
v___x_894_ = 12;
v___x_895_ = lean_uint32_shift_left(v___x_893_, v___x_894_);
v___x_896_ = lean_uint32_lor(v___x_892_, v___x_895_);
v___x_897_ = lean_uint8_to_uint32(v_b_u2082_888_);
v___x_898_ = 6;
v___x_899_ = lean_uint32_shift_left(v___x_897_, v___x_898_);
v___x_900_ = lean_uint32_lor(v___x_896_, v___x_899_);
v___x_901_ = lean_uint8_to_uint32(v_b_u2083_889_);
v_r_902_ = lean_uint32_lor(v___x_900_, v___x_901_);
v___x_903_ = 65536;
v___x_904_ = lean_uint32_dec_le(v___x_903_, v_r_902_);
if (v___x_904_ == 0)
{
return v___x_864_;
}
else
{
uint32_t v___x_905_; uint8_t v___x_906_; 
v___x_905_ = 1114111;
v___x_906_ = lean_uint32_dec_le(v_r_902_, v___x_905_);
return v___x_906_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_907_ = lean_unsigned_to_nat(2u);
v___x_908_ = lean_nat_add(v_i_850_, v___x_907_);
v___x_909_ = lean_nat_dec_lt(v___x_908_, v___x_851_);
if (v___x_909_ == 0)
{
lean_dec(v___x_908_);
return v___x_909_;
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; uint8_t v___x_913_; uint8_t v___x_914_; 
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = lean_nat_add(v_i_850_, v___x_910_);
v___x_912_ = lean_byte_array_fget(v_bytes_849_, v___x_911_);
lean_dec(v___x_911_);
v___x_913_ = lean_uint8_land(v___x_912_, v___x_860_);
v___x_914_ = lean_uint8_dec_eq(v___x_913_, v___x_854_);
if (v___x_914_ == 0)
{
lean_dec(v___x_908_);
return v___x_914_;
}
else
{
uint8_t v___x_915_; uint8_t v___x_916_; uint8_t v___x_917_; 
v___x_915_ = lean_byte_array_fget(v_bytes_849_, v___x_908_);
lean_dec(v___x_908_);
v___x_916_ = lean_uint8_land(v___x_915_, v___x_860_);
v___x_917_ = lean_uint8_dec_eq(v___x_916_, v___x_854_);
if (v___x_917_ == 0)
{
return v___x_861_;
}
else
{
uint8_t v___x_918_; uint8_t v_b_u2080_919_; uint8_t v___x_920_; uint8_t v_b_u2081_921_; uint8_t v_b_u2082_922_; uint32_t v___x_923_; uint32_t v___x_924_; uint32_t v___x_925_; uint32_t v___x_926_; uint32_t v___x_927_; uint32_t v___x_928_; uint32_t v___x_929_; uint32_t v___x_930_; uint32_t v_r_931_; uint32_t v___x_932_; uint8_t v___x_933_; 
v___x_918_ = 15;
v_b_u2080_919_ = lean_uint8_land(v___x_853_, v___x_918_);
v___x_920_ = 63;
v_b_u2081_921_ = lean_uint8_land(v___x_912_, v___x_920_);
v_b_u2082_922_ = lean_uint8_land(v___x_915_, v___x_920_);
v___x_923_ = lean_uint8_to_uint32(v_b_u2080_919_);
v___x_924_ = 12;
v___x_925_ = lean_uint32_shift_left(v___x_923_, v___x_924_);
v___x_926_ = lean_uint8_to_uint32(v_b_u2081_921_);
v___x_927_ = 6;
v___x_928_ = lean_uint32_shift_left(v___x_926_, v___x_927_);
v___x_929_ = lean_uint32_lor(v___x_925_, v___x_928_);
v___x_930_ = lean_uint8_to_uint32(v_b_u2082_922_);
v_r_931_ = lean_uint32_lor(v___x_929_, v___x_930_);
v___x_932_ = 2048;
v___x_933_ = lean_uint32_dec_le(v___x_932_, v_r_931_);
if (v___x_933_ == 0)
{
return v___x_861_;
}
else
{
uint32_t v___x_934_; uint8_t v___x_935_; 
v___x_934_ = 55296;
v___x_935_ = lean_uint32_dec_lt(v_r_931_, v___x_934_);
if (v___x_935_ == 0)
{
uint32_t v___x_936_; uint8_t v___x_937_; 
v___x_936_ = 57343;
v___x_937_ = lean_uint32_dec_lt(v___x_936_, v_r_931_);
return v___x_937_;
}
else
{
return v___x_935_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_938_ = lean_unsigned_to_nat(1u);
v___x_939_ = lean_nat_add(v_i_850_, v___x_938_);
v___x_940_ = lean_nat_dec_lt(v___x_939_, v___x_851_);
if (v___x_940_ == 0)
{
lean_dec(v___x_939_);
return v___x_940_;
}
else
{
uint8_t v___x_941_; uint8_t v___x_942_; uint8_t v___x_943_; 
v___x_941_ = lean_byte_array_fget(v_bytes_849_, v___x_939_);
lean_dec(v___x_939_);
v___x_942_ = lean_uint8_land(v___x_941_, v___x_860_);
v___x_943_ = lean_uint8_dec_eq(v___x_942_, v___x_854_);
if (v___x_943_ == 0)
{
return v___x_943_;
}
else
{
uint8_t v___x_944_; uint8_t v_b_u2080_945_; uint8_t v___x_946_; uint8_t v_b_u2081_947_; uint32_t v___x_948_; uint32_t v___x_949_; uint32_t v___x_950_; uint32_t v___x_951_; uint32_t v_r_952_; uint32_t v___x_953_; uint8_t v___x_954_; 
v___x_944_ = 31;
v_b_u2080_945_ = lean_uint8_land(v___x_853_, v___x_944_);
v___x_946_ = 63;
v_b_u2081_947_ = lean_uint8_land(v___x_941_, v___x_946_);
v___x_948_ = lean_uint8_to_uint32(v_b_u2080_945_);
v___x_949_ = 6;
v___x_950_ = lean_uint32_shift_left(v___x_948_, v___x_949_);
v___x_951_ = lean_uint8_to_uint32(v_b_u2081_947_);
v_r_952_ = lean_uint32_lor(v___x_950_, v___x_951_);
v___x_953_ = 128;
v___x_954_ = lean_uint32_dec_le(v___x_953_, v_r_952_);
return v___x_954_;
}
}
}
}
else
{
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8At___boxed(lean_object* v_bytes_955_, lean_object* v_i_956_){
_start:
{
uint8_t v_res_957_; lean_object* v_r_958_; 
v_res_957_ = l_ByteArray_validateUTF8At(v_bytes_955_, v_i_956_);
lean_dec(v_i_956_);
lean_dec_ref(v_bytes_955_);
v_r_958_ = lean_box(v_res_957_);
return v_r_958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t v_x_959_, lean_object* v_h__1_960_, lean_object* v_h__2_961_, lean_object* v_h__3_962_, lean_object* v_h__4_963_, lean_object* v_h__5_964_){
_start:
{
switch(v_x_959_)
{
case 0:
{
lean_object* v___x_965_; 
lean_dec(v_h__5_964_);
lean_dec(v_h__4_963_);
lean_dec(v_h__3_962_);
lean_dec(v_h__2_961_);
v___x_965_ = lean_apply_1(v_h__1_960_, lean_box(0));
return v___x_965_;
}
case 1:
{
lean_object* v___x_966_; 
lean_dec(v_h__5_964_);
lean_dec(v_h__4_963_);
lean_dec(v_h__3_962_);
lean_dec(v_h__1_960_);
v___x_966_ = lean_apply_1(v_h__2_961_, lean_box(0));
return v___x_966_;
}
case 2:
{
lean_object* v___x_967_; 
lean_dec(v_h__5_964_);
lean_dec(v_h__4_963_);
lean_dec(v_h__2_961_);
lean_dec(v_h__1_960_);
v___x_967_ = lean_apply_1(v_h__3_962_, lean_box(0));
return v___x_967_;
}
case 3:
{
lean_object* v___x_968_; 
lean_dec(v_h__5_964_);
lean_dec(v_h__3_962_);
lean_dec(v_h__2_961_);
lean_dec(v_h__1_960_);
v___x_968_ = lean_apply_1(v_h__4_963_, lean_box(0));
return v___x_968_;
}
default: 
{
lean_object* v___x_969_; 
lean_dec(v_h__4_963_);
lean_dec(v_h__3_962_);
lean_dec(v_h__2_961_);
lean_dec(v_h__1_960_);
v___x_969_ = lean_apply_1(v_h__5_964_, lean_box(0));
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_970_, lean_object* v_h__1_971_, lean_object* v_h__2_972_, lean_object* v_h__3_973_, lean_object* v_h__4_974_, lean_object* v_h__5_975_){
_start:
{
uint8_t v_x_47__boxed_976_; lean_object* v_res_977_; 
v_x_47__boxed_976_ = lean_unbox(v_x_970_);
v_res_977_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(v_x_47__boxed_976_, v_h__1_971_, v_h__2_972_, v_h__3_973_, v_h__4_974_, v_h__5_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object* v_motive_978_, uint8_t v_x_979_, lean_object* v_h__1_980_, lean_object* v_h__2_981_, lean_object* v_h__3_982_, lean_object* v_h__4_983_, lean_object* v_h__5_984_){
_start:
{
switch(v_x_979_)
{
case 0:
{
lean_object* v___x_985_; 
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
v___x_985_ = lean_apply_1(v_h__1_980_, lean_box(0));
return v___x_985_;
}
case 1:
{
lean_object* v___x_986_; 
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__1_980_);
v___x_986_ = lean_apply_1(v_h__2_981_, lean_box(0));
return v___x_986_;
}
case 2:
{
lean_object* v___x_987_; 
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v___x_987_ = lean_apply_1(v_h__3_982_, lean_box(0));
return v___x_987_;
}
case 3:
{
lean_object* v___x_988_; 
lean_dec(v_h__5_984_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v___x_988_ = lean_apply_1(v_h__4_983_, lean_box(0));
return v___x_988_;
}
default: 
{
lean_object* v___x_989_; 
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v___x_989_ = lean_apply_1(v_h__5_984_, lean_box(0));
return v___x_989_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object* v_motive_990_, lean_object* v_x_991_, lean_object* v_h__1_992_, lean_object* v_h__2_993_, lean_object* v_h__3_994_, lean_object* v_h__4_995_, lean_object* v_h__5_996_){
_start:
{
uint8_t v_x_60__boxed_997_; lean_object* v_res_998_; 
v_x_60__boxed_997_ = lean_unbox(v_x_991_);
v_res_998_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(v_motive_990_, v_x_60__boxed_997_, v_h__1_992_, v_h__2_993_, v_h__3_994_, v_h__4_995_, v_h__5_996_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__10_splitter___redArg(lean_object* v_x_999_, lean_object* v_h__1_1000_, lean_object* v_h__2_1001_){
_start:
{
if (lean_obj_tag(v_x_999_) == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec(v_h__2_1001_);
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_apply_1(v_h__1_1000_, v___x_1002_);
return v___x_1003_;
}
else
{
lean_object* v_head_1004_; lean_object* v_tail_1005_; lean_object* v___x_1006_; 
lean_dec(v_h__1_1000_);
v_head_1004_ = lean_ctor_get(v_x_999_, 0);
lean_inc(v_head_1004_);
v_tail_1005_ = lean_ctor_get(v_x_999_, 1);
lean_inc(v_tail_1005_);
lean_dec_ref_known(v_x_999_, 2);
v___x_1006_ = lean_apply_2(v_h__2_1001_, v_head_1004_, v_tail_1005_);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__10_splitter(lean_object* v_motive_1007_, lean_object* v_x_1008_, lean_object* v_h__1_1009_, lean_object* v_h__2_1010_){
_start:
{
if (lean_obj_tag(v_x_1008_) == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec(v_h__2_1010_);
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_apply_1(v_h__1_1009_, v___x_1011_);
return v___x_1012_;
}
else
{
lean_object* v_head_1013_; lean_object* v_tail_1014_; lean_object* v___x_1015_; 
lean_dec(v_h__1_1009_);
v_head_1013_ = lean_ctor_get(v_x_1008_, 0);
lean_inc(v_head_1013_);
v_tail_1014_ = lean_ctor_get(v_x_1008_, 1);
lean_inc(v_tail_1014_);
lean_dec_ref_known(v_x_1008_, 2);
v___x_1015_ = lean_apply_2(v_h__2_1010_, v_head_1013_, v_tail_1014_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__1_splitter___redArg(lean_object* v_x_1016_, lean_object* v_h__1_1017_, lean_object* v_h__2_1018_){
_start:
{
if (lean_obj_tag(v_x_1016_) == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec(v_h__1_1017_);
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_apply_1(v_h__2_1018_, v___x_1019_);
return v___x_1020_;
}
else
{
lean_object* v_val_1021_; lean_object* v___x_1022_; 
lean_dec(v_h__2_1018_);
v_val_1021_ = lean_ctor_get(v_x_1016_, 0);
lean_inc(v_val_1021_);
lean_dec_ref_known(v_x_1016_, 1);
v___x_1022_ = lean_apply_1(v_h__1_1017_, v_val_1021_);
return v___x_1022_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__1_splitter(lean_object* v_motive_1023_, lean_object* v_x_1024_, lean_object* v_h__1_1025_, lean_object* v_h__2_1026_){
_start:
{
if (lean_obj_tag(v_x_1024_) == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec(v_h__1_1025_);
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_apply_1(v_h__2_1026_, v___x_1027_);
return v___x_1028_;
}
else
{
lean_object* v_val_1029_; lean_object* v___x_1030_; 
lean_dec(v_h__2_1026_);
v_val_1029_ = lean_ctor_get(v_x_1024_, 0);
lean_inc(v_val_1029_);
lean_dec_ref_known(v_x_1024_, 1);
v___x_1030_ = lean_apply_1(v_h__1_1025_, v_val_1029_);
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__3_splitter___redArg(lean_object* v_ws_1031_, lean_object* v_h__1_1032_, lean_object* v_h__2_1033_){
_start:
{
if (lean_obj_tag(v_ws_1031_) == 1)
{
lean_object* v_head_1034_; lean_object* v_tail_1035_; lean_object* v___x_1036_; 
lean_dec(v_h__2_1033_);
v_head_1034_ = lean_ctor_get(v_ws_1031_, 0);
lean_inc(v_head_1034_);
v_tail_1035_ = lean_ctor_get(v_ws_1031_, 1);
lean_inc(v_tail_1035_);
lean_dec_ref_known(v_ws_1031_, 2);
v___x_1036_ = lean_apply_2(v_h__1_1032_, v_head_1034_, v_tail_1035_);
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; 
lean_dec(v_h__1_1032_);
v___x_1037_ = lean_apply_2(v_h__2_1033_, v_ws_1031_, lean_box(0));
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__3_splitter(lean_object* v_motive_1038_, lean_object* v_ws_1039_, lean_object* v_h__1_1040_, lean_object* v_h__2_1041_){
_start:
{
if (lean_obj_tag(v_ws_1039_) == 1)
{
lean_object* v_head_1042_; lean_object* v_tail_1043_; lean_object* v___x_1044_; 
lean_dec(v_h__2_1041_);
v_head_1042_ = lean_ctor_get(v_ws_1039_, 0);
lean_inc(v_head_1042_);
v_tail_1043_ = lean_ctor_get(v_ws_1039_, 1);
lean_inc(v_tail_1043_);
lean_dec_ref_known(v_ws_1039_, 2);
v___x_1044_ = lean_apply_2(v_h__1_1040_, v_head_1042_, v_tail_1043_);
return v___x_1044_;
}
else
{
lean_object* v___x_1045_; 
lean_dec(v_h__1_1040_);
v___x_1045_ = lean_apply_2(v_h__2_1041_, v_ws_1039_, lean_box(0));
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__6_splitter___redArg(lean_object* v_ws_1046_, lean_object* v_h__1_1047_, lean_object* v_h__2_1048_){
_start:
{
if (lean_obj_tag(v_ws_1046_) == 1)
{
lean_object* v_tail_1049_; 
v_tail_1049_ = lean_ctor_get(v_ws_1046_, 1);
if (lean_obj_tag(v_tail_1049_) == 1)
{
lean_object* v_head_1050_; lean_object* v_head_1051_; lean_object* v_tail_1052_; lean_object* v___x_1053_; 
lean_inc_ref(v_tail_1049_);
lean_dec(v_h__2_1048_);
v_head_1050_ = lean_ctor_get(v_ws_1046_, 0);
lean_inc(v_head_1050_);
lean_dec_ref_known(v_ws_1046_, 2);
v_head_1051_ = lean_ctor_get(v_tail_1049_, 0);
lean_inc(v_head_1051_);
v_tail_1052_ = lean_ctor_get(v_tail_1049_, 1);
lean_inc(v_tail_1052_);
lean_dec_ref_known(v_tail_1049_, 2);
v___x_1053_ = lean_apply_3(v_h__1_1047_, v_head_1050_, v_head_1051_, v_tail_1052_);
return v___x_1053_;
}
else
{
lean_object* v___x_1054_; 
lean_dec(v_h__1_1047_);
v___x_1054_ = lean_apply_2(v_h__2_1048_, v_ws_1046_, lean_box(0));
return v___x_1054_;
}
}
else
{
lean_object* v___x_1055_; 
lean_dec(v_h__1_1047_);
v___x_1055_ = lean_apply_2(v_h__2_1048_, v_ws_1046_, lean_box(0));
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__6_splitter(lean_object* v_motive_1056_, lean_object* v_ws_1057_, lean_object* v_h__1_1058_, lean_object* v_h__2_1059_){
_start:
{
if (lean_obj_tag(v_ws_1057_) == 1)
{
lean_object* v_tail_1060_; 
v_tail_1060_ = lean_ctor_get(v_ws_1057_, 1);
if (lean_obj_tag(v_tail_1060_) == 1)
{
lean_object* v_head_1061_; lean_object* v_head_1062_; lean_object* v_tail_1063_; lean_object* v___x_1064_; 
lean_inc_ref(v_tail_1060_);
lean_dec(v_h__2_1059_);
v_head_1061_ = lean_ctor_get(v_ws_1057_, 0);
lean_inc(v_head_1061_);
lean_dec_ref_known(v_ws_1057_, 2);
v_head_1062_ = lean_ctor_get(v_tail_1060_, 0);
lean_inc(v_head_1062_);
v_tail_1063_ = lean_ctor_get(v_tail_1060_, 1);
lean_inc(v_tail_1063_);
lean_dec_ref_known(v_tail_1060_, 2);
v___x_1064_ = lean_apply_3(v_h__1_1058_, v_head_1061_, v_head_1062_, v_tail_1063_);
return v___x_1064_;
}
else
{
lean_object* v___x_1065_; 
lean_dec(v_h__1_1058_);
v___x_1065_ = lean_apply_2(v_h__2_1059_, v_ws_1057_, lean_box(0));
return v___x_1065_;
}
}
else
{
lean_object* v___x_1066_; 
lean_dec(v_h__1_1058_);
v___x_1066_ = lean_apply_2(v_h__2_1059_, v_ws_1057_, lean_box(0));
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__8_splitter___redArg(lean_object* v_ws_1067_, lean_object* v_h__1_1068_, lean_object* v_h__2_1069_){
_start:
{
if (lean_obj_tag(v_ws_1067_) == 1)
{
lean_object* v_tail_1070_; 
v_tail_1070_ = lean_ctor_get(v_ws_1067_, 1);
if (lean_obj_tag(v_tail_1070_) == 1)
{
lean_object* v_tail_1071_; 
v_tail_1071_ = lean_ctor_get(v_tail_1070_, 1);
if (lean_obj_tag(v_tail_1071_) == 1)
{
lean_object* v_head_1072_; lean_object* v_head_1073_; lean_object* v_head_1074_; lean_object* v_tail_1075_; lean_object* v___x_1076_; 
lean_inc_ref(v_tail_1071_);
lean_inc_ref(v_tail_1070_);
lean_dec(v_h__2_1069_);
v_head_1072_ = lean_ctor_get(v_ws_1067_, 0);
lean_inc(v_head_1072_);
lean_dec_ref_known(v_ws_1067_, 2);
v_head_1073_ = lean_ctor_get(v_tail_1070_, 0);
lean_inc(v_head_1073_);
lean_dec_ref_known(v_tail_1070_, 2);
v_head_1074_ = lean_ctor_get(v_tail_1071_, 0);
lean_inc(v_head_1074_);
v_tail_1075_ = lean_ctor_get(v_tail_1071_, 1);
lean_inc(v_tail_1075_);
lean_dec_ref_known(v_tail_1071_, 2);
v___x_1076_ = lean_apply_4(v_h__1_1068_, v_head_1072_, v_head_1073_, v_head_1074_, v_tail_1075_);
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; 
lean_dec(v_h__1_1068_);
v___x_1077_ = lean_apply_2(v_h__2_1069_, v_ws_1067_, lean_box(0));
return v___x_1077_;
}
}
else
{
lean_object* v___x_1078_; 
lean_dec(v_h__1_1068_);
v___x_1078_ = lean_apply_2(v_h__2_1069_, v_ws_1067_, lean_box(0));
return v___x_1078_;
}
}
else
{
lean_object* v___x_1079_; 
lean_dec(v_h__1_1068_);
v___x_1079_ = lean_apply_2(v_h__2_1069_, v_ws_1067_, lean_box(0));
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__String_Internal_utf8DecodeList_match__8_splitter(lean_object* v_motive_1080_, lean_object* v_ws_1081_, lean_object* v_h__1_1082_, lean_object* v_h__2_1083_){
_start:
{
if (lean_obj_tag(v_ws_1081_) == 1)
{
lean_object* v_tail_1084_; 
v_tail_1084_ = lean_ctor_get(v_ws_1081_, 1);
if (lean_obj_tag(v_tail_1084_) == 1)
{
lean_object* v_tail_1085_; 
v_tail_1085_ = lean_ctor_get(v_tail_1084_, 1);
if (lean_obj_tag(v_tail_1085_) == 1)
{
lean_object* v_head_1086_; lean_object* v_head_1087_; lean_object* v_head_1088_; lean_object* v_tail_1089_; lean_object* v___x_1090_; 
lean_inc_ref(v_tail_1085_);
lean_inc_ref(v_tail_1084_);
lean_dec(v_h__2_1083_);
v_head_1086_ = lean_ctor_get(v_ws_1081_, 0);
lean_inc(v_head_1086_);
lean_dec_ref_known(v_ws_1081_, 2);
v_head_1087_ = lean_ctor_get(v_tail_1084_, 0);
lean_inc(v_head_1087_);
lean_dec_ref_known(v_tail_1084_, 2);
v_head_1088_ = lean_ctor_get(v_tail_1085_, 0);
lean_inc(v_head_1088_);
v_tail_1089_ = lean_ctor_get(v_tail_1085_, 1);
lean_inc(v_tail_1089_);
lean_dec_ref_known(v_tail_1085_, 2);
v___x_1090_ = lean_apply_4(v_h__1_1082_, v_head_1086_, v_head_1087_, v_head_1088_, v_tail_1089_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; 
lean_dec(v_h__1_1082_);
v___x_1091_ = lean_apply_2(v_h__2_1083_, v_ws_1081_, lean_box(0));
return v___x_1091_;
}
}
else
{
lean_object* v___x_1092_; 
lean_dec(v_h__1_1082_);
v___x_1092_ = lean_apply_2(v_h__2_1083_, v_ws_1081_, lean_box(0));
return v___x_1092_;
}
}
else
{
lean_object* v___x_1093_; 
lean_dec(v_h__1_1082_);
v___x_1093_ = lean_apply_2(v_h__2_1083_, v_ws_1081_, lean_box(0));
return v___x_1093_;
}
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar___redArg(lean_object* v_bytes_1094_, lean_object* v_i_1095_){
_start:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; uint8_t v___x_1098_; uint8_t v___x_1099_; uint8_t v___x_1100_; uint8_t v___x_1101_; uint8_t v___x_1102_; 
v___x_1096_ = lean_byte_array_size(v_bytes_1094_);
v___x_1097_ = lean_nat_dec_lt(v_i_1095_, v___x_1096_);
v___x_1098_ = lean_byte_array_fget(v_bytes_1094_, v_i_1095_);
v___x_1099_ = 128;
v___x_1100_ = lean_uint8_land(v___x_1098_, v___x_1099_);
v___x_1101_ = 0;
v___x_1102_ = lean_uint8_dec_eq(v___x_1100_, v___x_1101_);
if (v___x_1102_ == 0)
{
uint8_t v___x_1103_; uint8_t v___x_1104_; uint8_t v___x_1105_; uint8_t v___x_1106_; 
v___x_1103_ = 224;
v___x_1104_ = lean_uint8_land(v___x_1098_, v___x_1103_);
v___x_1105_ = 192;
v___x_1106_ = lean_uint8_dec_eq(v___x_1104_, v___x_1105_);
if (v___x_1106_ == 0)
{
uint8_t v___x_1107_; uint8_t v___x_1108_; uint8_t v___x_1109_; 
v___x_1107_ = 240;
v___x_1108_ = lean_uint8_land(v___x_1098_, v___x_1107_);
v___x_1109_ = lean_uint8_dec_eq(v___x_1108_, v___x_1103_);
if (v___x_1109_ == 0)
{
uint8_t v___x_1110_; uint8_t v___x_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; uint8_t v___x_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; uint8_t v___x_1124_; uint8_t v___x_1125_; uint8_t v___x_1126_; uint8_t v___x_1127_; uint8_t v___x_1128_; uint8_t v___x_1129_; uint8_t v_b_u2080_1130_; uint8_t v___x_1131_; uint8_t v_b_u2081_1132_; uint8_t v_b_u2082_1133_; uint8_t v_b_u2083_1134_; uint32_t v___x_1135_; uint32_t v___x_1136_; uint32_t v___x_1137_; uint32_t v___x_1138_; uint32_t v___x_1139_; uint32_t v___x_1140_; uint32_t v___x_1141_; uint32_t v___x_1142_; uint32_t v___x_1143_; uint32_t v___x_1144_; uint32_t v___x_1145_; uint32_t v___x_1146_; uint32_t v_r_1147_; uint32_t v___x_1148_; uint8_t v___x_1149_; uint32_t v___x_1150_; uint8_t v___x_1151_; 
v___x_1110_ = 248;
v___x_1111_ = lean_uint8_land(v___x_1098_, v___x_1110_);
v___x_1112_ = lean_uint8_dec_eq(v___x_1111_, v___x_1107_);
v___x_1113_ = lean_unsigned_to_nat(3u);
v___x_1114_ = lean_nat_add(v_i_1095_, v___x_1113_);
v___x_1115_ = lean_nat_dec_lt(v___x_1114_, v___x_1096_);
v___x_1116_ = lean_unsigned_to_nat(1u);
v___x_1117_ = lean_nat_add(v_i_1095_, v___x_1116_);
v___x_1118_ = lean_byte_array_fget(v_bytes_1094_, v___x_1117_);
lean_dec(v___x_1117_);
v___x_1119_ = lean_uint8_land(v___x_1118_, v___x_1105_);
v___x_1120_ = lean_uint8_dec_eq(v___x_1119_, v___x_1099_);
v___x_1121_ = lean_unsigned_to_nat(2u);
v___x_1122_ = lean_nat_add(v_i_1095_, v___x_1121_);
v___x_1123_ = lean_byte_array_fget(v_bytes_1094_, v___x_1122_);
lean_dec(v___x_1122_);
v___x_1124_ = lean_uint8_land(v___x_1123_, v___x_1105_);
v___x_1125_ = lean_uint8_dec_eq(v___x_1124_, v___x_1099_);
v___x_1126_ = lean_byte_array_fget(v_bytes_1094_, v___x_1114_);
lean_dec(v___x_1114_);
v___x_1127_ = lean_uint8_land(v___x_1126_, v___x_1105_);
v___x_1128_ = lean_uint8_dec_eq(v___x_1127_, v___x_1099_);
v___x_1129_ = 7;
v_b_u2080_1130_ = lean_uint8_land(v___x_1098_, v___x_1129_);
v___x_1131_ = 63;
v_b_u2081_1132_ = lean_uint8_land(v___x_1118_, v___x_1131_);
v_b_u2082_1133_ = lean_uint8_land(v___x_1123_, v___x_1131_);
v_b_u2083_1134_ = lean_uint8_land(v___x_1126_, v___x_1131_);
v___x_1135_ = lean_uint8_to_uint32(v_b_u2080_1130_);
v___x_1136_ = 18;
v___x_1137_ = lean_uint32_shift_left(v___x_1135_, v___x_1136_);
v___x_1138_ = lean_uint8_to_uint32(v_b_u2081_1132_);
v___x_1139_ = 12;
v___x_1140_ = lean_uint32_shift_left(v___x_1138_, v___x_1139_);
v___x_1141_ = lean_uint32_lor(v___x_1137_, v___x_1140_);
v___x_1142_ = lean_uint8_to_uint32(v_b_u2082_1133_);
v___x_1143_ = 6;
v___x_1144_ = lean_uint32_shift_left(v___x_1142_, v___x_1143_);
v___x_1145_ = lean_uint32_lor(v___x_1141_, v___x_1144_);
v___x_1146_ = lean_uint8_to_uint32(v_b_u2083_1134_);
v_r_1147_ = lean_uint32_lor(v___x_1145_, v___x_1146_);
v___x_1148_ = 65536;
v___x_1149_ = lean_uint32_dec_lt(v_r_1147_, v___x_1148_);
v___x_1150_ = 1114111;
v___x_1151_ = lean_uint32_dec_lt(v___x_1150_, v_r_1147_);
return v_r_1147_;
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; uint8_t v___x_1158_; uint8_t v___x_1159_; uint8_t v___x_1160_; uint8_t v___x_1161_; uint8_t v___x_1162_; uint8_t v___x_1163_; uint8_t v_b_u2080_1164_; uint8_t v___x_1165_; uint8_t v_b_u2081_1166_; uint8_t v_b_u2082_1167_; uint32_t v___x_1168_; uint32_t v___x_1169_; uint32_t v___x_1170_; uint32_t v___x_1171_; uint32_t v___x_1172_; uint32_t v___x_1173_; uint32_t v___x_1174_; uint32_t v___x_1175_; uint32_t v_r_1176_; uint32_t v___x_1177_; uint8_t v___x_1178_; uint32_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1152_ = lean_unsigned_to_nat(2u);
v___x_1153_ = lean_nat_add(v_i_1095_, v___x_1152_);
v___x_1154_ = lean_nat_dec_lt(v___x_1153_, v___x_1096_);
v___x_1155_ = lean_unsigned_to_nat(1u);
v___x_1156_ = lean_nat_add(v_i_1095_, v___x_1155_);
v___x_1157_ = lean_byte_array_fget(v_bytes_1094_, v___x_1156_);
lean_dec(v___x_1156_);
v___x_1158_ = lean_uint8_land(v___x_1157_, v___x_1105_);
v___x_1159_ = lean_uint8_dec_eq(v___x_1158_, v___x_1099_);
v___x_1160_ = lean_byte_array_fget(v_bytes_1094_, v___x_1153_);
lean_dec(v___x_1153_);
v___x_1161_ = lean_uint8_land(v___x_1160_, v___x_1105_);
v___x_1162_ = lean_uint8_dec_eq(v___x_1161_, v___x_1099_);
v___x_1163_ = 15;
v_b_u2080_1164_ = lean_uint8_land(v___x_1098_, v___x_1163_);
v___x_1165_ = 63;
v_b_u2081_1166_ = lean_uint8_land(v___x_1157_, v___x_1165_);
v_b_u2082_1167_ = lean_uint8_land(v___x_1160_, v___x_1165_);
v___x_1168_ = lean_uint8_to_uint32(v_b_u2080_1164_);
v___x_1169_ = 12;
v___x_1170_ = lean_uint32_shift_left(v___x_1168_, v___x_1169_);
v___x_1171_ = lean_uint8_to_uint32(v_b_u2081_1166_);
v___x_1172_ = 6;
v___x_1173_ = lean_uint32_shift_left(v___x_1171_, v___x_1172_);
v___x_1174_ = lean_uint32_lor(v___x_1170_, v___x_1173_);
v___x_1175_ = lean_uint8_to_uint32(v_b_u2082_1167_);
v_r_1176_ = lean_uint32_lor(v___x_1174_, v___x_1175_);
v___x_1177_ = 2048;
v___x_1178_ = lean_uint32_dec_lt(v_r_1176_, v___x_1177_);
v___x_1179_ = 55296;
v___x_1180_ = lean_uint32_dec_le(v___x_1179_, v_r_1176_);
if (v___x_1180_ == 0)
{
return v_r_1176_;
}
else
{
uint32_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = 57343;
v___x_1182_ = lean_uint32_dec_le(v_r_1176_, v___x_1181_);
return v_r_1176_;
}
}
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; uint8_t v___x_1186_; uint8_t v___x_1187_; uint8_t v___x_1188_; uint8_t v___x_1189_; uint8_t v_b_u2080_1190_; uint8_t v___x_1191_; uint8_t v_b_u2081_1192_; uint32_t v___x_1193_; uint32_t v___x_1194_; uint32_t v___x_1195_; uint32_t v___x_1196_; uint32_t v_r_1197_; uint32_t v___x_1198_; uint8_t v___x_1199_; 
v___x_1183_ = lean_unsigned_to_nat(1u);
v___x_1184_ = lean_nat_add(v_i_1095_, v___x_1183_);
v___x_1185_ = lean_nat_dec_lt(v___x_1184_, v___x_1096_);
v___x_1186_ = lean_byte_array_fget(v_bytes_1094_, v___x_1184_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_uint8_land(v___x_1186_, v___x_1105_);
v___x_1188_ = lean_uint8_dec_eq(v___x_1187_, v___x_1099_);
v___x_1189_ = 31;
v_b_u2080_1190_ = lean_uint8_land(v___x_1098_, v___x_1189_);
v___x_1191_ = 63;
v_b_u2081_1192_ = lean_uint8_land(v___x_1186_, v___x_1191_);
v___x_1193_ = lean_uint8_to_uint32(v_b_u2080_1190_);
v___x_1194_ = 6;
v___x_1195_ = lean_uint32_shift_left(v___x_1193_, v___x_1194_);
v___x_1196_ = lean_uint8_to_uint32(v_b_u2081_1192_);
v_r_1197_ = lean_uint32_lor(v___x_1195_, v___x_1196_);
v___x_1198_ = 128;
v___x_1199_ = lean_uint32_dec_lt(v_r_1197_, v___x_1198_);
return v_r_1197_;
}
}
else
{
uint32_t v___x_1200_; 
v___x_1200_ = lean_uint8_to_uint32(v___x_1098_);
return v___x_1200_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___redArg___boxed(lean_object* v_bytes_1201_, lean_object* v_i_1202_){
_start:
{
uint32_t v_res_1203_; lean_object* v_r_1204_; 
v_res_1203_ = l_ByteArray_utf8DecodeChar___redArg(v_bytes_1201_, v_i_1202_);
lean_dec(v_i_1202_);
lean_dec_ref(v_bytes_1201_);
v_r_1204_ = lean_box_uint32(v_res_1203_);
return v_r_1204_;
}
}
LEAN_EXPORT uint32_t l_ByteArray_utf8DecodeChar(lean_object* v_bytes_1205_, lean_object* v_i_1206_, lean_object* v_h_1207_){
_start:
{
lean_object* v___x_1208_; uint8_t v___x_1209_; uint8_t v___x_1210_; uint8_t v___x_1211_; uint8_t v___x_1212_; uint8_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1208_ = lean_byte_array_size(v_bytes_1205_);
v___x_1209_ = lean_nat_dec_lt(v_i_1206_, v___x_1208_);
v___x_1210_ = lean_byte_array_fget(v_bytes_1205_, v_i_1206_);
v___x_1211_ = 128;
v___x_1212_ = lean_uint8_land(v___x_1210_, v___x_1211_);
v___x_1213_ = 0;
v___x_1214_ = lean_uint8_dec_eq(v___x_1212_, v___x_1213_);
if (v___x_1214_ == 0)
{
uint8_t v___x_1215_; uint8_t v___x_1216_; uint8_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1215_ = 224;
v___x_1216_ = lean_uint8_land(v___x_1210_, v___x_1215_);
v___x_1217_ = 192;
v___x_1218_ = lean_uint8_dec_eq(v___x_1216_, v___x_1217_);
if (v___x_1218_ == 0)
{
uint8_t v___x_1219_; uint8_t v___x_1220_; uint8_t v___x_1221_; 
v___x_1219_ = 240;
v___x_1220_ = lean_uint8_land(v___x_1210_, v___x_1219_);
v___x_1221_ = lean_uint8_dec_eq(v___x_1220_, v___x_1215_);
if (v___x_1221_ == 0)
{
uint8_t v___x_1222_; uint8_t v___x_1223_; uint8_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; uint8_t v___x_1231_; uint8_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; uint8_t v___x_1236_; uint8_t v___x_1237_; uint8_t v___x_1238_; uint8_t v___x_1239_; uint8_t v___x_1240_; uint8_t v___x_1241_; uint8_t v_b_u2080_1242_; uint8_t v___x_1243_; uint8_t v_b_u2081_1244_; uint8_t v_b_u2082_1245_; uint8_t v_b_u2083_1246_; uint32_t v___x_1247_; uint32_t v___x_1248_; uint32_t v___x_1249_; uint32_t v___x_1250_; uint32_t v___x_1251_; uint32_t v___x_1252_; uint32_t v___x_1253_; uint32_t v___x_1254_; uint32_t v___x_1255_; uint32_t v___x_1256_; uint32_t v___x_1257_; uint32_t v___x_1258_; uint32_t v_r_1259_; uint32_t v___x_1260_; uint8_t v___x_1261_; uint32_t v___x_1262_; uint8_t v___x_1263_; 
v___x_1222_ = 248;
v___x_1223_ = lean_uint8_land(v___x_1210_, v___x_1222_);
v___x_1224_ = lean_uint8_dec_eq(v___x_1223_, v___x_1219_);
v___x_1225_ = lean_unsigned_to_nat(3u);
v___x_1226_ = lean_nat_add(v_i_1206_, v___x_1225_);
v___x_1227_ = lean_nat_dec_lt(v___x_1226_, v___x_1208_);
v___x_1228_ = lean_unsigned_to_nat(1u);
v___x_1229_ = lean_nat_add(v_i_1206_, v___x_1228_);
v___x_1230_ = lean_byte_array_fget(v_bytes_1205_, v___x_1229_);
lean_dec(v___x_1229_);
v___x_1231_ = lean_uint8_land(v___x_1230_, v___x_1217_);
v___x_1232_ = lean_uint8_dec_eq(v___x_1231_, v___x_1211_);
v___x_1233_ = lean_unsigned_to_nat(2u);
v___x_1234_ = lean_nat_add(v_i_1206_, v___x_1233_);
v___x_1235_ = lean_byte_array_fget(v_bytes_1205_, v___x_1234_);
lean_dec(v___x_1234_);
v___x_1236_ = lean_uint8_land(v___x_1235_, v___x_1217_);
v___x_1237_ = lean_uint8_dec_eq(v___x_1236_, v___x_1211_);
v___x_1238_ = lean_byte_array_fget(v_bytes_1205_, v___x_1226_);
lean_dec(v___x_1226_);
v___x_1239_ = lean_uint8_land(v___x_1238_, v___x_1217_);
v___x_1240_ = lean_uint8_dec_eq(v___x_1239_, v___x_1211_);
v___x_1241_ = 7;
v_b_u2080_1242_ = lean_uint8_land(v___x_1210_, v___x_1241_);
v___x_1243_ = 63;
v_b_u2081_1244_ = lean_uint8_land(v___x_1230_, v___x_1243_);
v_b_u2082_1245_ = lean_uint8_land(v___x_1235_, v___x_1243_);
v_b_u2083_1246_ = lean_uint8_land(v___x_1238_, v___x_1243_);
v___x_1247_ = lean_uint8_to_uint32(v_b_u2080_1242_);
v___x_1248_ = 18;
v___x_1249_ = lean_uint32_shift_left(v___x_1247_, v___x_1248_);
v___x_1250_ = lean_uint8_to_uint32(v_b_u2081_1244_);
v___x_1251_ = 12;
v___x_1252_ = lean_uint32_shift_left(v___x_1250_, v___x_1251_);
v___x_1253_ = lean_uint32_lor(v___x_1249_, v___x_1252_);
v___x_1254_ = lean_uint8_to_uint32(v_b_u2082_1245_);
v___x_1255_ = 6;
v___x_1256_ = lean_uint32_shift_left(v___x_1254_, v___x_1255_);
v___x_1257_ = lean_uint32_lor(v___x_1253_, v___x_1256_);
v___x_1258_ = lean_uint8_to_uint32(v_b_u2083_1246_);
v_r_1259_ = lean_uint32_lor(v___x_1257_, v___x_1258_);
v___x_1260_ = 65536;
v___x_1261_ = lean_uint32_dec_lt(v_r_1259_, v___x_1260_);
v___x_1262_ = 1114111;
v___x_1263_ = lean_uint32_dec_lt(v___x_1262_, v_r_1259_);
return v_r_1259_;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; uint8_t v___x_1270_; uint8_t v___x_1271_; uint8_t v___x_1272_; uint8_t v___x_1273_; uint8_t v___x_1274_; uint8_t v___x_1275_; uint8_t v_b_u2080_1276_; uint8_t v___x_1277_; uint8_t v_b_u2081_1278_; uint8_t v_b_u2082_1279_; uint32_t v___x_1280_; uint32_t v___x_1281_; uint32_t v___x_1282_; uint32_t v___x_1283_; uint32_t v___x_1284_; uint32_t v___x_1285_; uint32_t v___x_1286_; uint32_t v___x_1287_; uint32_t v_r_1288_; uint32_t v___x_1289_; uint8_t v___x_1290_; uint32_t v___x_1291_; uint8_t v___x_1292_; 
v___x_1264_ = lean_unsigned_to_nat(2u);
v___x_1265_ = lean_nat_add(v_i_1206_, v___x_1264_);
v___x_1266_ = lean_nat_dec_lt(v___x_1265_, v___x_1208_);
v___x_1267_ = lean_unsigned_to_nat(1u);
v___x_1268_ = lean_nat_add(v_i_1206_, v___x_1267_);
v___x_1269_ = lean_byte_array_fget(v_bytes_1205_, v___x_1268_);
lean_dec(v___x_1268_);
v___x_1270_ = lean_uint8_land(v___x_1269_, v___x_1217_);
v___x_1271_ = lean_uint8_dec_eq(v___x_1270_, v___x_1211_);
v___x_1272_ = lean_byte_array_fget(v_bytes_1205_, v___x_1265_);
lean_dec(v___x_1265_);
v___x_1273_ = lean_uint8_land(v___x_1272_, v___x_1217_);
v___x_1274_ = lean_uint8_dec_eq(v___x_1273_, v___x_1211_);
v___x_1275_ = 15;
v_b_u2080_1276_ = lean_uint8_land(v___x_1210_, v___x_1275_);
v___x_1277_ = 63;
v_b_u2081_1278_ = lean_uint8_land(v___x_1269_, v___x_1277_);
v_b_u2082_1279_ = lean_uint8_land(v___x_1272_, v___x_1277_);
v___x_1280_ = lean_uint8_to_uint32(v_b_u2080_1276_);
v___x_1281_ = 12;
v___x_1282_ = lean_uint32_shift_left(v___x_1280_, v___x_1281_);
v___x_1283_ = lean_uint8_to_uint32(v_b_u2081_1278_);
v___x_1284_ = 6;
v___x_1285_ = lean_uint32_shift_left(v___x_1283_, v___x_1284_);
v___x_1286_ = lean_uint32_lor(v___x_1282_, v___x_1285_);
v___x_1287_ = lean_uint8_to_uint32(v_b_u2082_1279_);
v_r_1288_ = lean_uint32_lor(v___x_1286_, v___x_1287_);
v___x_1289_ = 2048;
v___x_1290_ = lean_uint32_dec_lt(v_r_1288_, v___x_1289_);
v___x_1291_ = 55296;
v___x_1292_ = lean_uint32_dec_le(v___x_1291_, v_r_1288_);
if (v___x_1292_ == 0)
{
return v_r_1288_;
}
else
{
uint32_t v___x_1293_; uint8_t v___x_1294_; 
v___x_1293_ = 57343;
v___x_1294_ = lean_uint32_dec_le(v_r_1288_, v___x_1293_);
return v_r_1288_;
}
}
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; uint8_t v___x_1298_; uint8_t v___x_1299_; uint8_t v___x_1300_; uint8_t v___x_1301_; uint8_t v_b_u2080_1302_; uint8_t v___x_1303_; uint8_t v_b_u2081_1304_; uint32_t v___x_1305_; uint32_t v___x_1306_; uint32_t v___x_1307_; uint32_t v___x_1308_; uint32_t v_r_1309_; uint32_t v___x_1310_; uint8_t v___x_1311_; 
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1296_ = lean_nat_add(v_i_1206_, v___x_1295_);
v___x_1297_ = lean_nat_dec_lt(v___x_1296_, v___x_1208_);
v___x_1298_ = lean_byte_array_fget(v_bytes_1205_, v___x_1296_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_uint8_land(v___x_1298_, v___x_1217_);
v___x_1300_ = lean_uint8_dec_eq(v___x_1299_, v___x_1211_);
v___x_1301_ = 31;
v_b_u2080_1302_ = lean_uint8_land(v___x_1210_, v___x_1301_);
v___x_1303_ = 63;
v_b_u2081_1304_ = lean_uint8_land(v___x_1298_, v___x_1303_);
v___x_1305_ = lean_uint8_to_uint32(v_b_u2080_1302_);
v___x_1306_ = 6;
v___x_1307_ = lean_uint32_shift_left(v___x_1305_, v___x_1306_);
v___x_1308_ = lean_uint8_to_uint32(v_b_u2081_1304_);
v_r_1309_ = lean_uint32_lor(v___x_1307_, v___x_1308_);
v___x_1310_ = 128;
v___x_1311_ = lean_uint32_dec_lt(v_r_1309_, v___x_1310_);
return v_r_1309_;
}
}
else
{
uint32_t v___x_1312_; 
v___x_1312_ = lean_uint8_to_uint32(v___x_1210_);
return v___x_1312_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___boxed(lean_object* v_bytes_1313_, lean_object* v_i_1314_, lean_object* v_h_1315_){
_start:
{
uint32_t v_res_1316_; lean_object* v_r_1317_; 
v_res_1316_ = l_ByteArray_utf8DecodeChar(v_bytes_1313_, v_i_1314_, v_h_1315_);
lean_dec(v_i_1314_);
lean_dec_ref(v_bytes_1313_);
v_r_1317_ = lean_box_uint32(v_res_1316_);
return v_r_1317_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableIsUTF8FirstByte(uint8_t v_c_1318_){
_start:
{
uint8_t v___x_1319_; uint8_t v___x_1320_; uint8_t v___x_1321_; uint8_t v___x_1322_; 
v___x_1319_ = 128;
v___x_1320_ = lean_uint8_land(v_c_1318_, v___x_1319_);
v___x_1321_ = 0;
v___x_1322_ = lean_uint8_dec_eq(v___x_1320_, v___x_1321_);
if (v___x_1322_ == 0)
{
uint8_t v___x_1323_; uint8_t v___x_1324_; uint8_t v___x_1325_; uint8_t v___x_1326_; 
v___x_1323_ = 224;
v___x_1324_ = lean_uint8_land(v_c_1318_, v___x_1323_);
v___x_1325_ = 192;
v___x_1326_ = lean_uint8_dec_eq(v___x_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
uint8_t v___x_1327_; uint8_t v___x_1328_; uint8_t v___x_1329_; 
v___x_1327_ = 240;
v___x_1328_ = lean_uint8_land(v_c_1318_, v___x_1327_);
v___x_1329_ = lean_uint8_dec_eq(v___x_1328_, v___x_1323_);
if (v___x_1329_ == 0)
{
uint8_t v___x_1330_; uint8_t v___x_1331_; uint8_t v___x_1332_; 
v___x_1330_ = 248;
v___x_1331_ = lean_uint8_land(v_c_1318_, v___x_1330_);
v___x_1332_ = lean_uint8_dec_eq(v___x_1331_, v___x_1327_);
return v___x_1332_;
}
else
{
return v___x_1329_;
}
}
else
{
return v___x_1326_;
}
}
else
{
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableIsUTF8FirstByte___boxed(lean_object* v_c_1333_){
_start:
{
uint8_t v_c_boxed_1334_; uint8_t v_res_1335_; lean_object* v_r_1336_; 
v_c_boxed_1334_ = lean_unbox(v_c_1333_);
v_res_1335_ = l_UInt8_instDecidableIsUTF8FirstByte(v_c_boxed_1334_);
v_r_1336_ = lean_box(v_res_1335_);
return v_r_1336_;
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg(uint8_t v_c_1337_){
_start:
{
uint8_t v___x_1338_; uint8_t v___x_1339_; uint8_t v___x_1340_; uint8_t v___x_1341_; 
v___x_1338_ = 128;
v___x_1339_ = lean_uint8_land(v_c_1337_, v___x_1338_);
v___x_1340_ = 0;
v___x_1341_ = lean_uint8_dec_eq(v___x_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
uint8_t v___x_1342_; uint8_t v___x_1343_; uint8_t v___x_1344_; uint8_t v___x_1345_; 
v___x_1342_ = 224;
v___x_1343_ = lean_uint8_land(v_c_1337_, v___x_1342_);
v___x_1344_ = 192;
v___x_1345_ = lean_uint8_dec_eq(v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
uint8_t v___x_1346_; uint8_t v___x_1347_; uint8_t v___x_1348_; 
v___x_1346_ = 240;
v___x_1347_ = lean_uint8_land(v_c_1337_, v___x_1346_);
v___x_1348_ = lean_uint8_dec_eq(v___x_1347_, v___x_1342_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_unsigned_to_nat(4u);
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_unsigned_to_nat(3u);
return v___x_1350_;
}
}
else
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_unsigned_to_nat(2u);
return v___x_1351_;
}
}
else
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_unsigned_to_nat(1u);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg___boxed(lean_object* v_c_1353_){
_start:
{
uint8_t v_c_boxed_1354_; lean_object* v_res_1355_; 
v_c_boxed_1354_ = lean_unbox(v_c_1353_);
v_res_1355_ = l_UInt8_utf8ByteSize___redArg(v_c_boxed_1354_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize(uint8_t v_c_1356_, lean_object* v___h_1357_){
_start:
{
uint8_t v___x_1358_; uint8_t v___x_1359_; uint8_t v___x_1360_; uint8_t v___x_1361_; 
v___x_1358_ = 128;
v___x_1359_ = lean_uint8_land(v_c_1356_, v___x_1358_);
v___x_1360_ = 0;
v___x_1361_ = lean_uint8_dec_eq(v___x_1359_, v___x_1360_);
if (v___x_1361_ == 0)
{
uint8_t v___x_1362_; uint8_t v___x_1363_; uint8_t v___x_1364_; uint8_t v___x_1365_; 
v___x_1362_ = 224;
v___x_1363_ = lean_uint8_land(v_c_1356_, v___x_1362_);
v___x_1364_ = 192;
v___x_1365_ = lean_uint8_dec_eq(v___x_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
uint8_t v___x_1366_; uint8_t v___x_1367_; uint8_t v___x_1368_; 
v___x_1366_ = 240;
v___x_1367_ = lean_uint8_land(v_c_1356_, v___x_1366_);
v___x_1368_ = lean_uint8_dec_eq(v___x_1367_, v___x_1362_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_unsigned_to_nat(4u);
return v___x_1369_;
}
else
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_unsigned_to_nat(3u);
return v___x_1370_;
}
}
else
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_unsigned_to_nat(2u);
return v___x_1371_;
}
}
else
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_unsigned_to_nat(1u);
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___boxed(lean_object* v_c_1373_, lean_object* v___h_1374_){
_start:
{
uint8_t v_c_boxed_1375_; lean_object* v_res_1376_; 
v_c_boxed_1375_ = lean_unbox(v_c_1373_);
v_res_1376_ = l_UInt8_utf8ByteSize(v_c_boxed_1375_, v___h_1374_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(uint8_t v_x_1377_){
_start:
{
switch(v_x_1377_)
{
case 0:
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_unsigned_to_nat(0u);
return v___x_1378_;
}
case 1:
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_unsigned_to_nat(1u);
return v___x_1379_;
}
case 2:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_unsigned_to_nat(2u);
return v___x_1380_;
}
case 3:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_unsigned_to_nat(3u);
return v___x_1381_;
}
default: 
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_unsigned_to_nat(4u);
return v___x_1382_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize___boxed(lean_object* v_x_1383_){
_start:
{
uint8_t v_x_54__boxed_1384_; lean_object* v_res_1385_; 
v_x_54__boxed_1384_ = lean_unbox(v_x_1383_);
v_res_1385_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(v_x_54__boxed_1384_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(uint8_t v_x_1386_, lean_object* v_h__1_1387_, lean_object* v_h__2_1388_, lean_object* v_h__3_1389_, lean_object* v_h__4_1390_, lean_object* v_h__5_1391_){
_start:
{
switch(v_x_1386_)
{
case 0:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec(v_h__5_1391_);
lean_dec(v_h__4_1390_);
lean_dec(v_h__3_1389_);
lean_dec(v_h__2_1388_);
v___x_1392_ = lean_box(0);
v___x_1393_ = lean_apply_1(v_h__1_1387_, v___x_1392_);
return v___x_1393_;
}
case 1:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_dec(v_h__5_1391_);
lean_dec(v_h__4_1390_);
lean_dec(v_h__3_1389_);
lean_dec(v_h__1_1387_);
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_apply_1(v_h__2_1388_, v___x_1394_);
return v___x_1395_;
}
case 2:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_dec(v_h__5_1391_);
lean_dec(v_h__4_1390_);
lean_dec(v_h__2_1388_);
lean_dec(v_h__1_1387_);
v___x_1396_ = lean_box(0);
v___x_1397_ = lean_apply_1(v_h__3_1389_, v___x_1396_);
return v___x_1397_;
}
case 3:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec(v_h__5_1391_);
lean_dec(v_h__3_1389_);
lean_dec(v_h__2_1388_);
lean_dec(v_h__1_1387_);
v___x_1398_ = lean_box(0);
v___x_1399_ = lean_apply_1(v_h__4_1390_, v___x_1398_);
return v___x_1399_;
}
default: 
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec(v_h__4_1390_);
lean_dec(v_h__3_1389_);
lean_dec(v_h__2_1388_);
lean_dec(v_h__1_1387_);
v___x_1400_ = lean_box(0);
v___x_1401_ = lean_apply_1(v_h__5_1391_, v___x_1400_);
return v___x_1401_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg___boxed(lean_object* v_x_1402_, lean_object* v_h__1_1403_, lean_object* v_h__2_1404_, lean_object* v_h__3_1405_, lean_object* v_h__4_1406_, lean_object* v_h__5_1407_){
_start:
{
uint8_t v_x_51__boxed_1408_; lean_object* v_res_1409_; 
v_x_51__boxed_1408_ = lean_unbox(v_x_1402_);
v_res_1409_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(v_x_51__boxed_1408_, v_h__1_1403_, v_h__2_1404_, v_h__3_1405_, v_h__4_1406_, v_h__5_1407_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(lean_object* v_motive_1410_, uint8_t v_x_1411_, lean_object* v_h__1_1412_, lean_object* v_h__2_1413_, lean_object* v_h__3_1414_, lean_object* v_h__4_1415_, lean_object* v_h__5_1416_){
_start:
{
switch(v_x_1411_)
{
case 0:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_dec(v_h__5_1416_);
lean_dec(v_h__4_1415_);
lean_dec(v_h__3_1414_);
lean_dec(v_h__2_1413_);
v___x_1417_ = lean_box(0);
v___x_1418_ = lean_apply_1(v_h__1_1412_, v___x_1417_);
return v___x_1418_;
}
case 1:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_dec(v_h__5_1416_);
lean_dec(v_h__4_1415_);
lean_dec(v_h__3_1414_);
lean_dec(v_h__1_1412_);
v___x_1419_ = lean_box(0);
v___x_1420_ = lean_apply_1(v_h__2_1413_, v___x_1419_);
return v___x_1420_;
}
case 2:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_dec(v_h__5_1416_);
lean_dec(v_h__4_1415_);
lean_dec(v_h__2_1413_);
lean_dec(v_h__1_1412_);
v___x_1421_ = lean_box(0);
v___x_1422_ = lean_apply_1(v_h__3_1414_, v___x_1421_);
return v___x_1422_;
}
case 3:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_dec(v_h__5_1416_);
lean_dec(v_h__3_1414_);
lean_dec(v_h__2_1413_);
lean_dec(v_h__1_1412_);
v___x_1423_ = lean_box(0);
v___x_1424_ = lean_apply_1(v_h__4_1415_, v___x_1423_);
return v___x_1424_;
}
default: 
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec(v_h__4_1415_);
lean_dec(v_h__3_1414_);
lean_dec(v_h__2_1413_);
lean_dec(v_h__1_1412_);
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_apply_1(v_h__5_1416_, v___x_1425_);
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___boxed(lean_object* v_motive_1427_, lean_object* v_x_1428_, lean_object* v_h__1_1429_, lean_object* v_h__2_1430_, lean_object* v_h__3_1431_, lean_object* v_h__4_1432_, lean_object* v_h__5_1433_){
_start:
{
uint8_t v_x_74__boxed_1434_; lean_object* v_res_1435_; 
v_x_74__boxed_1434_ = lean_unbox(v_x_1428_);
v_res_1435_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(v_motive_1427_, v_x_74__boxed_1434_, v_h__1_1429_, v_h__2_1430_, v_h__3_1431_, v_h__4_1432_, v_h__5_1433_);
return v_res_1435_;
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

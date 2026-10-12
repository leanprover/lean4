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
lean_object* l_String_utf8EncodeCharFast(uint32_t v_c_1_){
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
LEAN_EXPORT void l_String_utf8EncodeCharFast_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1_ = stack[0].m_num;
lean_object* v_res_84_;
v_res_84_ = l_String_utf8EncodeCharFast(v_c_1_);
stack->m_obj
 = v_res_84_;
}
LEAN_EXPORT lean_object* l_String_utf8EncodeCharFast___boxed(lean_object* v_c_85_){
_start:
{
uint32_t v_c_boxed_86_; lean_object* v_res_87_; 
v_c_boxed_86_ = lean_unbox_uint32(v_c_85_);
lean_dec(v_c_85_);
v_res_87_ = l_String_utf8EncodeCharFast(v_c_boxed_86_);
return v_res_87_;
}
}
lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___impl(uint8_t v_x_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_box(v_x_88_);
v___x_90_ = lean_obj_tag_nat(v___x_89_);
lean_dec(v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_88_ = stack[0].m_num;
lean_object* v_res_91_;
v_res_91_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___impl(v_x_88_);
stack->m_obj
 = v_res_91_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___impl___boxed(lean_object* v_x_92_){
_start:
{
uint8_t v_x_4__boxed_93_; lean_object* v_res_94_; 
v_x_4__boxed_93_ = lean_unbox(v_x_92_);
v_res_94_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___impl(v_x_4__boxed_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg(lean_object* v_k_95_){
_start:
{
lean_inc(v_k_95_);
return v_k_95_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg___boxed(lean_object* v_k_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg(v_k_96_);
lean_dec(v_k_96_);
return v_res_97_;
}
}
lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim(lean_object* v_motive_98_, lean_object* v_ctorIdx_99_, uint8_t v_t_100_, lean_object* v_h_101_, lean_object* v_k_102_){
_start:
{
lean_inc(v_k_102_);
return v_k_102_;
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_99_ = stack[1].m_obj;
uint8_t v_t_100_ = stack[2].m_num;
lean_object* v_k_102_ = stack[4].m_obj;
lean_object* v_res_103_;
v_res_103_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim(lean_box(0), v_ctorIdx_99_, v_t_100_, lean_box(0), v_k_102_);
stack->m_obj
 = v_res_103_;
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
lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(lean_object* v_motive_114_, uint8_t v_t_115_, lean_object* v_h_116_, lean_object* v_invalid_117_){
_start:
{
lean_inc(v_invalid_117_);
return v_invalid_117_;
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_115_ = stack[1].m_num;
lean_object* v_invalid_117_ = stack[3].m_obj;
lean_object* v_res_118_;
v_res_118_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(lean_box(0), v_t_115_, lean_box(0), v_invalid_117_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___boxed(lean_object* v_motive_119_, lean_object* v_t_120_, lean_object* v_h_121_, lean_object* v_invalid_122_){
_start:
{
uint8_t v_t_boxed_123_; lean_object* v_res_124_; 
v_t_boxed_123_ = lean_unbox(v_t_120_);
v_res_124_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(v_motive_119_, v_t_boxed_123_, v_h_121_, v_invalid_122_);
lean_dec(v_invalid_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg(lean_object* v_done_125_){
_start:
{
lean_inc(v_done_125_);
return v_done_125_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg___boxed(lean_object* v_done_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg(v_done_126_);
lean_dec(v_done_126_);
return v_res_127_;
}
}
lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(lean_object* v_motive_128_, uint8_t v_t_129_, lean_object* v_h_130_, lean_object* v_done_131_){
_start:
{
lean_inc(v_done_131_);
return v_done_131_;
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_129_ = stack[1].m_num;
lean_object* v_done_131_ = stack[3].m_obj;
lean_object* v_res_132_;
v_res_132_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(lean_box(0), v_t_129_, lean_box(0), v_done_131_);
stack->m_obj
 = v_res_132_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___boxed(lean_object* v_motive_133_, lean_object* v_t_134_, lean_object* v_h_135_, lean_object* v_done_136_){
_start:
{
uint8_t v_t_boxed_137_; lean_object* v_res_138_; 
v_t_boxed_137_ = lean_unbox(v_t_134_);
v_res_138_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(v_motive_133_, v_t_boxed_137_, v_h_135_, v_done_136_);
lean_dec(v_done_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg(lean_object* v_oneMore_139_){
_start:
{
lean_inc(v_oneMore_139_);
return v_oneMore_139_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg___boxed(lean_object* v_oneMore_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg(v_oneMore_140_);
lean_dec(v_oneMore_140_);
return v_res_141_;
}
}
lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(lean_object* v_motive_142_, uint8_t v_t_143_, lean_object* v_h_144_, lean_object* v_oneMore_145_){
_start:
{
lean_inc(v_oneMore_145_);
return v_oneMore_145_;
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_143_ = stack[1].m_num;
lean_object* v_oneMore_145_ = stack[3].m_obj;
lean_object* v_res_146_;
v_res_146_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(lean_box(0), v_t_143_, lean_box(0), v_oneMore_145_);
stack->m_obj
 = v_res_146_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___boxed(lean_object* v_motive_147_, lean_object* v_t_148_, lean_object* v_h_149_, lean_object* v_oneMore_150_){
_start:
{
uint8_t v_t_boxed_151_; lean_object* v_res_152_; 
v_t_boxed_151_ = lean_unbox(v_t_148_);
v_res_152_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(v_motive_147_, v_t_boxed_151_, v_h_149_, v_oneMore_150_);
lean_dec(v_oneMore_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg(lean_object* v_twoMore_153_){
_start:
{
lean_inc(v_twoMore_153_);
return v_twoMore_153_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg___boxed(lean_object* v_twoMore_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg(v_twoMore_154_);
lean_dec(v_twoMore_154_);
return v_res_155_;
}
}
lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(lean_object* v_motive_156_, uint8_t v_t_157_, lean_object* v_h_158_, lean_object* v_twoMore_159_){
_start:
{
lean_inc(v_twoMore_159_);
return v_twoMore_159_;
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_157_ = stack[1].m_num;
lean_object* v_twoMore_159_ = stack[3].m_obj;
lean_object* v_res_160_;
v_res_160_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(lean_box(0), v_t_157_, lean_box(0), v_twoMore_159_);
stack->m_obj
 = v_res_160_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___boxed(lean_object* v_motive_161_, lean_object* v_t_162_, lean_object* v_h_163_, lean_object* v_twoMore_164_){
_start:
{
uint8_t v_t_boxed_165_; lean_object* v_res_166_; 
v_t_boxed_165_ = lean_unbox(v_t_162_);
v_res_166_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(v_motive_161_, v_t_boxed_165_, v_h_163_, v_twoMore_164_);
lean_dec(v_twoMore_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg(lean_object* v_threeMore_167_){
_start:
{
lean_inc(v_threeMore_167_);
return v_threeMore_167_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg___boxed(lean_object* v_threeMore_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg(v_threeMore_168_);
lean_dec(v_threeMore_168_);
return v_res_169_;
}
}
lean_object* l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim(lean_object* v_motive_170_, uint8_t v_t_171_, lean_object* v_h_172_, lean_object* v_threeMore_173_){
_start:
{
lean_inc(v_threeMore_173_);
return v_threeMore_173_;
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_171_ = stack[1].m_num;
lean_object* v_threeMore_173_ = stack[3].m_obj;
lean_object* v_res_174_;
v_res_174_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim(lean_box(0), v_t_171_, lean_box(0), v_threeMore_173_);
stack->m_obj
 = v_res_174_;
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
uint8_t l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(uint8_t v_b_181_){
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
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_parseFirstByte_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_181_ = stack[0].m_num;
uint8_t v_res_201_;
v_res_201_ = l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(v_b_181_);
stack->m_num = v_res_201_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_parseFirstByte___boxed(lean_object* v_b_202_){
_start:
{
uint8_t v_b_boxed_203_; uint8_t v_res_204_; lean_object* v_r_205_; 
v_b_boxed_203_ = lean_unbox(v_b_202_);
v_res_204_ = l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(v_b_boxed_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
uint8_t l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(uint8_t v_b_206_){
_start:
{
uint8_t v___x_207_; uint8_t v___x_208_; uint8_t v___x_209_; uint8_t v___x_210_; 
v___x_207_ = 192;
v___x_208_ = lean_uint8_land(v_b_206_, v___x_207_);
v___x_209_ = 128;
v___x_210_ = lean_uint8_dec_eq(v___x_208_, v___x_209_);
if (v___x_210_ == 0)
{
uint8_t v___x_211_; 
v___x_211_ = 1;
return v___x_211_;
}
else
{
uint8_t v___x_212_; 
v___x_212_ = 0;
return v___x_212_;
}
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_206_ = stack[0].m_num;
uint8_t v_res_213_;
v_res_213_ = l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(v_b_206_);
stack->m_num = v_res_213_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte___boxed(lean_object* v_b_214_){
_start:
{
uint8_t v_b_boxed_215_; uint8_t v_res_216_; lean_object* v_r_217_; 
v_b_boxed_215_ = lean_unbox(v_b_214_);
v_res_216_ = l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(v_b_boxed_215_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(uint8_t v_w_218_){
_start:
{
uint32_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_uint8_to_uint32(v_w_218_);
v___x_220_ = lean_box_uint32(v___x_219_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_w_218_ = stack[0].m_num;
lean_object* v_res_222_;
v_res_222_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(v_w_218_);
stack->m_obj
 = v_res_222_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg___boxed(lean_object* v_w_223_){
_start:
{
uint8_t v_w_boxed_224_; lean_object* v_res_225_; 
v_w_boxed_224_ = lean_unbox(v_w_223_);
v_res_225_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(v_w_boxed_224_);
return v_res_225_;
}
}
lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(uint8_t v_w_226_, lean_object* v_h_227_){
_start:
{
uint32_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = lean_uint8_to_uint32(v_w_226_);
v___x_229_ = lean_box_uint32(v___x_228_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_assemble_u2081_0interp(lean_interpreter_value* stack)
{
uint8_t v_w_226_ = stack[0].m_num;
lean_object* v_res_231_;
v_res_231_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(v_w_226_, lean_box(0));
stack->m_obj
 = v_res_231_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___boxed(lean_object* v_w_232_, lean_object* v_h_233_){
_start:
{
uint8_t v_w_boxed_234_; lean_object* v_res_235_; 
v_w_boxed_234_ = lean_unbox(v_w_232_);
v_res_235_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(v_w_boxed_234_, v_h_233_);
return v_res_235_;
}
}
uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg(){
_start:
{
uint8_t v___x_237_; 
v___x_237_ = 1;
return v___x_237_;
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_238_;
v_res_238_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg();
stack->m_num = v_res_238_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg___boxed(lean_object* v___dummy_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2081___redArg();
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2081(uint8_t v_w_242_, uint8_t v___w_243_, lean_object* v___h_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = 1;
return v___x_245_;
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_verify_u2081_0interp(lean_interpreter_value* stack)
{
uint8_t v_w_242_ = stack[0].m_num;
uint8_t v___w_243_ = stack[1].m_num;
uint8_t v_res_246_;
v_res_246_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2081(v_w_242_, v___w_243_, lean_box(0));
stack->m_num = v_res_246_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2081___boxed(lean_object* v_w_247_, lean_object* v___w_248_, lean_object* v___h_249_){
_start:
{
uint8_t v_w_boxed_250_; uint8_t v___w_boxed_251_; uint8_t v_res_252_; lean_object* v_r_253_; 
v_w_boxed_250_ = lean_unbox(v_w_247_);
v___w_boxed_251_ = lean_unbox(v___w_248_);
v_res_252_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2081(v_w_boxed_250_, v___w_boxed_251_, v___h_249_);
v_r_253_ = lean_box(v_res_252_);
return v_r_253_;
}
}
uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(uint8_t v_w_254_, uint8_t v_x_255_){
_start:
{
uint8_t v___x_256_; uint8_t v_b_u2080_257_; uint8_t v___x_258_; uint8_t v_b_u2081_259_; uint32_t v___x_260_; uint32_t v___x_261_; uint32_t v___x_262_; uint32_t v___x_263_; uint32_t v___x_264_; 
v___x_256_ = 31;
v_b_u2080_257_ = lean_uint8_land(v_w_254_, v___x_256_);
v___x_258_ = 63;
v_b_u2081_259_ = lean_uint8_land(v_x_255_, v___x_258_);
v___x_260_ = lean_uint8_to_uint32(v_b_u2080_257_);
v___x_261_ = 6;
v___x_262_ = lean_uint32_shift_left(v___x_260_, v___x_261_);
v___x_263_ = lean_uint8_to_uint32(v_b_u2081_259_);
v___x_264_ = lean_uint32_lor(v___x_262_, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked_0interp(lean_interpreter_value* stack)
{
uint8_t v_w_254_ = stack[0].m_num;
uint8_t v_x_255_ = stack[1].m_num;
uint32_t v_res_265_;
v_res_265_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(v_w_254_, v_x_255_);
stack->m_num = v_res_265_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked___boxed(lean_object* v_w_266_, lean_object* v_x_267_){
_start:
{
uint8_t v_w_boxed_268_; uint8_t v_x_boxed_269_; uint32_t v_res_270_; lean_object* v_r_271_; 
v_w_boxed_268_ = lean_unbox(v_w_266_);
v_x_boxed_269_ = lean_unbox(v_x_267_);
v_res_270_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(v_w_boxed_268_, v_x_boxed_269_);
v_r_271_ = lean_box_uint32(v_res_270_);
return v_r_271_;
}
}
lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(uint8_t v_w_272_, uint8_t v_x_273_){
_start:
{
uint8_t v___x_274_; uint8_t v___x_275_; uint8_t v___x_276_; uint8_t v___x_277_; 
v___x_274_ = 192;
v___x_275_ = lean_uint8_land(v_x_273_, v___x_274_);
v___x_276_ = 128;
v___x_277_ = lean_uint8_dec_eq(v___x_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
v___x_278_ = lean_box(0);
return v___x_278_;
}
else
{
uint8_t v___x_279_; uint8_t v_b_u2080_280_; uint8_t v___x_281_; uint8_t v_b_u2081_282_; uint32_t v___x_283_; uint32_t v___x_284_; uint32_t v___x_285_; uint32_t v___x_286_; uint32_t v_r_287_; uint32_t v___x_288_; uint8_t v___x_289_; 
v___x_279_ = 31;
v_b_u2080_280_ = lean_uint8_land(v_w_272_, v___x_279_);
v___x_281_ = 63;
v_b_u2081_282_ = lean_uint8_land(v_x_273_, v___x_281_);
v___x_283_ = lean_uint8_to_uint32(v_b_u2080_280_);
v___x_284_ = 6;
v___x_285_ = lean_uint32_shift_left(v___x_283_, v___x_284_);
v___x_286_ = lean_uint8_to_uint32(v_b_u2081_282_);
v_r_287_ = lean_uint32_lor(v___x_285_, v___x_286_);
v___x_288_ = 128;
v___x_289_ = lean_uint32_dec_lt(v_r_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_box_uint32(v_r_287_);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_box(0);
return v___x_292_;
}
}
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_assemble_u2082_0interp(lean_interpreter_value* stack)
{
uint8_t v_w_272_ = stack[0].m_num;
uint8_t v_x_273_ = stack[1].m_num;
lean_object* v_res_293_;
v_res_293_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(v_w_272_, v_x_273_);
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2082___boxed(lean_object* v_w_294_, lean_object* v_x_295_){
_start:
{
uint8_t v_w_boxed_296_; uint8_t v_x_boxed_297_; lean_object* v_res_298_; 
v_w_boxed_296_ = lean_unbox(v_w_294_);
v_x_boxed_297_ = lean_unbox(v_x_295_);
v_res_298_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(v_w_boxed_296_, v_x_boxed_297_);
return v_res_298_;
}
}
uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2082(uint8_t v_w_299_, uint8_t v_x_300_){
_start:
{
uint8_t v___x_301_; uint8_t v___x_302_; uint8_t v___x_303_; uint8_t v___x_304_; 
v___x_301_ = 192;
v___x_302_ = lean_uint8_land(v_x_300_, v___x_301_);
v___x_303_ = 128;
v___x_304_ = lean_uint8_dec_eq(v___x_302_, v___x_303_);
if (v___x_304_ == 0)
{
return v___x_304_;
}
else
{
uint8_t v___x_305_; uint8_t v_b_u2080_306_; uint8_t v___x_307_; uint8_t v_b_u2081_308_; uint32_t v___x_309_; uint32_t v___x_310_; uint32_t v___x_311_; uint32_t v___x_312_; uint32_t v_r_313_; uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_305_ = 31;
v_b_u2080_306_ = lean_uint8_land(v_w_299_, v___x_305_);
v___x_307_ = 63;
v_b_u2081_308_ = lean_uint8_land(v_x_300_, v___x_307_);
v___x_309_ = lean_uint8_to_uint32(v_b_u2080_306_);
v___x_310_ = 6;
v___x_311_ = lean_uint32_shift_left(v___x_309_, v___x_310_);
v___x_312_ = lean_uint8_to_uint32(v_b_u2081_308_);
v_r_313_ = lean_uint32_lor(v___x_311_, v___x_312_);
v___x_314_ = 128;
v___x_315_ = lean_uint32_dec_le(v___x_314_, v_r_313_);
return v___x_315_;
}
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_verify_u2082_0interp(lean_interpreter_value* stack)
{
uint8_t v_w_299_ = stack[0].m_num;
uint8_t v_x_300_ = stack[1].m_num;
uint8_t v_res_316_;
v_res_316_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2082(v_w_299_, v_x_300_);
stack->m_num = v_res_316_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2082___boxed(lean_object* v_w_317_, lean_object* v_x_318_){
_start:
{
uint8_t v_w_boxed_319_; uint8_t v_x_boxed_320_; uint8_t v_res_321_; lean_object* v_r_322_; 
v_w_boxed_319_ = lean_unbox(v_w_317_);
v_x_boxed_320_ = lean_unbox(v_x_318_);
v_res_321_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2082(v_w_boxed_319_, v_x_boxed_320_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(uint8_t v_w_323_, uint8_t v_x_324_, uint8_t v_y_325_){
_start:
{
uint8_t v___x_326_; uint8_t v_b_u2080_327_; uint8_t v___x_328_; uint8_t v_b_u2081_329_; uint8_t v_b_u2082_330_; uint32_t v___x_331_; uint32_t v___x_332_; uint32_t v___x_333_; uint32_t v___x_334_; uint32_t v___x_335_; uint32_t v___x_336_; uint32_t v___x_337_; uint32_t v___x_338_; uint32_t v___x_339_; 
v___x_326_ = 15;
v_b_u2080_327_ = lean_uint8_land(v_w_323_, v___x_326_);
v___x_328_ = 63;
v_b_u2081_329_ = lean_uint8_land(v_x_324_, v___x_328_);
v_b_u2082_330_ = lean_uint8_land(v_y_325_, v___x_328_);
v___x_331_ = lean_uint8_to_uint32(v_b_u2080_327_);
v___x_332_ = 12;
v___x_333_ = lean_uint32_shift_left(v___x_331_, v___x_332_);
v___x_334_ = lean_uint8_to_uint32(v_b_u2081_329_);
v___x_335_ = 6;
v___x_336_ = lean_uint32_shift_left(v___x_334_, v___x_335_);
v___x_337_ = lean_uint32_lor(v___x_333_, v___x_336_);
v___x_338_ = lean_uint8_to_uint32(v_b_u2082_330_);
v___x_339_ = lean_uint32_lor(v___x_337_, v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked_0interp(lean_interpreter_value* stack)
{
uint8_t v_w_323_ = stack[0].m_num;
uint8_t v_x_324_ = stack[1].m_num;
uint8_t v_y_325_ = stack[2].m_num;
uint32_t v_res_340_;
v_res_340_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(v_w_323_, v_x_324_, v_y_325_);
stack->m_num = v_res_340_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked___boxed(lean_object* v_w_341_, lean_object* v_x_342_, lean_object* v_y_343_){
_start:
{
uint8_t v_w_boxed_344_; uint8_t v_x_boxed_345_; uint8_t v_y_boxed_346_; uint32_t v_res_347_; lean_object* v_r_348_; 
v_w_boxed_344_ = lean_unbox(v_w_341_);
v_x_boxed_345_ = lean_unbox(v_x_342_);
v_y_boxed_346_ = lean_unbox(v_y_343_);
v_res_347_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(v_w_boxed_344_, v_x_boxed_345_, v_y_boxed_346_);
v_r_348_ = lean_box_uint32(v_res_347_);
return v_r_348_;
}
}
lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(uint8_t v_w_349_, uint8_t v_x_350_, uint8_t v_y_351_){
_start:
{
uint8_t v___x_352_; uint8_t v___x_353_; uint8_t v___x_354_; uint8_t v___x_355_; 
v___x_352_ = 192;
v___x_353_ = lean_uint8_land(v_x_350_, v___x_352_);
v___x_354_ = 128;
v___x_355_ = lean_uint8_dec_eq(v___x_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
v___x_356_ = lean_box(0);
return v___x_356_;
}
else
{
uint8_t v___x_357_; uint8_t v___x_358_; 
v___x_357_ = lean_uint8_land(v_y_351_, v___x_352_);
v___x_358_ = lean_uint8_dec_eq(v___x_357_, v___x_354_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
v___x_359_ = lean_box(0);
return v___x_359_;
}
else
{
uint8_t v___x_360_; uint8_t v_b_u2080_361_; uint8_t v___x_362_; uint8_t v_b_u2081_363_; uint8_t v_b_u2082_364_; uint32_t v___x_365_; uint32_t v___x_366_; uint32_t v___x_367_; uint32_t v___x_368_; uint32_t v___x_369_; uint32_t v___x_370_; uint32_t v___x_371_; uint32_t v___x_372_; uint32_t v_r_373_; uint32_t v___x_374_; uint8_t v___x_375_; 
v___x_360_ = 15;
v_b_u2080_361_ = lean_uint8_land(v_w_349_, v___x_360_);
v___x_362_ = 63;
v_b_u2081_363_ = lean_uint8_land(v_x_350_, v___x_362_);
v_b_u2082_364_ = lean_uint8_land(v_y_351_, v___x_362_);
v___x_365_ = lean_uint8_to_uint32(v_b_u2080_361_);
v___x_366_ = 12;
v___x_367_ = lean_uint32_shift_left(v___x_365_, v___x_366_);
v___x_368_ = lean_uint8_to_uint32(v_b_u2081_363_);
v___x_369_ = 6;
v___x_370_ = lean_uint32_shift_left(v___x_368_, v___x_369_);
v___x_371_ = lean_uint32_lor(v___x_367_, v___x_370_);
v___x_372_ = lean_uint8_to_uint32(v_b_u2082_364_);
v_r_373_ = lean_uint32_lor(v___x_371_, v___x_372_);
v___x_374_ = 2048;
v___x_375_ = lean_uint32_dec_lt(v_r_373_, v___x_374_);
if (v___x_375_ == 0)
{
uint32_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = 55296;
v___x_377_ = lean_uint32_dec_le(v___x_376_, v_r_373_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_box_uint32(v_r_373_);
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
else
{
uint32_t v___x_380_; uint8_t v___x_381_; 
v___x_380_ = 57343;
v___x_381_ = lean_uint32_dec_le(v_r_373_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_box_uint32(v_r_373_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
else
{
lean_object* v___x_384_; 
v___x_384_ = lean_box(0);
return v___x_384_;
}
}
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_box(0);
return v___x_385_;
}
}
}
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_assemble_u2083_0interp(lean_interpreter_value* stack)
{
uint8_t v_w_349_ = stack[0].m_num;
uint8_t v_x_350_ = stack[1].m_num;
uint8_t v_y_351_ = stack[2].m_num;
lean_object* v_res_386_;
v_res_386_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(v_w_349_, v_x_350_, v_y_351_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2083___boxed(lean_object* v_w_387_, lean_object* v_x_388_, lean_object* v_y_389_){
_start:
{
uint8_t v_w_boxed_390_; uint8_t v_x_boxed_391_; uint8_t v_y_boxed_392_; lean_object* v_res_393_; 
v_w_boxed_390_ = lean_unbox(v_w_387_);
v_x_boxed_391_ = lean_unbox(v_x_388_);
v_y_boxed_392_ = lean_unbox(v_y_389_);
v_res_393_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(v_w_boxed_390_, v_x_boxed_391_, v_y_boxed_392_);
return v_res_393_;
}
}
uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2083(uint8_t v_w_394_, uint8_t v_x_395_, uint8_t v_y_396_){
_start:
{
uint8_t v___x_397_; uint8_t v___x_398_; uint8_t v___x_399_; uint8_t v___x_400_; 
v___x_397_ = 192;
v___x_398_ = lean_uint8_land(v_x_395_, v___x_397_);
v___x_399_ = 128;
v___x_400_ = lean_uint8_dec_eq(v___x_398_, v___x_399_);
if (v___x_400_ == 0)
{
return v___x_400_;
}
else
{
uint8_t v___x_401_; uint8_t v___x_402_; uint8_t v___x_403_; 
v___x_401_ = 0;
v___x_402_ = lean_uint8_land(v_y_396_, v___x_397_);
v___x_403_ = lean_uint8_dec_eq(v___x_402_, v___x_399_);
if (v___x_403_ == 0)
{
return v___x_401_;
}
else
{
uint8_t v___x_404_; uint8_t v_b_u2080_405_; uint8_t v___x_406_; uint8_t v_b_u2081_407_; uint8_t v_b_u2082_408_; uint32_t v___x_409_; uint32_t v___x_410_; uint32_t v___x_411_; uint32_t v___x_412_; uint32_t v___x_413_; uint32_t v___x_414_; uint32_t v___x_415_; uint32_t v___x_416_; uint32_t v_r_417_; uint32_t v___x_418_; uint8_t v___x_419_; 
v___x_404_ = 15;
v_b_u2080_405_ = lean_uint8_land(v_w_394_, v___x_404_);
v___x_406_ = 63;
v_b_u2081_407_ = lean_uint8_land(v_x_395_, v___x_406_);
v_b_u2082_408_ = lean_uint8_land(v_y_396_, v___x_406_);
v___x_409_ = lean_uint8_to_uint32(v_b_u2080_405_);
v___x_410_ = 12;
v___x_411_ = lean_uint32_shift_left(v___x_409_, v___x_410_);
v___x_412_ = lean_uint8_to_uint32(v_b_u2081_407_);
v___x_413_ = 6;
v___x_414_ = lean_uint32_shift_left(v___x_412_, v___x_413_);
v___x_415_ = lean_uint32_lor(v___x_411_, v___x_414_);
v___x_416_ = lean_uint8_to_uint32(v_b_u2082_408_);
v_r_417_ = lean_uint32_lor(v___x_415_, v___x_416_);
v___x_418_ = 2048;
v___x_419_ = lean_uint32_dec_le(v___x_418_, v_r_417_);
if (v___x_419_ == 0)
{
return v___x_401_;
}
else
{
uint32_t v___x_420_; uint8_t v___x_421_; 
v___x_420_ = 55296;
v___x_421_ = lean_uint32_dec_lt(v_r_417_, v___x_420_);
if (v___x_421_ == 0)
{
uint32_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = 57343;
v___x_423_ = lean_uint32_dec_lt(v___x_422_, v_r_417_);
return v___x_423_;
}
else
{
return v___x_421_;
}
}
}
}
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_verify_u2083_0interp(lean_interpreter_value* stack)
{
uint8_t v_w_394_ = stack[0].m_num;
uint8_t v_x_395_ = stack[1].m_num;
uint8_t v_y_396_ = stack[2].m_num;
uint8_t v_res_424_;
v_res_424_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2083(v_w_394_, v_x_395_, v_y_396_);
stack->m_num = v_res_424_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2083___boxed(lean_object* v_w_425_, lean_object* v_x_426_, lean_object* v_y_427_){
_start:
{
uint8_t v_w_boxed_428_; uint8_t v_x_boxed_429_; uint8_t v_y_boxed_430_; uint8_t v_res_431_; lean_object* v_r_432_; 
v_w_boxed_428_ = lean_unbox(v_w_425_);
v_x_boxed_429_ = lean_unbox(v_x_426_);
v_y_boxed_430_ = lean_unbox(v_y_427_);
v_res_431_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2083(v_w_boxed_428_, v_x_boxed_429_, v_y_boxed_430_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
uint32_t l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(uint8_t v_w_433_, uint8_t v_x_434_, uint8_t v_y_435_, uint8_t v_z_436_){
_start:
{
uint8_t v___x_437_; uint8_t v_b_u2080_438_; uint8_t v___x_439_; uint8_t v_b_u2081_440_; uint8_t v_b_u2082_441_; uint8_t v_b_u2083_442_; uint32_t v___x_443_; uint32_t v___x_444_; uint32_t v___x_445_; uint32_t v___x_446_; uint32_t v___x_447_; uint32_t v___x_448_; uint32_t v___x_449_; uint32_t v___x_450_; uint32_t v___x_451_; uint32_t v___x_452_; uint32_t v___x_453_; uint32_t v___x_454_; uint32_t v___x_455_; 
v___x_437_ = 7;
v_b_u2080_438_ = lean_uint8_land(v_w_433_, v___x_437_);
v___x_439_ = 63;
v_b_u2081_440_ = lean_uint8_land(v_x_434_, v___x_439_);
v_b_u2082_441_ = lean_uint8_land(v_y_435_, v___x_439_);
v_b_u2083_442_ = lean_uint8_land(v_z_436_, v___x_439_);
v___x_443_ = lean_uint8_to_uint32(v_b_u2080_438_);
v___x_444_ = 18;
v___x_445_ = lean_uint32_shift_left(v___x_443_, v___x_444_);
v___x_446_ = lean_uint8_to_uint32(v_b_u2081_440_);
v___x_447_ = 12;
v___x_448_ = lean_uint32_shift_left(v___x_446_, v___x_447_);
v___x_449_ = lean_uint32_lor(v___x_445_, v___x_448_);
v___x_450_ = lean_uint8_to_uint32(v_b_u2082_441_);
v___x_451_ = 6;
v___x_452_ = lean_uint32_shift_left(v___x_450_, v___x_451_);
v___x_453_ = lean_uint32_lor(v___x_449_, v___x_452_);
v___x_454_ = lean_uint8_to_uint32(v_b_u2083_442_);
v___x_455_ = lean_uint32_lor(v___x_453_, v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked_0interp(lean_interpreter_value* stack)
{
uint8_t v_w_433_ = stack[0].m_num;
uint8_t v_x_434_ = stack[1].m_num;
uint8_t v_y_435_ = stack[2].m_num;
uint8_t v_z_436_ = stack[3].m_num;
uint32_t v_res_456_;
v_res_456_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(v_w_433_, v_x_434_, v_y_435_, v_z_436_);
stack->m_num = v_res_456_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked___boxed(lean_object* v_w_457_, lean_object* v_x_458_, lean_object* v_y_459_, lean_object* v_z_460_){
_start:
{
uint8_t v_w_boxed_461_; uint8_t v_x_boxed_462_; uint8_t v_y_boxed_463_; uint8_t v_z_boxed_464_; uint32_t v_res_465_; lean_object* v_r_466_; 
v_w_boxed_461_ = lean_unbox(v_w_457_);
v_x_boxed_462_ = lean_unbox(v_x_458_);
v_y_boxed_463_ = lean_unbox(v_y_459_);
v_z_boxed_464_ = lean_unbox(v_z_460_);
v_res_465_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(v_w_boxed_461_, v_x_boxed_462_, v_y_boxed_463_, v_z_boxed_464_);
v_r_466_ = lean_box_uint32(v_res_465_);
return v_r_466_;
}
}
lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(uint8_t v_w_467_, uint8_t v_x_468_, uint8_t v_y_469_, uint8_t v_z_470_){
_start:
{
uint8_t v___x_471_; uint8_t v___x_472_; uint8_t v___x_473_; uint8_t v___x_474_; 
v___x_471_ = 192;
v___x_472_ = lean_uint8_land(v_x_468_, v___x_471_);
v___x_473_ = 128;
v___x_474_ = lean_uint8_dec_eq(v___x_472_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
v___x_475_ = lean_box(0);
return v___x_475_;
}
else
{
uint8_t v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_uint8_land(v_y_469_, v___x_471_);
v___x_477_ = lean_uint8_dec_eq(v___x_476_, v___x_473_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
v___x_478_ = lean_box(0);
return v___x_478_;
}
else
{
uint8_t v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_uint8_land(v_z_470_, v___x_471_);
v___x_480_ = lean_uint8_dec_eq(v___x_479_, v___x_473_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
v___x_481_ = lean_box(0);
return v___x_481_;
}
else
{
uint8_t v___x_482_; uint8_t v_b_u2080_483_; uint8_t v___x_484_; uint8_t v_b_u2081_485_; uint8_t v_b_u2082_486_; uint8_t v_b_u2083_487_; uint32_t v___x_488_; uint32_t v___x_489_; uint32_t v___x_490_; uint32_t v___x_491_; uint32_t v___x_492_; uint32_t v___x_493_; uint32_t v___x_494_; uint32_t v___x_495_; uint32_t v___x_496_; uint32_t v___x_497_; uint32_t v___x_498_; uint32_t v___x_499_; uint32_t v_r_500_; uint32_t v___x_501_; uint8_t v___x_502_; 
v___x_482_ = 7;
v_b_u2080_483_ = lean_uint8_land(v_w_467_, v___x_482_);
v___x_484_ = 63;
v_b_u2081_485_ = lean_uint8_land(v_x_468_, v___x_484_);
v_b_u2082_486_ = lean_uint8_land(v_y_469_, v___x_484_);
v_b_u2083_487_ = lean_uint8_land(v_z_470_, v___x_484_);
v___x_488_ = lean_uint8_to_uint32(v_b_u2080_483_);
v___x_489_ = 18;
v___x_490_ = lean_uint32_shift_left(v___x_488_, v___x_489_);
v___x_491_ = lean_uint8_to_uint32(v_b_u2081_485_);
v___x_492_ = 12;
v___x_493_ = lean_uint32_shift_left(v___x_491_, v___x_492_);
v___x_494_ = lean_uint32_lor(v___x_490_, v___x_493_);
v___x_495_ = lean_uint8_to_uint32(v_b_u2082_486_);
v___x_496_ = 6;
v___x_497_ = lean_uint32_shift_left(v___x_495_, v___x_496_);
v___x_498_ = lean_uint32_lor(v___x_494_, v___x_497_);
v___x_499_ = lean_uint8_to_uint32(v_b_u2083_487_);
v_r_500_ = lean_uint32_lor(v___x_498_, v___x_499_);
v___x_501_ = 65536;
v___x_502_ = lean_uint32_dec_lt(v_r_500_, v___x_501_);
if (v___x_502_ == 0)
{
uint32_t v___x_503_; uint8_t v___x_504_; 
v___x_503_ = 1114111;
v___x_504_ = lean_uint32_dec_lt(v___x_503_, v_r_500_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_box_uint32(v_r_500_);
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
else
{
lean_object* v___x_507_; 
v___x_507_ = lean_box(0);
return v___x_507_;
}
}
else
{
lean_object* v___x_508_; 
v___x_508_ = lean_box(0);
return v___x_508_;
}
}
}
}
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_assemble_u2084_0interp(lean_interpreter_value* stack)
{
uint8_t v_w_467_ = stack[0].m_num;
uint8_t v_x_468_ = stack[1].m_num;
uint8_t v_y_469_ = stack[2].m_num;
uint8_t v_z_470_ = stack[3].m_num;
lean_object* v_res_509_;
v_res_509_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(v_w_467_, v_x_468_, v_y_469_, v_z_470_);
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_assemble_u2084___boxed(lean_object* v_w_510_, lean_object* v_x_511_, lean_object* v_y_512_, lean_object* v_z_513_){
_start:
{
uint8_t v_w_boxed_514_; uint8_t v_x_boxed_515_; uint8_t v_y_boxed_516_; uint8_t v_z_boxed_517_; lean_object* v_res_518_; 
v_w_boxed_514_ = lean_unbox(v_w_510_);
v_x_boxed_515_ = lean_unbox(v_x_511_);
v_y_boxed_516_ = lean_unbox(v_y_512_);
v_z_boxed_517_ = lean_unbox(v_z_513_);
v_res_518_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(v_w_boxed_514_, v_x_boxed_515_, v_y_boxed_516_, v_z_boxed_517_);
return v_res_518_;
}
}
uint8_t l_ByteArray_utf8DecodeChar_x3f_verify_u2084(uint8_t v_w_519_, uint8_t v_x_520_, uint8_t v_y_521_, uint8_t v_z_522_){
_start:
{
uint8_t v___x_523_; uint8_t v___x_524_; uint8_t v___x_525_; uint8_t v___x_526_; 
v___x_523_ = 192;
v___x_524_ = lean_uint8_land(v_x_520_, v___x_523_);
v___x_525_ = 128;
v___x_526_ = lean_uint8_dec_eq(v___x_524_, v___x_525_);
if (v___x_526_ == 0)
{
return v___x_526_;
}
else
{
uint8_t v___x_527_; uint8_t v___x_528_; uint8_t v___x_529_; 
v___x_527_ = 0;
v___x_528_ = lean_uint8_land(v_y_521_, v___x_523_);
v___x_529_ = lean_uint8_dec_eq(v___x_528_, v___x_525_);
if (v___x_529_ == 0)
{
return v___x_527_;
}
else
{
uint8_t v___x_530_; uint8_t v___x_531_; 
v___x_530_ = lean_uint8_land(v_z_522_, v___x_523_);
v___x_531_ = lean_uint8_dec_eq(v___x_530_, v___x_525_);
if (v___x_531_ == 0)
{
return v___x_527_;
}
else
{
uint8_t v___x_532_; uint8_t v_b_u2080_533_; uint8_t v___x_534_; uint8_t v_b_u2081_535_; uint8_t v_b_u2082_536_; uint8_t v_b_u2083_537_; uint32_t v___x_538_; uint32_t v___x_539_; uint32_t v___x_540_; uint32_t v___x_541_; uint32_t v___x_542_; uint32_t v___x_543_; uint32_t v___x_544_; uint32_t v___x_545_; uint32_t v___x_546_; uint32_t v___x_547_; uint32_t v___x_548_; uint32_t v___x_549_; uint32_t v_r_550_; uint32_t v___x_551_; uint8_t v___x_552_; 
v___x_532_ = 7;
v_b_u2080_533_ = lean_uint8_land(v_w_519_, v___x_532_);
v___x_534_ = 63;
v_b_u2081_535_ = lean_uint8_land(v_x_520_, v___x_534_);
v_b_u2082_536_ = lean_uint8_land(v_y_521_, v___x_534_);
v_b_u2083_537_ = lean_uint8_land(v_z_522_, v___x_534_);
v___x_538_ = lean_uint8_to_uint32(v_b_u2080_533_);
v___x_539_ = 18;
v___x_540_ = lean_uint32_shift_left(v___x_538_, v___x_539_);
v___x_541_ = lean_uint8_to_uint32(v_b_u2081_535_);
v___x_542_ = 12;
v___x_543_ = lean_uint32_shift_left(v___x_541_, v___x_542_);
v___x_544_ = lean_uint32_lor(v___x_540_, v___x_543_);
v___x_545_ = lean_uint8_to_uint32(v_b_u2082_536_);
v___x_546_ = 6;
v___x_547_ = lean_uint32_shift_left(v___x_545_, v___x_546_);
v___x_548_ = lean_uint32_lor(v___x_544_, v___x_547_);
v___x_549_ = lean_uint8_to_uint32(v_b_u2083_537_);
v_r_550_ = lean_uint32_lor(v___x_548_, v___x_549_);
v___x_551_ = 65536;
v___x_552_ = lean_uint32_dec_le(v___x_551_, v_r_550_);
if (v___x_552_ == 0)
{
return v___x_527_;
}
else
{
uint32_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = 1114111;
v___x_554_ = lean_uint32_dec_le(v_r_550_, v___x_553_);
return v___x_554_;
}
}
}
}
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_x3f_verify_u2084_0interp(lean_interpreter_value* stack)
{
uint8_t v_w_519_ = stack[0].m_num;
uint8_t v_x_520_ = stack[1].m_num;
uint8_t v_y_521_ = stack[2].m_num;
uint8_t v_z_522_ = stack[3].m_num;
uint8_t v_res_555_;
v_res_555_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2084(v_w_519_, v_x_520_, v_y_521_, v_z_522_);
stack->m_num = v_res_555_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f_verify_u2084___boxed(lean_object* v_w_556_, lean_object* v_x_557_, lean_object* v_y_558_, lean_object* v_z_559_){
_start:
{
uint8_t v_w_boxed_560_; uint8_t v_x_boxed_561_; uint8_t v_y_boxed_562_; uint8_t v_z_boxed_563_; uint8_t v_res_564_; lean_object* v_r_565_; 
v_w_boxed_560_ = lean_unbox(v_w_556_);
v_x_boxed_561_ = lean_unbox(v_x_557_);
v_y_boxed_562_ = lean_unbox(v_y_558_);
v_z_boxed_563_ = lean_unbox(v_z_559_);
v_res_564_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2084(v_w_boxed_560_, v_x_boxed_561_, v_y_boxed_562_, v_z_boxed_563_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f(lean_object* v_bytes_566_, lean_object* v_i_567_){
_start:
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_byte_array_size(v_bytes_566_);
v___x_569_ = lean_nat_dec_lt(v_i_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
v___x_570_ = lean_box(0);
return v___x_570_;
}
else
{
uint8_t v___x_571_; uint8_t v___x_572_; uint8_t v___x_573_; uint8_t v___x_574_; uint8_t v___x_575_; 
v___x_571_ = lean_byte_array_fget(v_bytes_566_, v_i_567_);
v___x_572_ = 128;
v___x_573_ = lean_uint8_land(v___x_571_, v___x_572_);
v___x_574_ = 0;
v___x_575_ = lean_uint8_dec_eq(v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
uint8_t v___x_576_; uint8_t v___x_577_; uint8_t v___x_578_; uint8_t v___x_579_; 
v___x_576_ = 224;
v___x_577_ = lean_uint8_land(v___x_571_, v___x_576_);
v___x_578_ = 192;
v___x_579_ = lean_uint8_dec_eq(v___x_577_, v___x_578_);
if (v___x_579_ == 0)
{
uint8_t v___x_580_; uint8_t v___x_581_; uint8_t v___x_582_; 
v___x_580_ = 240;
v___x_581_ = lean_uint8_land(v___x_571_, v___x_580_);
v___x_582_ = lean_uint8_dec_eq(v___x_581_, v___x_576_);
if (v___x_582_ == 0)
{
uint8_t v___x_583_; uint8_t v___x_584_; uint8_t v___x_585_; 
v___x_583_ = 248;
v___x_584_ = lean_uint8_land(v___x_571_, v___x_583_);
v___x_585_ = lean_uint8_dec_eq(v___x_584_, v___x_580_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_box(0);
return v___x_586_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_587_ = lean_unsigned_to_nat(3u);
v___x_588_ = lean_nat_add(v_i_567_, v___x_587_);
v___x_589_ = lean_nat_dec_lt(v___x_588_, v___x_568_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
lean_dec(v___x_588_);
v___x_590_ = lean_box(0);
return v___x_590_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; uint8_t v___x_594_; uint8_t v___x_595_; 
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_nat_add(v_i_567_, v___x_591_);
v___x_593_ = lean_byte_array_fget(v_bytes_566_, v___x_592_);
lean_dec(v___x_592_);
v___x_594_ = lean_uint8_land(v___x_593_, v___x_578_);
v___x_595_ = lean_uint8_dec_eq(v___x_594_, v___x_572_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec(v___x_588_);
v___x_596_ = lean_box(0);
return v___x_596_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; uint8_t v___x_600_; uint8_t v___x_601_; 
v___x_597_ = lean_unsigned_to_nat(2u);
v___x_598_ = lean_nat_add(v_i_567_, v___x_597_);
v___x_599_ = lean_byte_array_fget(v_bytes_566_, v___x_598_);
lean_dec(v___x_598_);
v___x_600_ = lean_uint8_land(v___x_599_, v___x_578_);
v___x_601_ = lean_uint8_dec_eq(v___x_600_, v___x_572_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_dec(v___x_588_);
v___x_602_ = lean_box(0);
return v___x_602_;
}
else
{
uint8_t v___x_603_; uint8_t v___x_604_; uint8_t v___x_605_; 
v___x_603_ = lean_byte_array_fget(v_bytes_566_, v___x_588_);
lean_dec(v___x_588_);
v___x_604_ = lean_uint8_land(v___x_603_, v___x_578_);
v___x_605_ = lean_uint8_dec_eq(v___x_604_, v___x_572_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; 
v___x_606_ = lean_box(0);
return v___x_606_;
}
else
{
uint8_t v___x_607_; uint8_t v_b_u2080_608_; uint8_t v___x_609_; uint8_t v_b_u2081_610_; uint8_t v_b_u2082_611_; uint8_t v_b_u2083_612_; uint32_t v___x_613_; uint32_t v___x_614_; uint32_t v___x_615_; uint32_t v___x_616_; uint32_t v___x_617_; uint32_t v___x_618_; uint32_t v___x_619_; uint32_t v___x_620_; uint32_t v___x_621_; uint32_t v___x_622_; uint32_t v___x_623_; uint32_t v___x_624_; uint32_t v_r_625_; uint32_t v___x_626_; uint8_t v___x_627_; 
v___x_607_ = 7;
v_b_u2080_608_ = lean_uint8_land(v___x_571_, v___x_607_);
v___x_609_ = 63;
v_b_u2081_610_ = lean_uint8_land(v___x_593_, v___x_609_);
v_b_u2082_611_ = lean_uint8_land(v___x_599_, v___x_609_);
v_b_u2083_612_ = lean_uint8_land(v___x_603_, v___x_609_);
v___x_613_ = lean_uint8_to_uint32(v_b_u2080_608_);
v___x_614_ = 18;
v___x_615_ = lean_uint32_shift_left(v___x_613_, v___x_614_);
v___x_616_ = lean_uint8_to_uint32(v_b_u2081_610_);
v___x_617_ = 12;
v___x_618_ = lean_uint32_shift_left(v___x_616_, v___x_617_);
v___x_619_ = lean_uint32_lor(v___x_615_, v___x_618_);
v___x_620_ = lean_uint8_to_uint32(v_b_u2082_611_);
v___x_621_ = 6;
v___x_622_ = lean_uint32_shift_left(v___x_620_, v___x_621_);
v___x_623_ = lean_uint32_lor(v___x_619_, v___x_622_);
v___x_624_ = lean_uint8_to_uint32(v_b_u2083_612_);
v_r_625_ = lean_uint32_lor(v___x_623_, v___x_624_);
v___x_626_ = 65536;
v___x_627_ = lean_uint32_dec_lt(v_r_625_, v___x_626_);
if (v___x_627_ == 0)
{
uint32_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = 1114111;
v___x_629_ = lean_uint32_dec_lt(v___x_628_, v_r_625_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_box_uint32(v_r_625_);
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
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
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_634_ = lean_unsigned_to_nat(2u);
v___x_635_ = lean_nat_add(v_i_567_, v___x_634_);
v___x_636_ = lean_nat_dec_lt(v___x_635_, v___x_568_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
lean_dec(v___x_635_);
v___x_637_ = lean_box(0);
return v___x_637_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; uint8_t v___x_641_; uint8_t v___x_642_; 
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_add(v_i_567_, v___x_638_);
v___x_640_ = lean_byte_array_fget(v_bytes_566_, v___x_639_);
lean_dec(v___x_639_);
v___x_641_ = lean_uint8_land(v___x_640_, v___x_578_);
v___x_642_ = lean_uint8_dec_eq(v___x_641_, v___x_572_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
lean_dec(v___x_635_);
v___x_643_ = lean_box(0);
return v___x_643_;
}
else
{
uint8_t v___x_644_; uint8_t v___x_645_; uint8_t v___x_646_; 
v___x_644_ = lean_byte_array_fget(v_bytes_566_, v___x_635_);
lean_dec(v___x_635_);
v___x_645_ = lean_uint8_land(v___x_644_, v___x_578_);
v___x_646_ = lean_uint8_dec_eq(v___x_645_, v___x_572_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
v___x_647_ = lean_box(0);
return v___x_647_;
}
else
{
uint8_t v___x_648_; uint8_t v_b_u2080_649_; uint8_t v___x_650_; uint8_t v_b_u2081_651_; uint8_t v_b_u2082_652_; uint32_t v___x_653_; uint32_t v___x_654_; uint32_t v___x_655_; uint32_t v___x_656_; uint32_t v___x_657_; uint32_t v___x_658_; uint32_t v___x_659_; uint32_t v___x_660_; uint32_t v_r_661_; uint32_t v___x_662_; uint8_t v___x_663_; 
v___x_648_ = 15;
v_b_u2080_649_ = lean_uint8_land(v___x_571_, v___x_648_);
v___x_650_ = 63;
v_b_u2081_651_ = lean_uint8_land(v___x_640_, v___x_650_);
v_b_u2082_652_ = lean_uint8_land(v___x_644_, v___x_650_);
v___x_653_ = lean_uint8_to_uint32(v_b_u2080_649_);
v___x_654_ = 12;
v___x_655_ = lean_uint32_shift_left(v___x_653_, v___x_654_);
v___x_656_ = lean_uint8_to_uint32(v_b_u2081_651_);
v___x_657_ = 6;
v___x_658_ = lean_uint32_shift_left(v___x_656_, v___x_657_);
v___x_659_ = lean_uint32_lor(v___x_655_, v___x_658_);
v___x_660_ = lean_uint8_to_uint32(v_b_u2082_652_);
v_r_661_ = lean_uint32_lor(v___x_659_, v___x_660_);
v___x_662_ = 2048;
v___x_663_ = lean_uint32_dec_lt(v_r_661_, v___x_662_);
if (v___x_663_ == 0)
{
uint32_t v___x_664_; uint8_t v___x_665_; 
v___x_664_ = 55296;
v___x_665_ = lean_uint32_dec_le(v___x_664_, v_r_661_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_box_uint32(v_r_661_);
v___x_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
return v___x_667_;
}
else
{
uint32_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = 57343;
v___x_669_ = lean_uint32_dec_le(v_r_661_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_box_uint32(v_r_661_);
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
else
{
lean_object* v___x_673_; 
v___x_673_ = lean_box(0);
return v___x_673_;
}
}
}
}
}
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_nat_add(v_i_567_, v___x_674_);
v___x_676_ = lean_nat_dec_lt(v___x_675_, v___x_568_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
lean_dec(v___x_675_);
v___x_677_ = lean_box(0);
return v___x_677_;
}
else
{
uint8_t v___x_678_; uint8_t v___x_679_; uint8_t v___x_680_; 
v___x_678_ = lean_byte_array_fget(v_bytes_566_, v___x_675_);
lean_dec(v___x_675_);
v___x_679_ = lean_uint8_land(v___x_678_, v___x_578_);
v___x_680_ = lean_uint8_dec_eq(v___x_679_, v___x_572_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
v___x_681_ = lean_box(0);
return v___x_681_;
}
else
{
uint8_t v___x_682_; uint8_t v_b_u2080_683_; uint8_t v___x_684_; uint8_t v_b_u2081_685_; uint32_t v___x_686_; uint32_t v___x_687_; uint32_t v___x_688_; uint32_t v___x_689_; uint32_t v_r_690_; uint32_t v___x_691_; uint8_t v___x_692_; 
v___x_682_ = 31;
v_b_u2080_683_ = lean_uint8_land(v___x_571_, v___x_682_);
v___x_684_ = 63;
v_b_u2081_685_ = lean_uint8_land(v___x_678_, v___x_684_);
v___x_686_ = lean_uint8_to_uint32(v_b_u2080_683_);
v___x_687_ = 6;
v___x_688_ = lean_uint32_shift_left(v___x_686_, v___x_687_);
v___x_689_ = lean_uint8_to_uint32(v_b_u2081_685_);
v_r_690_ = lean_uint32_lor(v___x_688_, v___x_689_);
v___x_691_ = 128;
v___x_692_ = lean_uint32_dec_lt(v_r_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_box_uint32(v_r_690_);
v___x_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
else
{
lean_object* v___x_695_; 
v___x_695_ = lean_box(0);
return v___x_695_;
}
}
}
}
}
else
{
uint32_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = lean_uint8_to_uint32(v___x_571_);
v___x_697_ = lean_box_uint32(v___x_696_);
v___x_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar_x3f___boxed(lean_object* v_bytes_699_, lean_object* v_i_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_ByteArray_utf8DecodeChar_x3f(v_bytes_699_, v_i_700_);
lean_dec(v_i_700_);
lean_dec_ref(v_bytes_699_);
return v_res_701_;
}
}
uint8_t l_ByteArray_validateUTF8At(lean_object* v_bytes_702_, lean_object* v_i_703_){
_start:
{
lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_704_ = lean_byte_array_size(v_bytes_702_);
v___x_705_ = lean_nat_dec_lt(v_i_703_, v___x_704_);
if (v___x_705_ == 0)
{
return v___x_705_;
}
else
{
uint8_t v___x_706_; uint8_t v___x_707_; uint8_t v___x_708_; uint8_t v___x_709_; uint8_t v___x_710_; 
v___x_706_ = lean_byte_array_fget(v_bytes_702_, v_i_703_);
v___x_707_ = 128;
v___x_708_ = lean_uint8_land(v___x_706_, v___x_707_);
v___x_709_ = 0;
v___x_710_ = lean_uint8_dec_eq(v___x_708_, v___x_709_);
if (v___x_710_ == 0)
{
uint8_t v___x_711_; uint8_t v___x_712_; uint8_t v___x_713_; uint8_t v___x_714_; 
v___x_711_ = 224;
v___x_712_ = lean_uint8_land(v___x_706_, v___x_711_);
v___x_713_ = 192;
v___x_714_ = lean_uint8_dec_eq(v___x_712_, v___x_713_);
if (v___x_714_ == 0)
{
uint8_t v___x_715_; uint8_t v___x_716_; uint8_t v___x_717_; 
v___x_715_ = 240;
v___x_716_ = lean_uint8_land(v___x_706_, v___x_715_);
v___x_717_ = lean_uint8_dec_eq(v___x_716_, v___x_711_);
if (v___x_717_ == 0)
{
uint8_t v___x_718_; uint8_t v___x_719_; uint8_t v___x_720_; 
v___x_718_ = 248;
v___x_719_ = lean_uint8_land(v___x_706_, v___x_718_);
v___x_720_ = lean_uint8_dec_eq(v___x_719_, v___x_715_);
if (v___x_720_ == 0)
{
return v___x_720_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_721_ = lean_unsigned_to_nat(3u);
v___x_722_ = lean_nat_add(v_i_703_, v___x_721_);
v___x_723_ = lean_nat_dec_lt(v___x_722_, v___x_704_);
if (v___x_723_ == 0)
{
lean_dec(v___x_722_);
return v___x_723_;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; uint8_t v___x_727_; uint8_t v___x_728_; 
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_add(v_i_703_, v___x_724_);
v___x_726_ = lean_byte_array_fget(v_bytes_702_, v___x_725_);
lean_dec(v___x_725_);
v___x_727_ = lean_uint8_land(v___x_726_, v___x_713_);
v___x_728_ = lean_uint8_dec_eq(v___x_727_, v___x_707_);
if (v___x_728_ == 0)
{
lean_dec(v___x_722_);
return v___x_728_;
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; uint8_t v___x_732_; uint8_t v___x_733_; 
v___x_729_ = lean_unsigned_to_nat(2u);
v___x_730_ = lean_nat_add(v_i_703_, v___x_729_);
v___x_731_ = lean_byte_array_fget(v_bytes_702_, v___x_730_);
lean_dec(v___x_730_);
v___x_732_ = lean_uint8_land(v___x_731_, v___x_713_);
v___x_733_ = lean_uint8_dec_eq(v___x_732_, v___x_707_);
if (v___x_733_ == 0)
{
lean_dec(v___x_722_);
return v___x_717_;
}
else
{
uint8_t v___x_734_; uint8_t v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_byte_array_fget(v_bytes_702_, v___x_722_);
lean_dec(v___x_722_);
v___x_735_ = lean_uint8_land(v___x_734_, v___x_713_);
v___x_736_ = lean_uint8_dec_eq(v___x_735_, v___x_707_);
if (v___x_736_ == 0)
{
return v___x_717_;
}
else
{
uint8_t v___x_737_; uint8_t v_b_u2080_738_; uint8_t v___x_739_; uint8_t v_b_u2081_740_; uint8_t v_b_u2082_741_; uint8_t v_b_u2083_742_; uint32_t v___x_743_; uint32_t v___x_744_; uint32_t v___x_745_; uint32_t v___x_746_; uint32_t v___x_747_; uint32_t v___x_748_; uint32_t v___x_749_; uint32_t v___x_750_; uint32_t v___x_751_; uint32_t v___x_752_; uint32_t v___x_753_; uint32_t v___x_754_; uint32_t v_r_755_; uint32_t v___x_756_; uint8_t v___x_757_; 
v___x_737_ = 7;
v_b_u2080_738_ = lean_uint8_land(v___x_706_, v___x_737_);
v___x_739_ = 63;
v_b_u2081_740_ = lean_uint8_land(v___x_726_, v___x_739_);
v_b_u2082_741_ = lean_uint8_land(v___x_731_, v___x_739_);
v_b_u2083_742_ = lean_uint8_land(v___x_734_, v___x_739_);
v___x_743_ = lean_uint8_to_uint32(v_b_u2080_738_);
v___x_744_ = 18;
v___x_745_ = lean_uint32_shift_left(v___x_743_, v___x_744_);
v___x_746_ = lean_uint8_to_uint32(v_b_u2081_740_);
v___x_747_ = 12;
v___x_748_ = lean_uint32_shift_left(v___x_746_, v___x_747_);
v___x_749_ = lean_uint32_lor(v___x_745_, v___x_748_);
v___x_750_ = lean_uint8_to_uint32(v_b_u2082_741_);
v___x_751_ = 6;
v___x_752_ = lean_uint32_shift_left(v___x_750_, v___x_751_);
v___x_753_ = lean_uint32_lor(v___x_749_, v___x_752_);
v___x_754_ = lean_uint8_to_uint32(v_b_u2083_742_);
v_r_755_ = lean_uint32_lor(v___x_753_, v___x_754_);
v___x_756_ = 65536;
v___x_757_ = lean_uint32_dec_le(v___x_756_, v_r_755_);
if (v___x_757_ == 0)
{
return v___x_717_;
}
else
{
uint32_t v___x_758_; uint8_t v___x_759_; 
v___x_758_ = 1114111;
v___x_759_ = lean_uint32_dec_le(v_r_755_, v___x_758_);
return v___x_759_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_760_ = lean_unsigned_to_nat(2u);
v___x_761_ = lean_nat_add(v_i_703_, v___x_760_);
v___x_762_ = lean_nat_dec_lt(v___x_761_, v___x_704_);
if (v___x_762_ == 0)
{
lean_dec(v___x_761_);
return v___x_762_;
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; uint8_t v___x_766_; uint8_t v___x_767_; 
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_add(v_i_703_, v___x_763_);
v___x_765_ = lean_byte_array_fget(v_bytes_702_, v___x_764_);
lean_dec(v___x_764_);
v___x_766_ = lean_uint8_land(v___x_765_, v___x_713_);
v___x_767_ = lean_uint8_dec_eq(v___x_766_, v___x_707_);
if (v___x_767_ == 0)
{
lean_dec(v___x_761_);
return v___x_767_;
}
else
{
uint8_t v___x_768_; uint8_t v___x_769_; uint8_t v___x_770_; 
v___x_768_ = lean_byte_array_fget(v_bytes_702_, v___x_761_);
lean_dec(v___x_761_);
v___x_769_ = lean_uint8_land(v___x_768_, v___x_713_);
v___x_770_ = lean_uint8_dec_eq(v___x_769_, v___x_707_);
if (v___x_770_ == 0)
{
return v___x_714_;
}
else
{
uint8_t v___x_771_; uint8_t v_b_u2080_772_; uint8_t v___x_773_; uint8_t v_b_u2081_774_; uint8_t v_b_u2082_775_; uint32_t v___x_776_; uint32_t v___x_777_; uint32_t v___x_778_; uint32_t v___x_779_; uint32_t v___x_780_; uint32_t v___x_781_; uint32_t v___x_782_; uint32_t v___x_783_; uint32_t v_r_784_; uint32_t v___x_785_; uint8_t v___x_786_; 
v___x_771_ = 15;
v_b_u2080_772_ = lean_uint8_land(v___x_706_, v___x_771_);
v___x_773_ = 63;
v_b_u2081_774_ = lean_uint8_land(v___x_765_, v___x_773_);
v_b_u2082_775_ = lean_uint8_land(v___x_768_, v___x_773_);
v___x_776_ = lean_uint8_to_uint32(v_b_u2080_772_);
v___x_777_ = 12;
v___x_778_ = lean_uint32_shift_left(v___x_776_, v___x_777_);
v___x_779_ = lean_uint8_to_uint32(v_b_u2081_774_);
v___x_780_ = 6;
v___x_781_ = lean_uint32_shift_left(v___x_779_, v___x_780_);
v___x_782_ = lean_uint32_lor(v___x_778_, v___x_781_);
v___x_783_ = lean_uint8_to_uint32(v_b_u2082_775_);
v_r_784_ = lean_uint32_lor(v___x_782_, v___x_783_);
v___x_785_ = 2048;
v___x_786_ = lean_uint32_dec_le(v___x_785_, v_r_784_);
if (v___x_786_ == 0)
{
return v___x_714_;
}
else
{
uint32_t v___x_787_; uint8_t v___x_788_; 
v___x_787_ = 55296;
v___x_788_ = lean_uint32_dec_lt(v_r_784_, v___x_787_);
if (v___x_788_ == 0)
{
uint32_t v___x_789_; uint8_t v___x_790_; 
v___x_789_ = 57343;
v___x_790_ = lean_uint32_dec_lt(v___x_789_, v_r_784_);
return v___x_790_;
}
else
{
return v___x_788_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_791_ = lean_unsigned_to_nat(1u);
v___x_792_ = lean_nat_add(v_i_703_, v___x_791_);
v___x_793_ = lean_nat_dec_lt(v___x_792_, v___x_704_);
if (v___x_793_ == 0)
{
lean_dec(v___x_792_);
return v___x_793_;
}
else
{
uint8_t v___x_794_; uint8_t v___x_795_; uint8_t v___x_796_; 
v___x_794_ = lean_byte_array_fget(v_bytes_702_, v___x_792_);
lean_dec(v___x_792_);
v___x_795_ = lean_uint8_land(v___x_794_, v___x_713_);
v___x_796_ = lean_uint8_dec_eq(v___x_795_, v___x_707_);
if (v___x_796_ == 0)
{
return v___x_796_;
}
else
{
uint8_t v___x_797_; uint8_t v_b_u2080_798_; uint8_t v___x_799_; uint8_t v_b_u2081_800_; uint32_t v___x_801_; uint32_t v___x_802_; uint32_t v___x_803_; uint32_t v___x_804_; uint32_t v_r_805_; uint32_t v___x_806_; uint8_t v___x_807_; 
v___x_797_ = 31;
v_b_u2080_798_ = lean_uint8_land(v___x_706_, v___x_797_);
v___x_799_ = 63;
v_b_u2081_800_ = lean_uint8_land(v___x_794_, v___x_799_);
v___x_801_ = lean_uint8_to_uint32(v_b_u2080_798_);
v___x_802_ = 6;
v___x_803_ = lean_uint32_shift_left(v___x_801_, v___x_802_);
v___x_804_ = lean_uint8_to_uint32(v_b_u2081_800_);
v_r_805_ = lean_uint32_lor(v___x_803_, v___x_804_);
v___x_806_ = 128;
v___x_807_ = lean_uint32_dec_le(v___x_806_, v_r_805_);
return v___x_807_;
}
}
}
}
else
{
return v___x_705_;
}
}
}
}
LEAN_EXPORT void l_ByteArray_validateUTF8At_0interp(lean_interpreter_value* stack)
{
lean_object* v_bytes_702_ = stack[0].m_obj;
lean_object* v_i_703_ = stack[1].m_obj;
uint8_t v_res_808_;
v_res_808_ = l_ByteArray_validateUTF8At(v_bytes_702_, v_i_703_);
stack->m_num = v_res_808_;
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8At___boxed(lean_object* v_bytes_809_, lean_object* v_i_810_){
_start:
{
uint8_t v_res_811_; lean_object* v_r_812_; 
v_res_811_ = l_ByteArray_validateUTF8At(v_bytes_809_, v_i_810_);
lean_dec(v_i_810_);
lean_dec_ref(v_bytes_809_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t v_x_813_, lean_object* v_h__1_814_, lean_object* v_h__2_815_, lean_object* v_h__3_816_, lean_object* v_h__4_817_, lean_object* v_h__5_818_){
_start:
{
switch(v_x_813_)
{
case 0:
{
lean_object* v___x_819_; 
lean_dec(v_h__5_818_);
lean_dec(v_h__4_817_);
lean_dec(v_h__3_816_);
lean_dec(v_h__2_815_);
v___x_819_ = lean_apply_1(v_h__1_814_, lean_box(0));
return v___x_819_;
}
case 1:
{
lean_object* v___x_820_; 
lean_dec(v_h__5_818_);
lean_dec(v_h__4_817_);
lean_dec(v_h__3_816_);
lean_dec(v_h__1_814_);
v___x_820_ = lean_apply_1(v_h__2_815_, lean_box(0));
return v___x_820_;
}
case 2:
{
lean_object* v___x_821_; 
lean_dec(v_h__5_818_);
lean_dec(v_h__4_817_);
lean_dec(v_h__2_815_);
lean_dec(v_h__1_814_);
v___x_821_ = lean_apply_1(v_h__3_816_, lean_box(0));
return v___x_821_;
}
case 3:
{
lean_object* v___x_822_; 
lean_dec(v_h__5_818_);
lean_dec(v_h__3_816_);
lean_dec(v_h__2_815_);
lean_dec(v_h__1_814_);
v___x_822_ = lean_apply_1(v_h__4_817_, lean_box(0));
return v___x_822_;
}
default: 
{
lean_object* v___x_823_; 
lean_dec(v_h__4_817_);
lean_dec(v_h__3_816_);
lean_dec(v_h__2_815_);
lean_dec(v_h__1_814_);
v___x_823_ = lean_apply_1(v_h__5_818_, lean_box(0));
return v___x_823_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_813_ = stack[0].m_num;
lean_object* v_h__1_814_ = stack[1].m_obj;
lean_object* v_h__2_815_ = stack[2].m_obj;
lean_object* v_h__3_816_ = stack[3].m_obj;
lean_object* v_h__4_817_ = stack[4].m_obj;
lean_object* v_h__5_818_ = stack[5].m_obj;
lean_object* v_res_824_;
v_res_824_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(v_x_813_, v_h__1_814_, v_h__2_815_, v_h__3_816_, v_h__4_817_, v_h__5_818_);
stack->m_obj
 = v_res_824_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_825_, lean_object* v_h__1_826_, lean_object* v_h__2_827_, lean_object* v_h__3_828_, lean_object* v_h__4_829_, lean_object* v_h__5_830_){
_start:
{
uint8_t v_x_47__boxed_831_; lean_object* v_res_832_; 
v_x_47__boxed_831_ = lean_unbox(v_x_825_);
v_res_832_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(v_x_47__boxed_831_, v_h__1_826_, v_h__2_827_, v_h__3_828_, v_h__4_829_, v_h__5_830_);
return v_res_832_;
}
}
lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object* v_motive_833_, uint8_t v_x_834_, lean_object* v_h__1_835_, lean_object* v_h__2_836_, lean_object* v_h__3_837_, lean_object* v_h__4_838_, lean_object* v_h__5_839_){
_start:
{
switch(v_x_834_)
{
case 0:
{
lean_object* v___x_840_; 
lean_dec(v_h__5_839_);
lean_dec(v_h__4_838_);
lean_dec(v_h__3_837_);
lean_dec(v_h__2_836_);
v___x_840_ = lean_apply_1(v_h__1_835_, lean_box(0));
return v___x_840_;
}
case 1:
{
lean_object* v___x_841_; 
lean_dec(v_h__5_839_);
lean_dec(v_h__4_838_);
lean_dec(v_h__3_837_);
lean_dec(v_h__1_835_);
v___x_841_ = lean_apply_1(v_h__2_836_, lean_box(0));
return v___x_841_;
}
case 2:
{
lean_object* v___x_842_; 
lean_dec(v_h__5_839_);
lean_dec(v_h__4_838_);
lean_dec(v_h__2_836_);
lean_dec(v_h__1_835_);
v___x_842_ = lean_apply_1(v_h__3_837_, lean_box(0));
return v___x_842_;
}
case 3:
{
lean_object* v___x_843_; 
lean_dec(v_h__5_839_);
lean_dec(v_h__3_837_);
lean_dec(v_h__2_836_);
lean_dec(v_h__1_835_);
v___x_843_ = lean_apply_1(v_h__4_838_, lean_box(0));
return v___x_843_;
}
default: 
{
lean_object* v___x_844_; 
lean_dec(v_h__4_838_);
lean_dec(v_h__3_837_);
lean_dec(v_h__2_836_);
lean_dec(v_h__1_835_);
v___x_844_ = lean_apply_1(v_h__5_839_, lean_box(0));
return v___x_844_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_834_ = stack[1].m_num;
lean_object* v_h__1_835_ = stack[2].m_obj;
lean_object* v_h__2_836_ = stack[3].m_obj;
lean_object* v_h__3_837_ = stack[4].m_obj;
lean_object* v_h__4_838_ = stack[5].m_obj;
lean_object* v_h__5_839_ = stack[6].m_obj;
lean_object* v_res_845_;
v_res_845_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_box(0), v_x_834_, v_h__1_835_, v_h__2_836_, v_h__3_837_, v_h__4_838_, v_h__5_839_);
stack->m_obj
 = v_res_845_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object* v_motive_846_, lean_object* v_x_847_, lean_object* v_h__1_848_, lean_object* v_h__2_849_, lean_object* v_h__3_850_, lean_object* v_h__4_851_, lean_object* v_h__5_852_){
_start:
{
uint8_t v_x_67__boxed_853_; lean_object* v_res_854_; 
v_x_67__boxed_853_ = lean_unbox(v_x_847_);
v_res_854_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(v_motive_846_, v_x_67__boxed_853_, v_h__1_848_, v_h__2_849_, v_h__3_850_, v_h__4_851_, v_h__5_852_);
return v_res_854_;
}
}
uint32_t l_ByteArray_utf8DecodeChar___redArg(lean_object* v_bytes_855_, lean_object* v_i_856_){
_start:
{
lean_object* v___x_857_; uint8_t v___x_858_; uint8_t v___x_859_; uint8_t v___x_860_; uint8_t v___x_861_; uint8_t v___x_862_; uint8_t v___x_863_; 
v___x_857_ = lean_byte_array_size(v_bytes_855_);
v___x_858_ = lean_nat_dec_lt(v_i_856_, v___x_857_);
v___x_859_ = lean_byte_array_fget(v_bytes_855_, v_i_856_);
v___x_860_ = 128;
v___x_861_ = lean_uint8_land(v___x_859_, v___x_860_);
v___x_862_ = 0;
v___x_863_ = lean_uint8_dec_eq(v___x_861_, v___x_862_);
if (v___x_863_ == 0)
{
uint8_t v___x_864_; uint8_t v___x_865_; uint8_t v___x_866_; uint8_t v___x_867_; 
v___x_864_ = 224;
v___x_865_ = lean_uint8_land(v___x_859_, v___x_864_);
v___x_866_ = 192;
v___x_867_ = lean_uint8_dec_eq(v___x_865_, v___x_866_);
if (v___x_867_ == 0)
{
uint8_t v___x_868_; uint8_t v___x_869_; uint8_t v___x_870_; 
v___x_868_ = 240;
v___x_869_ = lean_uint8_land(v___x_859_, v___x_868_);
v___x_870_ = lean_uint8_dec_eq(v___x_869_, v___x_864_);
if (v___x_870_ == 0)
{
uint8_t v___x_871_; uint8_t v___x_872_; uint8_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; uint8_t v___x_880_; uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; uint8_t v___x_885_; uint8_t v___x_886_; uint8_t v___x_887_; uint8_t v___x_888_; uint8_t v___x_889_; uint8_t v___x_890_; uint8_t v_b_u2080_891_; uint8_t v___x_892_; uint8_t v_b_u2081_893_; uint8_t v_b_u2082_894_; uint8_t v_b_u2083_895_; uint32_t v___x_896_; uint32_t v___x_897_; uint32_t v___x_898_; uint32_t v___x_899_; uint32_t v___x_900_; uint32_t v___x_901_; uint32_t v___x_902_; uint32_t v___x_903_; uint32_t v___x_904_; uint32_t v___x_905_; uint32_t v___x_906_; uint32_t v___x_907_; uint32_t v_r_908_; uint32_t v___x_909_; uint8_t v___x_910_; uint32_t v___x_911_; uint8_t v___x_912_; 
v___x_871_ = 248;
v___x_872_ = lean_uint8_land(v___x_859_, v___x_871_);
v___x_873_ = lean_uint8_dec_eq(v___x_872_, v___x_868_);
v___x_874_ = lean_unsigned_to_nat(3u);
v___x_875_ = lean_nat_add(v_i_856_, v___x_874_);
v___x_876_ = lean_nat_dec_lt(v___x_875_, v___x_857_);
v___x_877_ = lean_unsigned_to_nat(1u);
v___x_878_ = lean_nat_add(v_i_856_, v___x_877_);
v___x_879_ = lean_byte_array_fget(v_bytes_855_, v___x_878_);
lean_dec(v___x_878_);
v___x_880_ = lean_uint8_land(v___x_879_, v___x_866_);
v___x_881_ = lean_uint8_dec_eq(v___x_880_, v___x_860_);
v___x_882_ = lean_unsigned_to_nat(2u);
v___x_883_ = lean_nat_add(v_i_856_, v___x_882_);
v___x_884_ = lean_byte_array_fget(v_bytes_855_, v___x_883_);
lean_dec(v___x_883_);
v___x_885_ = lean_uint8_land(v___x_884_, v___x_866_);
v___x_886_ = lean_uint8_dec_eq(v___x_885_, v___x_860_);
v___x_887_ = lean_byte_array_fget(v_bytes_855_, v___x_875_);
lean_dec(v___x_875_);
v___x_888_ = lean_uint8_land(v___x_887_, v___x_866_);
v___x_889_ = lean_uint8_dec_eq(v___x_888_, v___x_860_);
v___x_890_ = 7;
v_b_u2080_891_ = lean_uint8_land(v___x_859_, v___x_890_);
v___x_892_ = 63;
v_b_u2081_893_ = lean_uint8_land(v___x_879_, v___x_892_);
v_b_u2082_894_ = lean_uint8_land(v___x_884_, v___x_892_);
v_b_u2083_895_ = lean_uint8_land(v___x_887_, v___x_892_);
v___x_896_ = lean_uint8_to_uint32(v_b_u2080_891_);
v___x_897_ = 18;
v___x_898_ = lean_uint32_shift_left(v___x_896_, v___x_897_);
v___x_899_ = lean_uint8_to_uint32(v_b_u2081_893_);
v___x_900_ = 12;
v___x_901_ = lean_uint32_shift_left(v___x_899_, v___x_900_);
v___x_902_ = lean_uint32_lor(v___x_898_, v___x_901_);
v___x_903_ = lean_uint8_to_uint32(v_b_u2082_894_);
v___x_904_ = 6;
v___x_905_ = lean_uint32_shift_left(v___x_903_, v___x_904_);
v___x_906_ = lean_uint32_lor(v___x_902_, v___x_905_);
v___x_907_ = lean_uint8_to_uint32(v_b_u2083_895_);
v_r_908_ = lean_uint32_lor(v___x_906_, v___x_907_);
v___x_909_ = 65536;
v___x_910_ = lean_uint32_dec_lt(v_r_908_, v___x_909_);
v___x_911_ = 1114111;
v___x_912_ = lean_uint32_dec_lt(v___x_911_, v_r_908_);
return v_r_908_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; uint8_t v___x_919_; uint8_t v___x_920_; uint8_t v___x_921_; uint8_t v___x_922_; uint8_t v___x_923_; uint8_t v___x_924_; uint8_t v_b_u2080_925_; uint8_t v___x_926_; uint8_t v_b_u2081_927_; uint8_t v_b_u2082_928_; uint32_t v___x_929_; uint32_t v___x_930_; uint32_t v___x_931_; uint32_t v___x_932_; uint32_t v___x_933_; uint32_t v___x_934_; uint32_t v___x_935_; uint32_t v___x_936_; uint32_t v_r_937_; uint32_t v___x_938_; uint8_t v___x_939_; uint32_t v___x_940_; uint8_t v___x_941_; 
v___x_913_ = lean_unsigned_to_nat(2u);
v___x_914_ = lean_nat_add(v_i_856_, v___x_913_);
v___x_915_ = lean_nat_dec_lt(v___x_914_, v___x_857_);
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_nat_add(v_i_856_, v___x_916_);
v___x_918_ = lean_byte_array_fget(v_bytes_855_, v___x_917_);
lean_dec(v___x_917_);
v___x_919_ = lean_uint8_land(v___x_918_, v___x_866_);
v___x_920_ = lean_uint8_dec_eq(v___x_919_, v___x_860_);
v___x_921_ = lean_byte_array_fget(v_bytes_855_, v___x_914_);
lean_dec(v___x_914_);
v___x_922_ = lean_uint8_land(v___x_921_, v___x_866_);
v___x_923_ = lean_uint8_dec_eq(v___x_922_, v___x_860_);
v___x_924_ = 15;
v_b_u2080_925_ = lean_uint8_land(v___x_859_, v___x_924_);
v___x_926_ = 63;
v_b_u2081_927_ = lean_uint8_land(v___x_918_, v___x_926_);
v_b_u2082_928_ = lean_uint8_land(v___x_921_, v___x_926_);
v___x_929_ = lean_uint8_to_uint32(v_b_u2080_925_);
v___x_930_ = 12;
v___x_931_ = lean_uint32_shift_left(v___x_929_, v___x_930_);
v___x_932_ = lean_uint8_to_uint32(v_b_u2081_927_);
v___x_933_ = 6;
v___x_934_ = lean_uint32_shift_left(v___x_932_, v___x_933_);
v___x_935_ = lean_uint32_lor(v___x_931_, v___x_934_);
v___x_936_ = lean_uint8_to_uint32(v_b_u2082_928_);
v_r_937_ = lean_uint32_lor(v___x_935_, v___x_936_);
v___x_938_ = 2048;
v___x_939_ = lean_uint32_dec_lt(v_r_937_, v___x_938_);
v___x_940_ = 55296;
v___x_941_ = lean_uint32_dec_le(v___x_940_, v_r_937_);
if (v___x_941_ == 0)
{
return v_r_937_;
}
else
{
uint32_t v___x_942_; uint8_t v___x_943_; 
v___x_942_ = 57343;
v___x_943_ = lean_uint32_dec_le(v_r_937_, v___x_942_);
return v_r_937_;
}
}
}
else
{
lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; uint8_t v___x_947_; uint8_t v___x_948_; uint8_t v___x_949_; uint8_t v___x_950_; uint8_t v_b_u2080_951_; uint8_t v___x_952_; uint8_t v_b_u2081_953_; uint32_t v___x_954_; uint32_t v___x_955_; uint32_t v___x_956_; uint32_t v___x_957_; uint32_t v_r_958_; uint32_t v___x_959_; uint8_t v___x_960_; 
v___x_944_ = lean_unsigned_to_nat(1u);
v___x_945_ = lean_nat_add(v_i_856_, v___x_944_);
v___x_946_ = lean_nat_dec_lt(v___x_945_, v___x_857_);
v___x_947_ = lean_byte_array_fget(v_bytes_855_, v___x_945_);
lean_dec(v___x_945_);
v___x_948_ = lean_uint8_land(v___x_947_, v___x_866_);
v___x_949_ = lean_uint8_dec_eq(v___x_948_, v___x_860_);
v___x_950_ = 31;
v_b_u2080_951_ = lean_uint8_land(v___x_859_, v___x_950_);
v___x_952_ = 63;
v_b_u2081_953_ = lean_uint8_land(v___x_947_, v___x_952_);
v___x_954_ = lean_uint8_to_uint32(v_b_u2080_951_);
v___x_955_ = 6;
v___x_956_ = lean_uint32_shift_left(v___x_954_, v___x_955_);
v___x_957_ = lean_uint8_to_uint32(v_b_u2081_953_);
v_r_958_ = lean_uint32_lor(v___x_956_, v___x_957_);
v___x_959_ = 128;
v___x_960_ = lean_uint32_dec_lt(v_r_958_, v___x_959_);
return v_r_958_;
}
}
else
{
uint32_t v___x_961_; 
v___x_961_ = lean_uint8_to_uint32(v___x_859_);
return v___x_961_;
}
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_bytes_855_ = stack[0].m_obj;
lean_object* v_i_856_ = stack[1].m_obj;
uint32_t v_res_962_;
v_res_962_ = l_ByteArray_utf8DecodeChar___redArg(v_bytes_855_, v_i_856_);
stack->m_num = v_res_962_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___redArg___boxed(lean_object* v_bytes_963_, lean_object* v_i_964_){
_start:
{
uint32_t v_res_965_; lean_object* v_r_966_; 
v_res_965_ = l_ByteArray_utf8DecodeChar___redArg(v_bytes_963_, v_i_964_);
lean_dec(v_i_964_);
lean_dec_ref(v_bytes_963_);
v_r_966_ = lean_box_uint32(v_res_965_);
return v_r_966_;
}
}
uint32_t l_ByteArray_utf8DecodeChar(lean_object* v_bytes_967_, lean_object* v_i_968_, lean_object* v_h_969_){
_start:
{
lean_object* v___x_970_; uint8_t v___x_971_; uint8_t v___x_972_; uint8_t v___x_973_; uint8_t v___x_974_; uint8_t v___x_975_; uint8_t v___x_976_; 
v___x_970_ = lean_byte_array_size(v_bytes_967_);
v___x_971_ = lean_nat_dec_lt(v_i_968_, v___x_970_);
v___x_972_ = lean_byte_array_fget(v_bytes_967_, v_i_968_);
v___x_973_ = 128;
v___x_974_ = lean_uint8_land(v___x_972_, v___x_973_);
v___x_975_ = 0;
v___x_976_ = lean_uint8_dec_eq(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
uint8_t v___x_977_; uint8_t v___x_978_; uint8_t v___x_979_; uint8_t v___x_980_; 
v___x_977_ = 224;
v___x_978_ = lean_uint8_land(v___x_972_, v___x_977_);
v___x_979_ = 192;
v___x_980_ = lean_uint8_dec_eq(v___x_978_, v___x_979_);
if (v___x_980_ == 0)
{
uint8_t v___x_981_; uint8_t v___x_982_; uint8_t v___x_983_; 
v___x_981_ = 240;
v___x_982_ = lean_uint8_land(v___x_972_, v___x_981_);
v___x_983_ = lean_uint8_dec_eq(v___x_982_, v___x_977_);
if (v___x_983_ == 0)
{
uint8_t v___x_984_; uint8_t v___x_985_; uint8_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; uint8_t v___x_993_; uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; uint8_t v___x_998_; uint8_t v___x_999_; uint8_t v___x_1000_; uint8_t v___x_1001_; uint8_t v___x_1002_; uint8_t v___x_1003_; uint8_t v_b_u2080_1004_; uint8_t v___x_1005_; uint8_t v_b_u2081_1006_; uint8_t v_b_u2082_1007_; uint8_t v_b_u2083_1008_; uint32_t v___x_1009_; uint32_t v___x_1010_; uint32_t v___x_1011_; uint32_t v___x_1012_; uint32_t v___x_1013_; uint32_t v___x_1014_; uint32_t v___x_1015_; uint32_t v___x_1016_; uint32_t v___x_1017_; uint32_t v___x_1018_; uint32_t v___x_1019_; uint32_t v___x_1020_; uint32_t v_r_1021_; uint32_t v___x_1022_; uint8_t v___x_1023_; uint32_t v___x_1024_; uint8_t v___x_1025_; 
v___x_984_ = 248;
v___x_985_ = lean_uint8_land(v___x_972_, v___x_984_);
v___x_986_ = lean_uint8_dec_eq(v___x_985_, v___x_981_);
v___x_987_ = lean_unsigned_to_nat(3u);
v___x_988_ = lean_nat_add(v_i_968_, v___x_987_);
v___x_989_ = lean_nat_dec_lt(v___x_988_, v___x_970_);
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_add(v_i_968_, v___x_990_);
v___x_992_ = lean_byte_array_fget(v_bytes_967_, v___x_991_);
lean_dec(v___x_991_);
v___x_993_ = lean_uint8_land(v___x_992_, v___x_979_);
v___x_994_ = lean_uint8_dec_eq(v___x_993_, v___x_973_);
v___x_995_ = lean_unsigned_to_nat(2u);
v___x_996_ = lean_nat_add(v_i_968_, v___x_995_);
v___x_997_ = lean_byte_array_fget(v_bytes_967_, v___x_996_);
lean_dec(v___x_996_);
v___x_998_ = lean_uint8_land(v___x_997_, v___x_979_);
v___x_999_ = lean_uint8_dec_eq(v___x_998_, v___x_973_);
v___x_1000_ = lean_byte_array_fget(v_bytes_967_, v___x_988_);
lean_dec(v___x_988_);
v___x_1001_ = lean_uint8_land(v___x_1000_, v___x_979_);
v___x_1002_ = lean_uint8_dec_eq(v___x_1001_, v___x_973_);
v___x_1003_ = 7;
v_b_u2080_1004_ = lean_uint8_land(v___x_972_, v___x_1003_);
v___x_1005_ = 63;
v_b_u2081_1006_ = lean_uint8_land(v___x_992_, v___x_1005_);
v_b_u2082_1007_ = lean_uint8_land(v___x_997_, v___x_1005_);
v_b_u2083_1008_ = lean_uint8_land(v___x_1000_, v___x_1005_);
v___x_1009_ = lean_uint8_to_uint32(v_b_u2080_1004_);
v___x_1010_ = 18;
v___x_1011_ = lean_uint32_shift_left(v___x_1009_, v___x_1010_);
v___x_1012_ = lean_uint8_to_uint32(v_b_u2081_1006_);
v___x_1013_ = 12;
v___x_1014_ = lean_uint32_shift_left(v___x_1012_, v___x_1013_);
v___x_1015_ = lean_uint32_lor(v___x_1011_, v___x_1014_);
v___x_1016_ = lean_uint8_to_uint32(v_b_u2082_1007_);
v___x_1017_ = 6;
v___x_1018_ = lean_uint32_shift_left(v___x_1016_, v___x_1017_);
v___x_1019_ = lean_uint32_lor(v___x_1015_, v___x_1018_);
v___x_1020_ = lean_uint8_to_uint32(v_b_u2083_1008_);
v_r_1021_ = lean_uint32_lor(v___x_1019_, v___x_1020_);
v___x_1022_ = 65536;
v___x_1023_ = lean_uint32_dec_lt(v_r_1021_, v___x_1022_);
v___x_1024_ = 1114111;
v___x_1025_ = lean_uint32_dec_lt(v___x_1024_, v_r_1021_);
return v_r_1021_;
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; uint8_t v___x_1032_; uint8_t v___x_1033_; uint8_t v___x_1034_; uint8_t v___x_1035_; uint8_t v___x_1036_; uint8_t v___x_1037_; uint8_t v_b_u2080_1038_; uint8_t v___x_1039_; uint8_t v_b_u2081_1040_; uint8_t v_b_u2082_1041_; uint32_t v___x_1042_; uint32_t v___x_1043_; uint32_t v___x_1044_; uint32_t v___x_1045_; uint32_t v___x_1046_; uint32_t v___x_1047_; uint32_t v___x_1048_; uint32_t v___x_1049_; uint32_t v_r_1050_; uint32_t v___x_1051_; uint8_t v___x_1052_; uint32_t v___x_1053_; uint8_t v___x_1054_; 
v___x_1026_ = lean_unsigned_to_nat(2u);
v___x_1027_ = lean_nat_add(v_i_968_, v___x_1026_);
v___x_1028_ = lean_nat_dec_lt(v___x_1027_, v___x_970_);
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_nat_add(v_i_968_, v___x_1029_);
v___x_1031_ = lean_byte_array_fget(v_bytes_967_, v___x_1030_);
lean_dec(v___x_1030_);
v___x_1032_ = lean_uint8_land(v___x_1031_, v___x_979_);
v___x_1033_ = lean_uint8_dec_eq(v___x_1032_, v___x_973_);
v___x_1034_ = lean_byte_array_fget(v_bytes_967_, v___x_1027_);
lean_dec(v___x_1027_);
v___x_1035_ = lean_uint8_land(v___x_1034_, v___x_979_);
v___x_1036_ = lean_uint8_dec_eq(v___x_1035_, v___x_973_);
v___x_1037_ = 15;
v_b_u2080_1038_ = lean_uint8_land(v___x_972_, v___x_1037_);
v___x_1039_ = 63;
v_b_u2081_1040_ = lean_uint8_land(v___x_1031_, v___x_1039_);
v_b_u2082_1041_ = lean_uint8_land(v___x_1034_, v___x_1039_);
v___x_1042_ = lean_uint8_to_uint32(v_b_u2080_1038_);
v___x_1043_ = 12;
v___x_1044_ = lean_uint32_shift_left(v___x_1042_, v___x_1043_);
v___x_1045_ = lean_uint8_to_uint32(v_b_u2081_1040_);
v___x_1046_ = 6;
v___x_1047_ = lean_uint32_shift_left(v___x_1045_, v___x_1046_);
v___x_1048_ = lean_uint32_lor(v___x_1044_, v___x_1047_);
v___x_1049_ = lean_uint8_to_uint32(v_b_u2082_1041_);
v_r_1050_ = lean_uint32_lor(v___x_1048_, v___x_1049_);
v___x_1051_ = 2048;
v___x_1052_ = lean_uint32_dec_lt(v_r_1050_, v___x_1051_);
v___x_1053_ = 55296;
v___x_1054_ = lean_uint32_dec_le(v___x_1053_, v_r_1050_);
if (v___x_1054_ == 0)
{
return v_r_1050_;
}
else
{
uint32_t v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = 57343;
v___x_1056_ = lean_uint32_dec_le(v_r_1050_, v___x_1055_);
return v_r_1050_;
}
}
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; uint8_t v___x_1060_; uint8_t v___x_1061_; uint8_t v___x_1062_; uint8_t v___x_1063_; uint8_t v_b_u2080_1064_; uint8_t v___x_1065_; uint8_t v_b_u2081_1066_; uint32_t v___x_1067_; uint32_t v___x_1068_; uint32_t v___x_1069_; uint32_t v___x_1070_; uint32_t v_r_1071_; uint32_t v___x_1072_; uint8_t v___x_1073_; 
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_nat_add(v_i_968_, v___x_1057_);
v___x_1059_ = lean_nat_dec_lt(v___x_1058_, v___x_970_);
v___x_1060_ = lean_byte_array_fget(v_bytes_967_, v___x_1058_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_uint8_land(v___x_1060_, v___x_979_);
v___x_1062_ = lean_uint8_dec_eq(v___x_1061_, v___x_973_);
v___x_1063_ = 31;
v_b_u2080_1064_ = lean_uint8_land(v___x_972_, v___x_1063_);
v___x_1065_ = 63;
v_b_u2081_1066_ = lean_uint8_land(v___x_1060_, v___x_1065_);
v___x_1067_ = lean_uint8_to_uint32(v_b_u2080_1064_);
v___x_1068_ = 6;
v___x_1069_ = lean_uint32_shift_left(v___x_1067_, v___x_1068_);
v___x_1070_ = lean_uint8_to_uint32(v_b_u2081_1066_);
v_r_1071_ = lean_uint32_lor(v___x_1069_, v___x_1070_);
v___x_1072_ = 128;
v___x_1073_ = lean_uint32_dec_lt(v_r_1071_, v___x_1072_);
return v_r_1071_;
}
}
else
{
uint32_t v___x_1074_; 
v___x_1074_ = lean_uint8_to_uint32(v___x_972_);
return v___x_1074_;
}
}
}
LEAN_EXPORT void l_ByteArray_utf8DecodeChar_0interp(lean_interpreter_value* stack)
{
lean_object* v_bytes_967_ = stack[0].m_obj;
lean_object* v_i_968_ = stack[1].m_obj;
uint32_t v_res_1075_;
v_res_1075_ = l_ByteArray_utf8DecodeChar(v_bytes_967_, v_i_968_, lean_box(0));
stack->m_num = v_res_1075_;
}
LEAN_EXPORT lean_object* l_ByteArray_utf8DecodeChar___boxed(lean_object* v_bytes_1076_, lean_object* v_i_1077_, lean_object* v_h_1078_){
_start:
{
uint32_t v_res_1079_; lean_object* v_r_1080_; 
v_res_1079_ = l_ByteArray_utf8DecodeChar(v_bytes_1076_, v_i_1077_, v_h_1078_);
lean_dec(v_i_1077_);
lean_dec_ref(v_bytes_1076_);
v_r_1080_ = lean_box_uint32(v_res_1079_);
return v_r_1080_;
}
}
uint8_t l_UInt8_instDecidableIsUTF8FirstByte(uint8_t v_c_1081_){
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
uint8_t v___x_1093_; uint8_t v___x_1094_; uint8_t v___x_1095_; 
v___x_1093_ = 248;
v___x_1094_ = lean_uint8_land(v_c_1081_, v___x_1093_);
v___x_1095_ = lean_uint8_dec_eq(v___x_1094_, v___x_1090_);
return v___x_1095_;
}
else
{
return v___x_1092_;
}
}
else
{
return v___x_1089_;
}
}
else
{
return v___x_1085_;
}
}
}
LEAN_EXPORT void l_UInt8_instDecidableIsUTF8FirstByte_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_1081_ = stack[0].m_num;
uint8_t v_res_1096_;
v_res_1096_ = l_UInt8_instDecidableIsUTF8FirstByte(v_c_1081_);
stack->m_num = v_res_1096_;
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableIsUTF8FirstByte___boxed(lean_object* v_c_1097_){
_start:
{
uint8_t v_c_boxed_1098_; uint8_t v_res_1099_; lean_object* v_r_1100_; 
v_c_boxed_1098_ = lean_unbox(v_c_1097_);
v_res_1099_ = l_UInt8_instDecidableIsUTF8FirstByte(v_c_boxed_1098_);
v_r_1100_ = lean_box(v_res_1099_);
return v_r_1100_;
}
}
lean_object* l_UInt8_utf8ByteSize___redArg(uint8_t v_c_1101_){
_start:
{
uint8_t v___x_1102_; uint8_t v___x_1103_; uint8_t v___x_1104_; uint8_t v___x_1105_; 
v___x_1102_ = 128;
v___x_1103_ = lean_uint8_land(v_c_1101_, v___x_1102_);
v___x_1104_ = 0;
v___x_1105_ = lean_uint8_dec_eq(v___x_1103_, v___x_1104_);
if (v___x_1105_ == 0)
{
uint8_t v___x_1106_; uint8_t v___x_1107_; uint8_t v___x_1108_; uint8_t v___x_1109_; 
v___x_1106_ = 224;
v___x_1107_ = lean_uint8_land(v_c_1101_, v___x_1106_);
v___x_1108_ = 192;
v___x_1109_ = lean_uint8_dec_eq(v___x_1107_, v___x_1108_);
if (v___x_1109_ == 0)
{
uint8_t v___x_1110_; uint8_t v___x_1111_; uint8_t v___x_1112_; 
v___x_1110_ = 240;
v___x_1111_ = lean_uint8_land(v_c_1101_, v___x_1110_);
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
LEAN_EXPORT void l_UInt8_utf8ByteSize___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_1101_ = stack[0].m_num;
lean_object* v_res_1117_;
v_res_1117_ = l_UInt8_utf8ByteSize___redArg(v_c_1101_);
stack->m_obj
 = v_res_1117_;
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___redArg___boxed(lean_object* v_c_1118_){
_start:
{
uint8_t v_c_boxed_1119_; lean_object* v_res_1120_; 
v_c_boxed_1119_ = lean_unbox(v_c_1118_);
v_res_1120_ = l_UInt8_utf8ByteSize___redArg(v_c_boxed_1119_);
return v_res_1120_;
}
}
lean_object* l_UInt8_utf8ByteSize(uint8_t v_c_1121_, lean_object* v___h_1122_){
_start:
{
uint8_t v___x_1123_; uint8_t v___x_1124_; uint8_t v___x_1125_; uint8_t v___x_1126_; 
v___x_1123_ = 128;
v___x_1124_ = lean_uint8_land(v_c_1121_, v___x_1123_);
v___x_1125_ = 0;
v___x_1126_ = lean_uint8_dec_eq(v___x_1124_, v___x_1125_);
if (v___x_1126_ == 0)
{
uint8_t v___x_1127_; uint8_t v___x_1128_; uint8_t v___x_1129_; uint8_t v___x_1130_; 
v___x_1127_ = 224;
v___x_1128_ = lean_uint8_land(v_c_1121_, v___x_1127_);
v___x_1129_ = 192;
v___x_1130_ = lean_uint8_dec_eq(v___x_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
uint8_t v___x_1131_; uint8_t v___x_1132_; uint8_t v___x_1133_; 
v___x_1131_ = 240;
v___x_1132_ = lean_uint8_land(v_c_1121_, v___x_1131_);
v___x_1133_ = lean_uint8_dec_eq(v___x_1132_, v___x_1127_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_unsigned_to_nat(4u);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_unsigned_to_nat(3u);
return v___x_1135_;
}
}
else
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_unsigned_to_nat(2u);
return v___x_1136_;
}
}
else
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_unsigned_to_nat(1u);
return v___x_1137_;
}
}
}
LEAN_EXPORT void l_UInt8_utf8ByteSize_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_1121_ = stack[0].m_num;
lean_object* v_res_1138_;
v_res_1138_ = l_UInt8_utf8ByteSize(v_c_1121_, lean_box(0));
stack->m_obj
 = v_res_1138_;
}
LEAN_EXPORT lean_object* l_UInt8_utf8ByteSize___boxed(lean_object* v_c_1139_, lean_object* v___h_1140_){
_start:
{
uint8_t v_c_boxed_1141_; lean_object* v_res_1142_; 
v_c_boxed_1141_ = lean_unbox(v_c_1139_);
v_res_1142_ = l_UInt8_utf8ByteSize(v_c_boxed_1141_, v___h_1140_);
return v_res_1142_;
}
}
lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(uint8_t v_x_1143_){
_start:
{
switch(v_x_1143_)
{
case 0:
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
return v___x_1144_;
}
case 1:
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_unsigned_to_nat(1u);
return v___x_1145_;
}
case 2:
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_unsigned_to_nat(2u);
return v___x_1146_;
}
case 3:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_unsigned_to_nat(3u);
return v___x_1147_;
}
default: 
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_unsigned_to_nat(4u);
return v___x_1148_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1143_ = stack[0].m_num;
lean_object* v_res_1149_;
v_res_1149_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(v_x_1143_);
stack->m_obj
 = v_res_1149_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize___boxed(lean_object* v_x_1150_){
_start:
{
uint8_t v_x_54__boxed_1151_; lean_object* v_res_1152_; 
v_x_54__boxed_1151_ = lean_unbox(v_x_1150_);
v_res_1152_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(v_x_54__boxed_1151_);
return v_res_1152_;
}
}
lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(uint8_t v_x_1153_, lean_object* v_h__1_1154_, lean_object* v_h__2_1155_, lean_object* v_h__3_1156_, lean_object* v_h__4_1157_, lean_object* v_h__5_1158_){
_start:
{
switch(v_x_1153_)
{
case 0:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec(v_h__5_1158_);
lean_dec(v_h__4_1157_);
lean_dec(v_h__3_1156_);
lean_dec(v_h__2_1155_);
v___x_1159_ = lean_box(0);
v___x_1160_ = lean_apply_1(v_h__1_1154_, v___x_1159_);
return v___x_1160_;
}
case 1:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec(v_h__5_1158_);
lean_dec(v_h__4_1157_);
lean_dec(v_h__3_1156_);
lean_dec(v_h__1_1154_);
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_apply_1(v_h__2_1155_, v___x_1161_);
return v___x_1162_;
}
case 2:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec(v_h__5_1158_);
lean_dec(v_h__4_1157_);
lean_dec(v_h__2_1155_);
lean_dec(v_h__1_1154_);
v___x_1163_ = lean_box(0);
v___x_1164_ = lean_apply_1(v_h__3_1156_, v___x_1163_);
return v___x_1164_;
}
case 3:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec(v_h__5_1158_);
lean_dec(v_h__3_1156_);
lean_dec(v_h__2_1155_);
lean_dec(v_h__1_1154_);
v___x_1165_ = lean_box(0);
v___x_1166_ = lean_apply_1(v_h__4_1157_, v___x_1165_);
return v___x_1166_;
}
default: 
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec(v_h__4_1157_);
lean_dec(v_h__3_1156_);
lean_dec(v_h__2_1155_);
lean_dec(v_h__1_1154_);
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_apply_1(v_h__5_1158_, v___x_1167_);
return v___x_1168_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1153_ = stack[0].m_num;
lean_object* v_h__1_1154_ = stack[1].m_obj;
lean_object* v_h__2_1155_ = stack[2].m_obj;
lean_object* v_h__3_1156_ = stack[3].m_obj;
lean_object* v_h__4_1157_ = stack[4].m_obj;
lean_object* v_h__5_1158_ = stack[5].m_obj;
lean_object* v_res_1169_;
v_res_1169_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(v_x_1153_, v_h__1_1154_, v_h__2_1155_, v_h__3_1156_, v_h__4_1157_, v_h__5_1158_);
stack->m_obj
 = v_res_1169_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg___boxed(lean_object* v_x_1170_, lean_object* v_h__1_1171_, lean_object* v_h__2_1172_, lean_object* v_h__3_1173_, lean_object* v_h__4_1174_, lean_object* v_h__5_1175_){
_start:
{
uint8_t v_x_51__boxed_1176_; lean_object* v_res_1177_; 
v_x_51__boxed_1176_ = lean_unbox(v_x_1170_);
v_res_1177_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(v_x_51__boxed_1176_, v_h__1_1171_, v_h__2_1172_, v_h__3_1173_, v_h__4_1174_, v_h__5_1175_);
return v_res_1177_;
}
}
lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(lean_object* v_motive_1178_, uint8_t v_x_1179_, lean_object* v_h__1_1180_, lean_object* v_h__2_1181_, lean_object* v_h__3_1182_, lean_object* v_h__4_1183_, lean_object* v_h__5_1184_){
_start:
{
switch(v_x_1179_)
{
case 0:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec(v_h__5_1184_);
lean_dec(v_h__4_1183_);
lean_dec(v_h__3_1182_);
lean_dec(v_h__2_1181_);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_apply_1(v_h__1_1180_, v___x_1185_);
return v___x_1186_;
}
case 1:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec(v_h__5_1184_);
lean_dec(v_h__4_1183_);
lean_dec(v_h__3_1182_);
lean_dec(v_h__1_1180_);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_apply_1(v_h__2_1181_, v___x_1187_);
return v___x_1188_;
}
case 2:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec(v_h__5_1184_);
lean_dec(v_h__4_1183_);
lean_dec(v_h__2_1181_);
lean_dec(v_h__1_1180_);
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_apply_1(v_h__3_1182_, v___x_1189_);
return v___x_1190_;
}
case 3:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_dec(v_h__5_1184_);
lean_dec(v_h__3_1182_);
lean_dec(v_h__2_1181_);
lean_dec(v_h__1_1180_);
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_apply_1(v_h__4_1183_, v___x_1191_);
return v___x_1192_;
}
default: 
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec(v_h__4_1183_);
lean_dec(v_h__3_1182_);
lean_dec(v_h__2_1181_);
lean_dec(v_h__1_1180_);
v___x_1193_ = lean_box(0);
v___x_1194_ = lean_apply_1(v_h__5_1184_, v___x_1193_);
return v___x_1194_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1179_ = stack[1].m_num;
lean_object* v_h__1_1180_ = stack[2].m_obj;
lean_object* v_h__2_1181_ = stack[3].m_obj;
lean_object* v_h__3_1182_ = stack[4].m_obj;
lean_object* v_h__4_1183_ = stack[5].m_obj;
lean_object* v_h__5_1184_ = stack[6].m_obj;
lean_object* v_res_1195_;
v_res_1195_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(lean_box(0), v_x_1179_, v_h__1_1180_, v_h__2_1181_, v_h__3_1182_, v_h__4_1183_, v_h__5_1184_);
stack->m_obj
 = v_res_1195_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___boxed(lean_object* v_motive_1196_, lean_object* v_x_1197_, lean_object* v_h__1_1198_, lean_object* v_h__2_1199_, lean_object* v_h__3_1200_, lean_object* v_h__4_1201_, lean_object* v_h__5_1202_){
_start:
{
uint8_t v_x_86__boxed_1203_; lean_object* v_res_1204_; 
v_x_86__boxed_1203_ = lean_unbox(v_x_1197_);
v_res_1204_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(v_motive_1196_, v_x_86__boxed_1203_, v_h__1_1198_, v_h__2_1199_, v_h__3_1200_, v_h__4_1201_, v_h__5_1202_);
return v_res_1204_;
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
